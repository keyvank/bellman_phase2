use bellman::{Circuit, ConstraintSystem, SynthesisError};
use std::ops::MulAssign;

struct CubeRoot {
    cube_root: Option<bls12_381::Scalar>,
}

impl Circuit<bls12_381::Scalar> for CubeRoot {
    fn synthesize<CS: ConstraintSystem<bls12_381::Scalar>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        // Witness the cube root
        let root = cs.alloc(
            || "root",
            || self.cube_root.ok_or(SynthesisError::AssignmentMissing),
        )?;

        // Witness the square of the cube root
        let square = cs.alloc(
            || "square",
            || {
                self.cube_root
                    .ok_or(SynthesisError::AssignmentMissing)
                    .map(|root| root.square())
            },
        )?;

        // Enforce that `square` is root^2
        cs.enforce(
            || "squaring",
            |lc| lc + root,
            |lc| lc + root,
            |lc| lc + square,
        );

        // Witness the cube, as a public input
        let cube = cs.alloc_input(
            || "cube",
            || {
                self.cube_root
                    .ok_or(SynthesisError::AssignmentMissing)
                    .map(|root| {
                        let mut tmp = root;
                        tmp.square();
                        tmp.mul_assign(&root);
                        tmp
                    })
            },
        )?;

        // Enforce that `cube` is root^3
        // i.e. that `cube` is `root` * `square`
        cs.enforce(
            || "cubing",
            |lc| lc + root,
            |lc| lc + square,
            |lc| lc + cube,
        );

        Ok(())
    }
}

fn main() {
    println!("Hello, world!");
    let mut params = bellman_phase2::MPCParameters::new(CubeRoot { cube_root: None }).unwrap();
    let hash = params.contribute(&mut rand::thread_rng());
    let contributions = params
        .verify(CubeRoot { cube_root: None })
        .expect("parameters should be valid!");
    assert!(bellman_phase2::contains_contribution(&contributions, &hash));

    let params = params.get_params();
    let pvk = bellman::groth16::prepare_verifying_key(&params.vk);
    let rng = &mut rand::thread_rng();

    let root = bls12_381::Scalar::from(123);
    let mut cube = root;
    cube.square();
    cube.mul_assign(&root);

    let proof = bellman::groth16::create_random_proof(
        CubeRoot {
            cube_root: Some(root),
        },
        params,
        rng,
    )
    .unwrap();

    assert!(bellman::groth16::verify_proof(&pvk, &proof, &[cube]).is_ok());
}
