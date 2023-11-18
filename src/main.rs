use bellman::groth16::Parameters;
use bellman::Index;
use bellman::SynthesisError;
use bellman::Variable;
use bellman::{ConstraintSystem, LinearCombination};
use blake2_rfc::blake2b::Blake2b;
use bls12_381::Bls12;
use ff::Field;
use ff::PrimeField;
use group::Wnaf;
use pairing::group::Curve;
use pairing::group::Group;
use pairing::group::UncompressedEncoding;
use rand::SeedableRng;
use rand_chacha::ChaChaRng;
use std::io;
use std::io::{Read, Write};
use std::ops::AddAssign;

struct KeypairAssembly<Fr: PrimeField> {
    num_inputs: usize,
    num_aux: usize,
    num_constraints: usize,
    at_inputs: Vec<Vec<(Fr, usize)>>,
    bt_inputs: Vec<Vec<(Fr, usize)>>,
    ct_inputs: Vec<Vec<(Fr, usize)>>,
    at_aux: Vec<Vec<(Fr, usize)>>,
    bt_aux: Vec<Vec<(Fr, usize)>>,
    ct_aux: Vec<Vec<(Fr, usize)>>,
}

impl<Fr: PrimeField> ConstraintSystem<Fr> for KeypairAssembly<Fr> {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, _: A, _: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // There is no assignment, so we don't even invoke the
        // function for obtaining one.

        let index = self.num_aux;
        self.num_aux += 1;

        self.at_aux.push(vec![]);
        self.bt_aux.push(vec![]);
        self.ct_aux.push(vec![]);

        Ok(Variable::new_unchecked(Index::Aux(index)))
    }
    fn alloc_input<F, A, AR>(&mut self, _: A, _: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // There is no assignment, so we don't even invoke the
        // function for obtaining one.

        let index = self.num_inputs;
        self.num_inputs += 1;

        self.at_inputs.push(vec![]);
        self.bt_inputs.push(vec![]);
        self.ct_inputs.push(vec![]);

        Ok(Variable::new_unchecked(Index::Input(index)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<Fr>) -> LinearCombination<Fr>,
        LB: FnOnce(LinearCombination<Fr>) -> LinearCombination<Fr>,
        LC: FnOnce(LinearCombination<Fr>) -> LinearCombination<Fr>,
    {
        fn eval<Fr: PrimeField>(
            l: LinearCombination<Fr>,
            inputs: &mut [Vec<(Fr, usize)>],
            aux: &mut [Vec<(Fr, usize)>],
            this_constraint: usize,
        ) {
            for &(var, coeff) in l.as_ref() {
                match var.get_unchecked() {
                    Index::Input(id) => inputs[id].push((coeff, this_constraint)),
                    Index::Aux(id) => aux[id].push((coeff, this_constraint)),
                }
            }
        }

        eval(
            a(LinearCombination::zero()),
            &mut self.at_inputs,
            &mut self.at_aux,
            self.num_constraints,
        );
        eval(
            b(LinearCombination::zero()),
            &mut self.bt_inputs,
            &mut self.bt_aux,
            self.num_constraints,
        );
        eval(
            c(LinearCombination::zero()),
            &mut self.ct_inputs,
            &mut self.ct_aux,
            self.num_constraints,
        );

        self.num_constraints += 1;
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self) {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

/// This allows others to verify that you contributed. The hash produced
/// by `MPCParameters::contribute` is just a BLAKE2b hash of this object.
#[derive(Clone)]
struct PublicKey {
    /// This is the delta (in G1) after the transformation, kept so that we
    /// can check correctness of the public keys without having the entire
    /// interstitial parameters for each contribution.
    delta_after: bls12_381::G1Affine,

    /// Random element chosen by the contributor.
    s: bls12_381::G1Affine,

    /// That element, taken to the contributor's secret delta.
    s_delta: bls12_381::G1Affine,

    /// r is H(last_pubkey | s | s_delta), r_delta proves knowledge of delta
    r_delta: bls12_381::G2Affine,

    /// Hash of the transcript (used for mapping to r)
    transcript: [u8; 64],
}

impl PartialEq for PublicKey {
    fn eq(&self, other: &PublicKey) -> bool {
        self.delta_after == other.delta_after
            && self.s == other.s
            && self.s_delta == other.s_delta
            && self.r_delta == other.r_delta
            && &self.transcript[..] == &other.transcript[..]
    }
}

#[derive(Clone)]
pub struct MPCParameters {
    params: Parameters<Bls12>,
    cs_hash: [u8; 64],
    contributions: Vec<PublicKey>,
}

impl PartialEq for MPCParameters {
    fn eq(&self, other: &MPCParameters) -> bool {
        self.params == other.params
            && &self.cs_hash[..] == &other.cs_hash[..]
            && self.contributions == other.contributions
    }
}

impl PublicKey {
    fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(self.delta_after.to_uncompressed().as_ref())?;
        writer.write_all(self.s.to_uncompressed().as_ref())?;
        writer.write_all(self.s_delta.to_uncompressed().as_ref())?;
        writer.write_all(self.r_delta.to_uncompressed().as_ref())?;
        writer.write_all(&self.transcript)?;

        Ok(())
    }

    fn read<R: Read>(mut reader: R) -> io::Result<PublicKey> {
        let mut g1_repr = <bls12_381::G1Affine as UncompressedEncoding>::Uncompressed::default();
        let mut g2_repr = <bls12_381::G2Affine as UncompressedEncoding>::Uncompressed::default();

        reader.read_exact(g1_repr.as_mut())?;
        let delta_after =
            <bls12_381::G1Affine as UncompressedEncoding>::from_uncompressed(&g1_repr).unwrap();
        //.map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        if delta_after.is_identity().into() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "point at infinity",
            ));
        }

        reader.read_exact(g1_repr.as_mut())?;
        let s = <bls12_381::G1Affine as UncompressedEncoding>::from_uncompressed(&g1_repr)
            //.map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
            .unwrap();

        if s.is_identity().into() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "point at infinity",
            ));
        }

        reader.read_exact(g1_repr.as_mut())?;
        let s_delta = <bls12_381::G1Affine as UncompressedEncoding>::from_uncompressed(&g1_repr)
            //.map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
            .unwrap();

        if s_delta.is_identity().into() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "point at infinity",
            ));
        }

        reader.read_exact(g2_repr.as_mut())?;
        let r_delta = <bls12_381::G2Affine as UncompressedEncoding>::from_uncompressed(&g2_repr)
            //.map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
            .unwrap();

        if r_delta.is_identity().into() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "point at infinity",
            ));
        }

        let mut transcript = [0u8; 64];
        reader.read_exact(&mut transcript)?;

        Ok(PublicKey {
            delta_after,
            s,
            s_delta,
            r_delta,
            transcript,
        })
    }
}

/// Abstraction over a writer which hashes the data being written.
struct HashWriter<W: Write> {
    writer: W,
    hasher: Blake2b,
}

impl Clone for HashWriter<io::Sink> {
    fn clone(&self) -> HashWriter<io::Sink> {
        HashWriter {
            writer: io::sink(),
            hasher: self.hasher.clone(),
        }
    }
}

impl<W: Write> HashWriter<W> {
    /// Construct a new `HashWriter` given an existing `writer` by value.
    pub fn new(writer: W) -> Self {
        HashWriter {
            writer: writer,
            hasher: Blake2b::new(64),
        }
    }

    /// Destroy this writer and return the hash of what was written.
    pub fn into_hash(self) -> [u8; 64] {
        let mut tmp = [0u8; 64];
        tmp.copy_from_slice(self.hasher.finalize().as_ref());
        tmp
    }
}

impl<W: Write> Write for HashWriter<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let bytes = self.writer.write(buf)?;

        if bytes > 0 {
            self.hasher.update(&buf[0..bytes]);
        }

        Ok(bytes)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }
}

fn hash_to_g2(digest: &[u8]) -> bls12_381::G2Projective {
    assert!(digest.len() == 32);

    bls12_381::G2Projective::random(&mut ChaChaRng::from_seed(digest.try_into().unwrap()))
}

/// Verify a contribution, given the old parameters and
/// the new parameters. Returns the hash of the contribution.
pub fn verify_contribution(before: &MPCParameters, after: &MPCParameters) -> Result<[u8; 64], ()> {
    // Transformation involves a single new object
    if after.contributions.len() != (before.contributions.len() + 1) {
        return Err(());
    }

    // None of the previous transformations should change
    if &before.contributions[..] != &after.contributions[0..before.contributions.len()] {
        return Err(());
    }

    // H/L will change, but should have same length
    if before.params.h.len() != after.params.h.len() {
        return Err(());
    }
    if before.params.l.len() != after.params.l.len() {
        return Err(());
    }

    // A/B_G1/B_G2 doesn't change at all
    if before.params.a != after.params.a {
        return Err(());
    }
    if before.params.b_g1 != after.params.b_g1 {
        return Err(());
    }
    if before.params.b_g2 != after.params.b_g2 {
        return Err(());
    }

    // alpha/beta/gamma don't change
    if before.params.vk.alpha_g1 != after.params.vk.alpha_g1 {
        return Err(());
    }
    if before.params.vk.beta_g1 != after.params.vk.beta_g1 {
        return Err(());
    }
    if before.params.vk.beta_g2 != after.params.vk.beta_g2 {
        return Err(());
    }
    if before.params.vk.gamma_g2 != after.params.vk.gamma_g2 {
        return Err(());
    }

    // IC shouldn't change, as gamma doesn't change
    if before.params.vk.ic != after.params.vk.ic {
        return Err(());
    }

    // cs_hash should be the same
    if &before.cs_hash[..] != &after.cs_hash[..] {
        return Err(());
    }

    let sink = io::sink();
    let mut sink = HashWriter::new(sink);
    sink.write_all(&before.cs_hash[..]).unwrap();

    for pubkey in &before.contributions {
        pubkey.write(&mut sink).unwrap();
    }

    let pubkey = after.contributions.last().unwrap();
    sink.write_all(pubkey.s.to_uncompressed().as_ref()).unwrap();
    sink.write_all(pubkey.s_delta.to_uncompressed().as_ref())
        .unwrap();

    let h = sink.into_hash();

    // The transcript must be consistent
    if &pubkey.transcript[..] != h.as_ref() {
        return Err(());
    }

    let r = hash_to_g2(h.as_ref()).to_affine();

    // Check the signature of knowledge
    if !same_ratio((r, pubkey.r_delta), (pubkey.s, pubkey.s_delta)) {
        return Err(());
    }

    // Check the change from the old delta is consistent
    if !same_ratio(
        (before.params.vk.delta_g1, pubkey.delta_after),
        (r, pubkey.r_delta),
    ) {
        return Err(());
    }

    // Current parameters should have consistent delta in G1
    if pubkey.delta_after != after.params.vk.delta_g1 {
        return Err(());
    }

    // Current parameters should have consistent delta in G2
    if !same_ratio(
        (bls12_381::G1Affine::generator(), pubkey.delta_after),
        (bls12_381::G2Affine::generator(), after.params.vk.delta_g2),
    ) {
        return Err(());
    }

    // H and L queries should be updated with delta^-1
    if !same_ratio(
        merge_pairs(&before.params.h, &after.params.h),
        (after.params.vk.delta_g2, before.params.vk.delta_g2), // reversed for inverse
    ) {
        return Err(());
    }

    if !same_ratio(
        merge_pairs(&before.params.l, &after.params.l),
        (after.params.vk.delta_g2, before.params.vk.delta_g2), // reversed for inverse
    ) {
        return Err(());
    }

    let sink = io::sink();
    let mut sink = HashWriter::new(sink);
    pubkey.write(&mut sink).unwrap();
    let h = sink.into_hash();
    let mut response = [0u8; 64];
    response.copy_from_slice(h.as_ref());

    Ok(response)
}

fn same_ratio<G1: pairing::PairingCurveAffine>(g1: (G1, G1), g2: (G1::Pair, G1::Pair)) -> bool {
    g1.0.pairing_with(&g2.1) == g1.1.pairing_with(&g2.0)
}

use group::WnafGroup;

fn merge_pairs<G: pairing::PairingCurveAffine>(v1: &[G], v2: &[G]) -> (G, G)
where
    G::Curve: WnafGroup,
{
    use rand::thread_rng;
    use std::sync::{Arc, Mutex};

    assert_eq!(v1.len(), v2.len());

    let chunk = (v1.len() / num_cpus::get()) + 1;

    let s = Arc::new(Mutex::new(G::Curve::identity()));
    let sx = Arc::new(Mutex::new(G::Curve::identity()));

    crossbeam::scope(|scope| {
        for (v1, v2) in v1.chunks(chunk).zip(v2.chunks(chunk)) {
            let s = s.clone();
            let sx = sx.clone();

            scope.spawn(move || {
                // We do not need to be overly cautious of the RNG
                // used for this check.
                let rng = &mut thread_rng();

                let mut wnaf = Wnaf::new();
                let mut local_s = G::Curve::identity();
                let mut local_sx = G::Curve::identity();

                for (v1, v2) in v1.iter().zip(v2.iter()) {
                    let rho = G::Scalar::random(&mut *rng);
                    let mut wnaf = wnaf.scalar(&rho);
                    let v1 = wnaf.base(v1.to_curve());
                    let v2 = wnaf.base(v2.to_curve());

                    local_s.add_assign(&v1);
                    local_sx.add_assign(&v2);
                }

                s.lock().unwrap().add_assign(&local_s);
                sx.lock().unwrap().add_assign(&local_sx);
            });
        }
    });

    let s = s.lock().unwrap().to_affine();
    let sx = sx.lock().unwrap().to_affine();

    (s, sx)
}

use rand::Rng;

/// This needs to be destroyed by at least one participant
/// for the final parameters to be secure.
struct PrivateKey {
    delta: bls12_381::Scalar,
}

use std::ops::Mul;

/// Compute a keypair, given the current parameters. Keypairs
/// cannot be reused for multiple contributions or contributions
/// in different parameters.
fn keypair<R: Rng>(rng: &mut R, current: &MPCParameters) -> (PublicKey, PrivateKey) {
    // Sample random delta
    let delta: bls12_381::Scalar = bls12_381::Scalar::random(&mut *rng);

    // Compute delta s-pair in G1
    let s = bls12_381::G1Projective::random(rng).to_affine();
    let s_delta = s.mul(delta).to_affine();

    // H(cs_hash | <previous pubkeys> | s | s_delta)
    let h = {
        let sink = io::sink();
        let mut sink = HashWriter::new(sink);

        sink.write_all(&current.cs_hash[..]).unwrap();
        for pubkey in &current.contributions {
            pubkey.write(&mut sink).unwrap();
        }
        sink.write_all(s.to_uncompressed().as_ref()).unwrap();
        sink.write_all(s_delta.to_uncompressed().as_ref()).unwrap();

        sink.into_hash()
    };

    // This avoids making a weird assumption about the hash into the
    // group.
    let mut transcript = [0; 64];
    transcript.copy_from_slice(h.as_ref());

    // Compute delta s-pair in G2
    let r = hash_to_g2(h.as_ref()).to_affine();
    let r_delta = r.mul(delta).to_affine();

    (
        PublicKey {
            delta_after: current.params.vk.delta_g1.mul(delta).to_affine(),
            s: s,
            s_delta: s_delta,
            r_delta: r_delta,
            transcript: transcript,
        },
        PrivateKey { delta: delta },
    )
}

fn main() {
    println!("Hello, world!");
}
