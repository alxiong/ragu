use ragu_arithmetic::Cycle;
use ragu_circuits::polynomials::ProductionRank;
use ragu_core::Result;
use ragu_pasta::{Fp, Pasta};
use ragu_pcd::ApplicationBuilder;
use ragu_testing::pcd::nontrivial::{Hash2, WitnessLeaf};
use rand::SeedableRng;
use rand::rngs::StdRng;

#[test]
fn various_merging_operations() -> Result<()> {
    let pasta = Pasta::baked();
    let poseidon_params = Pasta::circuit_poseidon(pasta);
    let witness_leaf = WitnessLeaf { poseidon_params };
    let hash2 = Hash2 { poseidon_params };
    let app = ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(WitnessLeaf { poseidon_params })?
        .register(Hash2 { poseidon_params })?
        .finalize(pasta)?;

    let mut rng = StdRng::seed_from_u64(1234);

    let (leaf1, _) = app.seed(&mut rng, &witness_leaf, Fp::from(42u64))?;
    assert!(app.verify(&leaf1, &mut rng)?);

    let (leaf2, _) = app.seed(&mut rng, &witness_leaf, Fp::from(42u64))?;
    assert!(app.verify(&leaf2, &mut rng)?);

    let (node1, _) = app.fuse(&mut rng, &hash2, (), leaf1, leaf2)?;
    assert!(app.verify(&node1, &mut rng)?);

    Ok(())
}
