use ragu_arithmetic::Cycle;
use ragu_circuits::polynomials::ProductionRank;
use ragu_pasta::{Fp, Pasta};
use ragu_pcd::{Application, ApplicationBuilder, Pcd};
use ragu_testing::pcd::nontrivial;
use rand::SeedableRng;
use rand::rngs::StdRng;

pub fn setup_register() -> (
    nontrivial::WitnessLeaf<'static, Pasta>,
    nontrivial::Hash2<'static, Pasta>,
) {
    let pasta = Pasta::baked();
    let poseidon_params = Pasta::circuit_poseidon(pasta);
    (
        nontrivial::WitnessLeaf { poseidon_params },
        nontrivial::Hash2 { poseidon_params },
    )
}

pub fn setup_finalize() -> (
    ApplicationBuilder<'static, Pasta, ProductionRank, 4>,
    &'static <Pasta as Cycle>::Params,
) {
    let pasta = Pasta::baked();
    let poseidon_params = Pasta::circuit_poseidon(pasta);
    let app = ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(nontrivial::WitnessLeaf { poseidon_params })
        .unwrap()
        .register(nontrivial::Hash2 { poseidon_params })
        .unwrap();
    (app, pasta)
}

pub fn setup_seed() -> (
    Application<'static, Pasta, ProductionRank, 4>,
    nontrivial::WitnessLeaf<'static, Pasta>,
    nontrivial::Hash2<'static, Pasta>,
    StdRng,
) {
    let pasta = Pasta::baked();
    let poseidon_params = Pasta::circuit_poseidon(pasta);
    let app = ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(nontrivial::WitnessLeaf { poseidon_params })
        .unwrap()
        .register(nontrivial::Hash2 { poseidon_params })
        .unwrap()
        .finalize(pasta)
        .unwrap();
    let witness_leaf = nontrivial::WitnessLeaf { poseidon_params };
    let hash2 = nontrivial::Hash2 { poseidon_params };
    (app, witness_leaf, hash2, StdRng::seed_from_u64(1234))
}

pub fn setup_fuse() -> (
    Application<'static, Pasta, ProductionRank, 4>,
    Pcd<Pasta, ProductionRank, nontrivial::LeafNode>,
    Pcd<Pasta, ProductionRank, nontrivial::LeafNode>,
    nontrivial::Hash2<'static, Pasta>,
    StdRng,
) {
    let (app, witness_leaf, hash2, mut rng) = setup_seed();

    let (leaf1, _) = app.seed(&mut rng, &witness_leaf, Fp::from(1u64)).unwrap();
    let (leaf2, _) = app.seed(&mut rng, &witness_leaf, Fp::from(2u64)).unwrap();

    (app, leaf1, leaf2, hash2, rng)
}

pub fn setup_verify_leaf() -> (
    Application<'static, Pasta, ProductionRank, 4>,
    Pcd<Pasta, ProductionRank, nontrivial::LeafNode>,
    StdRng,
) {
    let (app, witness_leaf, _hash2, mut rng) = setup_seed();
    let (leaf, _) = app.seed(&mut rng, &witness_leaf, Fp::from(1u64)).unwrap();
    (app, leaf, rng)
}

pub fn setup_verify_node() -> (
    Application<'static, Pasta, ProductionRank, 4>,
    Pcd<Pasta, ProductionRank, nontrivial::InternalNode>,
    StdRng,
) {
    let (app, witness_leaf, hash2, mut rng) = setup_seed();

    let (leaf1, _) = app.seed(&mut rng, &witness_leaf, Fp::from(1u64)).unwrap();
    let (leaf2, _) = app.seed(&mut rng, &witness_leaf, Fp::from(2u64)).unwrap();
    let (node, _) = app.fuse(&mut rng, &hash2, (), leaf1, leaf2).unwrap();

    (app, node, rng)
}
