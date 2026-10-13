use super::{BoolsBuffer, CircuitTranscript};
use crate::config::{CSConfig, DevCSConfig};
use crate::cs::cs_builder::new_builder;
use crate::cs::cs_builder_reference::CsReferenceImplementationBuilder;
use crate::cs::gates::{
    BooleanConstraintGate, ConstantsAllocatorGate, FmaGateInBaseFieldWithoutConstant, NopGate,
    ReductionGate,
};
use crate::cs::implementations::reference_cs::CSReferenceAssembly;
use crate::cs::traits::cs::{CSWitnessSource, ConstraintSystem, DstBuffer};
use crate::cs::traits::gate::GatePlacementStrategy;
use crate::cs::{CSGeometry, Place};
use crate::dag::resolvers::StCircuitResolverParams;
use crate::dag::{CircuitResolver, StCircuitResolver, WitnessSource, WitnessSourceAwaitable};
use crate::field::goldilocks::GoldilocksField as F;
use crate::field::U64Representable;
use crate::gadgets::num::Num;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::witnessable::WitnessHookable;
use crate::worker::Worker;
use std::alloc::Global;
use std::panic::{catch_unwind, AssertUnwindSafe};

type Config = <DevCSConfig as CSConfig>::ResolverConfig;
type Assembly = CSReferenceAssembly<F, F, DevCSConfig, Global>;

struct ResolverArgs {
    representation: u64,
    auxiliary_override: Option<F>,
}

// Supply adversarial witnesses through the resolver while retaining the exact
// production constraint generation and query-bit extraction.
struct AdversarialResolver {
    inner: StCircuitResolver<F, Config>,
    representation: u64,
    auxiliary_override: Option<F>,
    challenge: Option<Place>,
}

impl WitnessSource<F> for AdversarialResolver {
    const PRODUCES_VALUES: bool = true;
    fn try_get_value(&self, place: Place) -> Option<F> {
        self.inner.try_get_value(place)
    }
    fn get_value_unchecked(&self, place: Place) -> F {
        self.inner.get_value_unchecked(place)
    }
}

impl WitnessSourceAwaitable<F> for AdversarialResolver {
    type Awaiter<'a> = <StCircuitResolver<F, Config> as WitnessSourceAwaitable<F>>::Awaiter<'a>;
    fn get_awaiter<const N: usize>(&mut self, places: [Place; N]) -> Self::Awaiter<'_> {
        self.inner.get_awaiter(places)
    }
}

impl CSWitnessSource<F> for AdversarialResolver {}

impl CircuitResolver<F, Config> for AdversarialResolver {
    type Arg = ResolverArgs;
    fn new(args: ResolverArgs) -> Self {
        Self {
            inner: StCircuitResolver::new(StCircuitResolverParams::new(1 << 16)),
            representation: args.representation,
            auxiliary_override: args.auxiliary_override,
            challenge: None,
        }
    }
    fn set_value(&mut self, place: Place, value: F) {
        self.inner.set_value(place, value);
    }
    fn add_resolution<FN>(&mut self, inputs: &[Place], outputs: &[Place], f: FN)
    where
        FN: FnOnce(&[F], &mut DstBuffer<'_, '_, F>) + Send + Sync,
    {
        if inputs.len() == 1 && outputs.len() == 64 {
            self.challenge = Some(inputs[0]);
            let representation = self.representation;
            self.inner.add_resolution(inputs, outputs, move |_, dst| {
                for bit in 0..64 {
                    dst.push(F::from_u64_unchecked((representation >> bit) & 1));
                }
            });
        } else if inputs.len() == 2 && outputs.len() == 1 && Some(inputs[1]) == self.challenge {
            if let Some(value) = self.auxiliary_override {
                self.inner
                    .add_resolution(inputs, outputs, move |_, dst| dst.push(value));
            } else {
                self.inner.add_resolution(inputs, outputs, f);
            }
        } else {
            self.inner.add_resolution(inputs, outputs, f);
        }
    }
    fn wait_till_resolved(&mut self) {
        self.inner.wait_till_resolved();
    }
    fn clear(&mut self) {
        self.inner.clear();
    }
}

#[derive(Clone, Debug)]
struct FixedTranscript(F);

impl CircuitTranscript<F> for FixedTranscript {
    type CircuitCompatibleCap = ();
    type TransciptParameters = F;
    fn new<CS: ConstraintSystem<F>>(_cs: &mut CS, value: F) -> Self {
        Self(value)
    }
    fn witness_field_elements<CS: ConstraintSystem<F>>(&mut self, _cs: &mut CS, _els: &[Num<F>]) {}
    fn witness_merkle_tree_cap<CS: ConstraintSystem<F>>(&mut self, _cs: &mut CS, _cap: &[()]) {}
    fn get_challenge<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Num<F> {
        Num::allocated_constant(cs, self.0)
    }
}

fn query_witness(
    challenge: u64,
    representation: u64,
    auxiliary_override: Option<F>,
) -> (u64, Assembly) {
    let geometry = CSGeometry {
        num_columns_under_copy_permutation: 136,
        num_witness_columns: 5,
        num_constant_columns: 4,
        max_allowed_constraint_degree: 8,
    };
    let builder = new_builder::<_, F>(CsReferenceImplementationBuilder::<
        F,
        F,
        DevCSConfig,
        AdversarialResolver,
    >::new(geometry, 1024));
    let builder = ConstantsAllocatorGate::configure_builder(
        builder,
        GatePlacementStrategy::UseGeneralPurposeColumns,
    );
    let builder = BooleanConstraintGate::configure_builder(
        builder,
        GatePlacementStrategy::UseSpecializedColumns {
            num_repetitions: 1,
            share_constants: false,
        },
    );
    let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
        builder,
        GatePlacementStrategy::UseGeneralPurposeColumns,
    );
    let builder = ReductionGate::<F, 4>::configure_builder(
        builder,
        GatePlacementStrategy::UseGeneralPurposeColumns,
    );
    let builder =
        NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);
    let mut cs = builder.build(ResolverArgs {
        representation,
        auxiliary_override,
    });
    let mut transcript = FixedTranscript(F::from_u64_unchecked(challenge));
    let mut buffer = BoolsBuffer {
        available: vec![],
        max_needed: 21,
    };
    let bits = buffer.get_bits(&mut cs, &mut transcript, 21);
    let index = bits.iter().enumerate().fold(0, |result, (i, bit)| {
        result | ((bit.witness_hook(&cs)().unwrap() as u64) << i)
    });
    cs.pad_and_shrink();
    (index, cs.into_assembly::<Global>())
}

fn assert_rejected(mut assembly: Assembly) {
    let failure = catch_unwind(AssertUnwindSafe(|| {
        assembly.check_if_satisfied(&Worker::new_with_num_threads(1))
    }))
    .expect_err("adversarial query witness satisfied the circuit");
    let message = failure
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| failure.downcast_ref::<&str>().map(|s| (*s).to_owned()))
        .expect("non-string failure");
    assert!(message.contains("Unsatisfied at row"), "{message}");
}

#[test]
fn canonical_query_bits_reject_noncanonical_encodings() {
    for challenge in [0, 1, 255, 65535, (1 << 21) - 1, 1 << 21, (1 << 32) - 2] {
        for auxiliary in [
            F::from_u64_unchecked(0),
            F::from_u64_unchecked(1),
            F::from_u64_unchecked(F::ORDER - 1),
        ] {
            let (index, assembly) = query_witness(challenge, challenge + F::ORDER, Some(auxiliary));
            assert_ne!(index, challenge & ((1 << 21) - 1));
            assert_rejected(assembly);
        }
    }
}

#[test]
fn canonical_query_bits_accept_boundaries_and_match_native_indices() {
    for challenge in [
        0,
        1,
        (1 << 32) - 2,
        (1 << 32) - 1,
        1 << 32,
        0xfffffffeffffffff,
        F::ORDER - 1,
    ] {
        let (index, mut assembly) = query_witness(challenge, challenge, None);
        assert_eq!(index, challenge & ((1 << 21) - 1));
        assert!(assembly.check_if_satisfied(&Worker::new_with_num_threads(1)));
    }
}

#[test]
fn canonical_query_bits_constrain_the_auxiliary_witness() {
    let (_, assembly) = query_witness(1, 1, Some(F::from_u64_unchecked(0)));
    assert_rejected(assembly);
    // At p - 1, H and x + 1 are both zero, so this unused auxiliary may be arbitrary.
    let (_, mut assembly) =
        query_witness(F::ORDER - 1, F::ORDER - 1, Some(F::from_u64_unchecked(123)));
    assert!(assembly.check_if_satisfied(&Worker::new_with_num_threads(1)));
}
