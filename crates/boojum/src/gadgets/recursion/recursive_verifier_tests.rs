use super::{materialize_powers_serial, precompute_opening_claim, quotening_operation};
use crate::config::DevCSConfig;
use crate::cs::cs_builder::new_builder;
use crate::cs::cs_builder_reference::CsReferenceImplementationBuilder;
use crate::cs::gates::{
    ConstantsAllocatorGate, FmaGateInBaseFieldWithoutConstant, FmaGateInExtensionWithoutConstant,
    NopGate,
};
use crate::cs::implementations::reference_cs::CSReferenceAssembly;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::gate::GatePlacementStrategy;
use crate::cs::CSGeometry;
use crate::dag::StCircuitResolver;
use crate::field::goldilocks::{GoldilocksExt2, GoldilocksField};
use crate::field::traits::field_like::PrimeFieldLike;
use crate::field::{ExtensionField, Field, PrimeField, U64Representable};
use crate::gadgets::num::prime_field_like::{NumAsFieldWrapper, NumExtAsFieldWrapper};
use crate::gadgets::num::Num;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::witnessable::WitnessHookable;
use crate::worker::Worker;
use std::alloc::Global;
use std::panic::{catch_unwind, AssertUnwindSafe};

type F = GoldilocksField;
type Ext = GoldilocksExt2;
type NativeExt = ExtensionField<F, 2, Ext>;
type Assembly = CSReferenceAssembly<F, F, DevCSConfig, Global>;

macro_rules! opening_test_cs {
    () => {{
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 136,
            num_witness_columns: 5,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 8,
        };
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig, StCircuitResolver<_, _>>::new(
                geometry,
                1 << 10,
            );
        let builder = new_builder::<_, F>(builder_impl);
        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInExtensionWithoutConstant::<F, Ext>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);
        builder.build(1 << 16)
    }};
}

fn native_ext(c0: u64, c1: u64) -> NativeExt {
    NativeExt::from_coeff_in_base([
        F::from_u64_with_reduction(c0),
        F::from_u64_with_reduction(c1),
    ])
}

fn allocate_ext<CS: ConstraintSystem<F> + 'static>(
    cs: &mut CS,
    value: NativeExt,
) -> NumExtAsFieldWrapper<F, Ext, CS> {
    NumExtAsFieldWrapper::allocate(cs, value)
}

fn enforce_ext_equal<CS: ConstraintSystem<F> + 'static>(
    cs: &mut CS,
    a: NumExtAsFieldWrapper<F, Ext, CS>,
    b: NumExtAsFieldWrapper<F, Ext, CS>,
) {
    for (a, b) in a
        .into_num_coeffs_in_base()
        .into_iter()
        .zip(b.into_num_coeffs_in_base())
    {
        Num::enforce_equal(cs, &a, &b);
    }
}

fn original_quotient<CS: ConstraintSystem<F> + 'static>(
    cs: &mut CS,
    dst: &mut NumExtAsFieldWrapper<F, Ext, CS>,
    sources: &[NumExtAsFieldWrapper<F, Ext, CS>],
    claims: &[NumExtAsFieldWrapper<F, Ext, CS>],
    domain_element: NumAsFieldWrapper<F, CS>,
    at: NumExtAsFieldWrapper<F, Ext, CS>,
    weights: &[NumExtAsFieldWrapper<F, Ext, CS>],
) {
    assert_eq!(sources.len(), claims.len());
    assert_eq!(sources.len(), weights.len());
    let zero = NumAsFieldWrapper::zero(cs);
    let mut denominator =
        NumExtAsFieldWrapper::<F, Ext, CS>::from_coeffs_in_base([domain_element, zero]);
    denominator.sub_assign(&at, cs);
    let inverse = denominator.inverse(cs);
    let mut accumulator = NumExtAsFieldWrapper::<F, Ext, CS>::zero(cs);
    for ((source, claim), weight) in sources.iter().zip(claims).zip(weights) {
        let mut difference = *source;
        difference.sub_assign(claim, cs);
        NumExtAsFieldWrapper::mul_and_accumulate_into(&mut accumulator, &difference, weight, cs);
    }
    NumExtAsFieldWrapper::mul_and_accumulate_into(dst, &accumulator, &inverse, cs);
}

fn native_quotient(
    sources: &[NativeExt],
    claims: &[NativeExt],
    weights: &[NativeExt],
    x: F,
    at: NativeExt,
) -> NativeExt {
    let mut denominator = NativeExt::from_coeff_in_base([x, F::ZERO]);
    Field::sub_assign(&mut denominator, &at);
    let inverse = <NativeExt as PrimeField>::inverse(&denominator).unwrap();
    let mut numerator = NativeExt::ZERO;
    for ((source, claim), weight) in sources.iter().zip(claims).zip(weights) {
        let mut term = *source;
        Field::sub_assign(&mut term, claim);
        Field::mul_assign(&mut term, weight);
        Field::add_assign(&mut numerator, &term);
    }
    Field::mul_assign(&mut numerator, &inverse);
    numerator
}

fn expect_constraint_failure(assembly: &mut Assembly) -> String {
    let worker = Worker::new_with_num_threads(1);
    let error = catch_unwind(AssertUnwindSafe(|| assembly.check_if_satisfied(&worker)))
        .expect_err("tampered witness satisfied the circuit");
    let message = error
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| error.downcast_ref::<&str>().map(|text| (*text).to_owned()))
        .expect("non-string constraint-check failure");
    assert!(message.contains("Unsatisfied at row"), "{message}");
    message
}

#[test]
fn opening_precompute_matches_original_constraints_and_native_across_groups() {
    // False claims must retain the same algebraic relation as honest claims.
    // Distinct group sizes and points expose accidental challenge-slice reuse.
    let group_sizes = [5, 1, 3, 4];
    let points = [
        native_ext(11, 4),
        native_ext(22, 8),
        NativeExt::ZERO,
        native_ext(23, 0),
    ];
    for seed in [
        NativeExt::ZERO,
        NativeExt::ONE,
        native_ext(0, 1),
        native_ext(7, 11),
    ] {
        let mut cs = opening_test_cs!();
        let allocated_seed = allocate_ext(&mut cs, seed);
        let weights = materialize_powers_serial(&mut cs, allocated_seed, group_sizes.iter().sum());
        let mut native_weights = Vec::with_capacity(weights.len());
        let mut power = NativeExt::ONE;
        for _ in 0..weights.len() {
            native_weights.push(power);
            Field::mul_assign(&mut power, &seed);
        }
        let native_claims: Vec<Vec<_>> = group_sizes
            .iter()
            .enumerate()
            .map(|(group, size)| {
                (0..*size)
                    .map(|term| {
                        native_ext(
                            31 + 17 * group as u64 + term as u64,
                            if group == 3 { 0 } else { 47 + term as u64 },
                        )
                    })
                    .collect()
            })
            .collect();
        let claims: Vec<Vec<_>> = native_claims
            .iter()
            .map(|group| {
                group
                    .iter()
                    .map(|value| allocate_ext(&mut cs, *value))
                    .collect()
            })
            .collect();
        let allocated_points: Vec<_> = points
            .iter()
            .map(|point| allocate_ext(&mut cs, *point))
            .collect();
        let mut weighted_claims = Vec::with_capacity(group_sizes.len());
        let mut offset = 0;
        for (group, size) in group_sizes.iter().enumerate() {
            weighted_claims.push(precompute_opening_claim(
                &mut cs,
                &claims[group],
                &weights[offset..offset + size],
            ));
            offset += size;
        }
        assert_eq!(offset, weights.len());
        let before: Vec<_> = weighted_claims
            .iter()
            .map(|claim| claim.witness_hook(&cs)().unwrap())
            .collect();

        for (query, x) in [5, 7, 19].into_iter().enumerate() {
            let x = F::from_u64_with_reduction(x);
            let domain_element = Num::allocate(&mut cs, x).into();
            let initial = native_ext(17 + query as u64, 29);
            let mut optimized = allocate_ext(&mut cs, initial);
            let mut original = allocate_ext(&mut cs, initial);
            let mut expected = initial;
            let mut offset = 0;
            for (group, size) in group_sizes.iter().enumerate() {
                let native_sources: Vec<_> = (0..*size)
                    .map(|term| {
                        native_ext(
                            101 + 19 * query as u64 + 7 * group as u64 + term as u64,
                            if group == 3 { 0 } else { 59 + 3 * term as u64 },
                        )
                    })
                    .collect();
                let sources: Vec<_> = native_sources
                    .iter()
                    .map(|value| allocate_ext(&mut cs, *value))
                    .collect();
                let group_weights = &weights[offset..offset + size];
                quotening_operation(
                    &mut cs,
                    &mut optimized,
                    &sources,
                    &claims[group],
                    weighted_claims[group],
                    domain_element,
                    allocated_points[group],
                    group_weights,
                );
                original_quotient(
                    &mut cs,
                    &mut original,
                    &sources,
                    &claims[group],
                    domain_element,
                    allocated_points[group],
                    group_weights,
                );
                let contribution = native_quotient(
                    &native_sources,
                    &native_claims[group],
                    &native_weights[offset..offset + size],
                    x,
                    points[group],
                );
                Field::add_assign(&mut expected, &contribution);
                offset += size;
            }
            assert_eq!(offset, weights.len());
            assert_eq!(optimized.witness_hook(&cs)().unwrap(), expected);
            assert_eq!(original.witness_hook(&cs)().unwrap(), expected);
            enforce_ext_equal(&mut cs, optimized, original);
        }
        let after: Vec<_> = weighted_claims
            .iter()
            .map(|claim| claim.witness_hook(&cs)().unwrap())
            .collect();
        assert_eq!(before, after);
        cs.pad_and_shrink();
        assert!(cs
            .into_assembly::<Global>()
            .check_if_satisfied(&Worker::new_with_num_threads(1)));
    }
}

#[test]
fn opening_precompute_rejects_a_tampered_weighted_claim_witness() {
    let mut cs = opening_test_cs!();
    let claims = [
        allocate_ext(&mut cs, native_ext(31, 47)),
        allocate_ext(&mut cs, native_ext(13, 19)),
    ];
    let weights = [
        allocate_ext(&mut cs, NativeExt::ONE),
        allocate_ext(&mut cs, native_ext(2, 7)),
    ];
    let weighted = precompute_opening_claim(&mut cs, &claims, &weights);
    let output = weighted.into_num_coeffs_in_base()[0].get_variable();
    let claim = claims[0].into_num_coeffs_in_base()[0].get_variable();
    let weight = weights[1].into_num_coeffs_in_base()[1].get_variable();
    cs.pad_and_shrink();
    let mut assembly = cs.into_assembly::<Global>();
    assert!(assembly.check_if_satisfied(&Worker::new_with_num_threads(1)));
    for variable in [output, claim, weight] {
        let index = variable.as_variable_index() as usize;
        let original = assembly.witness.as_ref().unwrap().all_values[index];
        Field::add_assign(
            &mut assembly.witness.as_mut().unwrap().all_values[index],
            &F::ONE,
        );
        expect_constraint_failure(&mut assembly);
        assembly.witness.as_mut().unwrap().all_values[index] = original;
    }
}

#[test]
fn opening_precompute_keeps_zero_opening_denominator_inversion_constrained() {
    let mut cs = opening_test_cs!();
    let claims = [allocate_ext(&mut cs, native_ext(31, 47))];
    let sources = [allocate_ext(&mut cs, native_ext(29, 43))];
    let weights = [allocate_ext(&mut cs, native_ext(5, 9))];
    let weighted = precompute_opening_claim(&mut cs, &claims, &weights);
    let domain = Num::allocate(&mut cs, F::from_u64_with_reduction(13));
    let at = allocate_ext(&mut cs, NativeExt::ZERO);
    let mut result = allocate_ext(&mut cs, NativeExt::ZERO);
    quotening_operation(
        &mut cs,
        &mut result,
        &sources,
        &claims,
        weighted,
        domain.into(),
        at,
        &weights,
    );
    cs.pad_and_shrink();
    let mut assembly = cs.into_assembly::<Global>();
    assert!(assembly.check_if_satisfied(&Worker::new_with_num_threads(1)));

    // Keep the subtraction consistent with x = t = 0 and retain the otherwise
    // valid witness. Rejection must come from the denominator * inverse = 1 gate.
    let inverse_row = assembly
        .constants_requested_per_row
        .iter()
        .position(|constants| constants.as_slice() == [F::ONE, F::ZERO, F::ZERO, F::ZERO])
        .expect("quotient helper omitted its inversion constraint");
    let denominator = [
        assembly.copy_permutation_data[0][inverse_row],
        assembly.copy_permutation_data[1][inverse_row],
    ];
    let values = &mut assembly.witness.as_mut().unwrap().all_values;
    values[domain.get_variable().as_variable_index() as usize] = F::ZERO;
    for variable in denominator {
        values[variable.as_variable_index() as usize] = F::ZERO;
    }
    assert!(expect_constraint_failure(&mut assembly).contains("quadratic extension"));
}

#[test]
fn opening_precompute_rejects_claim_weight_length_mismatch() {
    let mut cs = opening_test_cs!();
    let claims = [allocate_ext(&mut cs, native_ext(31, 47))];
    assert!(catch_unwind(AssertUnwindSafe(|| {
        precompute_opening_claim(&mut cs, &claims, &[])
    }))
    .is_err());
}

#[test]
fn opening_precompute_quotient_rejects_source_claim_or_weight_length_mismatch() {
    for omit_claim in [false, true] {
        let mut cs = opening_test_cs!();
        let claims = [allocate_ext(&mut cs, native_ext(31, 47))];
        let sources = [allocate_ext(&mut cs, native_ext(29, 43))];
        let weights = [allocate_ext(&mut cs, native_ext(5, 9))];
        let weighted = precompute_opening_claim(&mut cs, &claims, &weights);
        let domain = Num::allocate(&mut cs, F::from_u64_with_reduction(13)).into();
        let at = allocate_ext(&mut cs, NativeExt::ZERO);
        let mut result = allocate_ext(&mut cs, NativeExt::ZERO);
        assert!(catch_unwind(AssertUnwindSafe(|| {
            quotening_operation(
                &mut cs,
                &mut result,
                &sources,
                if omit_claim { &[] } else { &claims },
                weighted,
                domain,
                at,
                if omit_claim { &weights } else { &[] },
            )
        }))
        .is_err());
    }
}
