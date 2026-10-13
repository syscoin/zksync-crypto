use self::super::prime_field_like::GoldilocksExtAsFieldWrapper;
use super::*;
use crate::bellman::pairing::bn256::Bn256;
use crate::bellman::plonk::better_better_cs::cs::*;
use boojum::field::traits::field_like::PrimeFieldLike;

type Assembly = TrivialAssembly<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>;

fn operand(cs: &mut Assembly, value: u64, variable: bool) -> GoldilocksField<Bn256> {
    if variable {
        GoldilocksField::alloc_from_u64(cs, Some(value)).unwrap()
    } else {
        GoldilocksField::constant(value)
    }
}

#[test]
fn goldilocks_boundary_addition_reduces_the_modulus() {
    let p = GoldilocksField::<Bn256>::ORDER;
    for (a, b) in [(0, 0), (1, p - 2), (1, p - 1), (2, p - 1), (p - 1, p - 1), (p / 2, p - p / 2)] {
        for (a_variable, b_variable) in [(true, true), (true, false), (false, true), (false, false)] {
            let mut cs = Assembly::new();
            let a_num = operand(&mut cs, a, a_variable);
            let b_num = operand(&mut cs, b, b_variable);
            let result = a_num.add(&mut cs, &b_num).unwrap();
            let expected = ((a as u128 + b as u128) % p as u128) as u64;
            assert_eq!(result.into_u64(), Some(expected), "{a} + {b}; variable modes {a_variable}/{b_variable}");
            assert!(cs.is_satisfied());
        }
    }
}

#[test]
fn goldilocks_boundary_equal_extension_subtraction_is_zero() {
    let p = GoldilocksField::<Bn256>::ORDER;
    for [c0, c1] in [[0, 0], [1, 0], [1, 2], [1 << 32, p - 1], [p - 1, p - 1]] {
        for (a_variable, b_variable) in [(true, true), (true, false), (false, true), (false, false)] {
            let mut cs = Assembly::new();
            let a = [operand(&mut cs, c0, a_variable), operand(&mut cs, c1, a_variable)];
            let b = [operand(&mut cs, c0, b_variable), operand(&mut cs, c1, b_variable)];
            let mut difference = GoldilocksExtAsFieldWrapper::<Bn256, Assembly>::from_coeffs_in_base(a);
            let other = GoldilocksExtAsFieldWrapper::<Bn256, Assembly>::from_coeffs_in_base(b);
            difference.sub_assign(&other, &mut cs);
            for coordinate in difference.into_coeffs_in_base() {
                assert_eq!(coordinate.into_u64(), Some(0));
            }
            assert!(cs.is_satisfied());
        }
    }
}
