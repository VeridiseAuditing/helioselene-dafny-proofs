include "Math.dfy"

// General-purpose modular exponentiation: pow_mod and supporting lemmas.
// Extracted from Field.dfy for modularity (REORG-004).

module PowMod {
  import MathHelpers
  import Power = Std.Arithmetic.Power
  import DivMod = Std.Arithmetic.DivMod

  // Ghost function for modular exponentiation: base^exp mod modulus.
  ghost function {:rlimit 38} pow_mod(base: int, exp: int, modulus: int): int
    requires modulus > 0
    requires 0 <= base < modulus
    requires 0 <= exp
    decreases exp
  {
    if exp == 0 then 1 % modulus
    else if exp % 2 == 0 then
      var half := pow_mod(base, exp / 2, modulus);
      (half * half) % modulus
    else
      (base * pow_mod(base, exp - 1, modulus)) % modulus
  }

  // Bridge: pow_mod(b, e, m) == Pow(b, e) % m
  // Connects our squaring-based pow_mod to the standard library's linear Pow,
  // enabling use of LemmaPowAdds, LemmaPowMultiplies, etc.
  lemma {:rlimit 141} PowModEqPowLemma(base: int, exp: int, modulus: int)
    requires modulus > 0
    requires 0 <= base < modulus
    requires 0 <= exp
    decreases exp
    ensures pow_mod(base, exp, modulus) == Power.Pow(base, exp) % modulus
  {
    if exp == 0 {
    } else if exp % 2 == 0 {
      PowModEqPowLemma(base, exp / 2, modulus);
      var half := Power.Pow(base, exp / 2);
      DivMod.LemmaMulModNoopGeneral(half, half, modulus);
      Power.LemmaPowAdds(base, exp / 2, exp / 2);
      assert exp / 2 + exp / 2 == exp;
    } else {
      PowModEqPowLemma(base, exp - 1, modulus);
      DivMod.LemmaMulModNoopRight(base, Power.Pow(base, exp - 1), modulus);
    }
  }

  // pow_mod base cases and identities
  lemma {:rlimit 30} PowModZeroLemma(base: int, modulus: int)
    requires modulus > 0
    requires 0 <= base < modulus
    ensures pow_mod(base, 0, modulus) == 1 % modulus
  {
  }

  lemma {:rlimit 18240} PowModOneLemma(base: int, modulus: int)
    requires modulus > 0
    requires 0 <= base < modulus
    ensures pow_mod(base, 1, modulus) == base % modulus
  {
  }

  // pow_mod result is always in [0, modulus)
  lemma {:rlimit 82} PowModBoundLemma(base: int, exp: int, modulus: int)
    requires modulus > 0
    requires 0 <= base < modulus
    requires 0 <= exp
    decreases exp
    ensures 0 <= pow_mod(base, exp, modulus) < modulus
  {
    if exp == 0 {
    } else if exp % 2 == 0 {
      PowModBoundLemma(base, exp / 2, modulus);
    } else {
      PowModBoundLemma(base, exp - 1, modulus);
    }
  }

  // pow_mod(b, e1 + e2, m) == (pow_mod(b, e1, m) * pow_mod(b, e2, m)) % m
  lemma {:rlimit 138} PowModAddLemma(base: int, e1: int, e2: int, modulus: int)
    requires modulus > 0
    requires 0 <= base < modulus
    requires 0 <= e1 && 0 <= e2
    ensures pow_mod(base, e1 + e2, modulus)
         == (pow_mod(base, e1, modulus) * pow_mod(base, e2, modulus)) % modulus
  {
    PowModEqPowLemma(base, e1 + e2, modulus);
    PowModEqPowLemma(base, e1, modulus);
    PowModEqPowLemma(base, e2, modulus);
    Power.LemmaPowAdds(base, e1, e2);
    DivMod.LemmaMulModNoopGeneral(
      Power.Pow(base, e1), Power.Pow(base, e2), modulus);
  }

  // pow_mod(b, e1 * e2, m) == pow_mod(pow_mod(b, e1, m), e2, m)
  lemma {:rlimit 57} PowModMulExpLemma(base: int, e1: int, e2: int, modulus: int)
    requires modulus > 0
    requires 0 <= base < modulus
    requires 0 <= e1 && 0 <= e2
    ensures pow_mod(base, e1 * e2, modulus)
         == pow_mod(pow_mod(base, e1, modulus), e2, modulus)
  {
    PowModBoundLemma(base, e1, modulus);
    var pe1 := pow_mod(base, e1, modulus);
    Power.LemmaPowMultiplies(base, e1, e2);
    PowModEqPowLemma(base, e1 * e2, modulus);
    PowModEqPowLemma(pe1, e2, modulus);
    PowModEqPowLemma(base, e1, modulus);
    Power.LemmaPowModNoop(Power.Pow(base, e1), e2, modulus);
  }

  // Squaring k times: pow_mod(pow_mod(b, e, m), 2^k, m) == pow_mod(b, e * 2^k, m)
  lemma {:rlimit 81} PowModSquareChainLemma(base: int, exp: int, k: nat, modulus: int)
    requires modulus > 0
    requires 0 <= base < modulus
    requires 0 <= exp
    requires MathHelpers.pow2(k) >= 0
    ensures pow_mod(pow_mod(base, exp, modulus), MathHelpers.pow2(k), modulus)
         == pow_mod(base, exp * MathHelpers.pow2(k), modulus)
  {
    PowModMulExpLemma(base, exp, MathHelpers.pow2(k), modulus);
  }

  // Window step: squaring 4 times then multiplying by table[bits]
  lemma {:rlimit 78} PowModWindowStepLemma(base: int, prefix_exp: int, window_bits: int, modulus: int)
    requires modulus > 0
    requires 0 <= base < modulus
    requires 0 <= prefix_exp
    requires 0 <= window_bits < 16
    ensures pow_mod(base, prefix_exp * 16 + window_bits, modulus)
         == (pow_mod(pow_mod(base, prefix_exp, modulus), 16, modulus)
             * pow_mod(base, window_bits, modulus)) % modulus
  {
    PowModAddLemma(base, prefix_exp * 16, window_bits, modulus);
    MathHelpers.Pow2PositiveLemma(4);
    assert MathHelpers.pow2(4) == 16;
    PowModSquareChainLemma(base, prefix_exp, 4, modulus);
  }

  // First window (no squaring): pow_mod(b, k, m) == (1 * pow_mod(b, k, m)) % m
  lemma {:rlimit 39} PowModFirstWindowLemma(base: int, window_bits: int, modulus: int)
    requires modulus > 1
    requires 0 <= base < modulus
    requires 0 <= window_bits < 16
    ensures pow_mod(base, window_bits, modulus)
         == (pow_mod(base, 0, modulus) * pow_mod(base, window_bits, modulus)) % modulus
  {
    PowModAddLemma(base, 0, window_bits, modulus);
  }
}
