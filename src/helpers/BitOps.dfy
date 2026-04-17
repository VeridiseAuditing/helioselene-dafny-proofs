include "Math.dfy"

// General-purpose bit operations: TopBits and supporting lemmas.
// Extracted from Field.dfy for modularity (REORG-005).

module BitOps {
  import MathHelpers
  import DivMod = Std.Arithmetic.DivMod

  // Top k bits of a 256-bit value: val / 2^(256-k)
  ghost function {:rlimit 36} TopBits(val: int, k: nat): int
    requires 0 <= val
    requires 0 <= k <= 256
  {
    // pow2(256-k) > 0 follows from Pow2PositiveLemma
    // For Dafny: 256-k is in 0..256, all concrete cases of pow2 return > 0
    var divisor := MathHelpers.pow2(256 - k);
    if divisor > 0 then val / divisor else 0  // divisor is always > 0 but Dafny can't prove it
  }

  // TopBits(val, 0) == 0 for val < 2^256
  lemma {:rlimit 257} TopBitsZeroLemma(val: int)
    requires 0 <= val < MathHelpers.pow2(256)
    ensures TopBits(val, 0) == 0
  {
    MathHelpers.Pow2PositiveLemma(256);
  }

  // TopBits(val, 256) == val
  lemma {:rlimit 39} TopBits256Lemma(val: int)
    requires 0 <= val
    ensures TopBits(val, 256) == val
  {
    MathHelpers.Pow2PositiveLemma(0);
    assert MathHelpers.pow2(0) == 1;
  }

  // TopBits step: TopBits(val, k+1) == TopBits(val, k) * 2 + bit_at_position_(255-k)
  lemma {:rlimit 94} TopBitsStepLemma(val: int, k: nat)
    requires 0 <= val
    requires 0 <= k < 256
    ensures TopBits(val, k + 1) == TopBits(val, k) * 2 + (val / MathHelpers.pow2(255 - k)) % 2
  {
    MathHelpers.Pow2PositiveLemma(255 - k);
    MathHelpers.Pow2PositiveLemma(256 - k);
    var d := MathHelpers.pow2(255 - k);
    var d2 := MathHelpers.pow2(256 - k);
    assert d > 0;
    assert d2 > 0;
    MathHelpers.Pow2DoubleLemma(255 - k);
    assert d2 == 2 * d;
    assert TopBits(val, k + 1) == val / d;
    assert TopBits(val, k) == val / d2;
    DivMod.LemmaDivDenominator(val, d, 2);
    assert (val / d) / 2 == val / (d * 2);
    assert d * 2 == 2 * d;
    var q := val / d;
    assert q == (q / 2) * 2 + q % 2;
  }
}
