include "Red512.dfy"

module FieldArith {
  import opened FieldBase
  import opened FieldRed256
  import opened FieldRed512
  import opened CryptoBigint_0_5_5_Limb
  import opened CryptoBigint_0_5_5_U256
  import Modular
  import opened Limbs
  import DivMod = Std.Arithmetic.DivMod

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L146-L148
  // field_add: HelioseleneField(red1(self.0.wrapping_add(&b.0)))
  method field_add(a: HelioseleneField, b: HelioseleneField) returns (result: HelioseleneField)
    requires ValidField(a)
    requires ValidField(b)
    ensures ValidField(result)
    ensures fresh(result.inner) && fresh(result.inner.limbs)
    ensures result.inner.ValueSpec() == (a.inner.ValueSpec() + b.inner.ValueSpec()) % ModulusValueSpec()
  {
    // original code: HelioseleneField(red1(self.0.wrapping_add(&b.0)))
    var sum := a.inner.wrapping_add(b.inner);

    // LEMMAS: a < p, b < p, so a + b < 2p. Since 2p < 2^256, no wrap occurs.
    ghost var p := ModulusValueSpec();
    TwoModulusLt2Pow256Lemma();
    assert a.inner.ValueSpec() + b.inner.ValueSpec() < 2 * p;
    assert a.inner.ValueSpec() + b.inner.ValueSpec() < WORD_MODULUS4;
    assert sum.ValueSpec() == a.inner.ValueSpec() + b.inner.ValueSpec();

    // original code: HelioseleneField(red1(...))
    assert sum.ValueSpec() < 2 * p;
    var reduced := red1(sum);
    result := HelioseleneField(reduced);
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L207-L216
  // field_sub: sub_value then conditional wrapping_add(MODULUS), select
  method {:isolate_assertions} {:fuel LimbsSumSpec, 5} field_sub(a: HelioseleneField, b: HelioseleneField) returns (result: HelioseleneField)
    requires ValidField(a)
    requires ValidField(b)
    ensures ValidField(result)
    ensures fresh(result.inner) && fresh(result.inner.limbs)
    ensures result.inner.ValueSpec() == (a.inner.ValueSpec() - b.inner.ValueSpec()) % ModulusValueSpec()
  {
    // original code:
    // let (candidate, underflowed) = sub_value(self.0, b.0);
    // let plus_modulus = candidate.wrapping_add(&MODULUS);
    // let mut out = U256::ZERO;
    // for j in 0 .. U256::LIMBS {
    //   out.as_limbs_mut()[j] = select_word(candidate.as_limbs()[j], plus_modulus.as_limbs()[j], underflowed);
    // }
    var candidate, underflowed := sub_value(a.inner, b.inner);
    var MODULUS := Modulus();
    var plus_modulus := candidate.wrapping_add(MODULUS);
    var out := U256_Zero();

    for j: int := 0 to U256_LIMBS
      invariant 0 <= j <= U256_LIMBS
      invariant out.Valid()
      invariant out.limbs[..j] == if underflowed == ZeroLimb()
        then candidate.limbs[..j]
        else plus_modulus.limbs[..j]
      invariant fresh(out.limbs)
      modifies out.limbs
    {
      var candidate_limbs := candidate.as_limbs();
      var plus_modulus_limbs := plus_modulus.as_limbs();
      var out_as_limbs_mut := out.as_limbs_mut();
      out_as_limbs_mut[j] := select_word(candidate_limbs[j], plus_modulus_limbs[j], underflowed);
    }

    result := HelioseleneField(out);

    // LEMMAS
    ghost var p := ModulusValueSpec();
    ghost var av := a.inner.ValueSpec();
    ghost var bv := b.inner.ValueSpec();
    ghost var d := av - bv;
    if underflowed == ZeroLimb() {
      // No underflow: a >= b, candidate = a - b
      assert out.limbs[..] == candidate.limbs[..];
      assert result.inner.ValueSpec() == candidate.ValueSpec();
      assert candidate.ValueSpec() == d;
      assert 0 <= d < p;
      Modular.LessThanModulusMeansIsReducedLemma(d, p);
    } else {
      // Underflow: a < b, candidate = a - b + 2^256
      assert out.limbs[..] == plus_modulus.limbs[..];
      assert result.inner.ValueSpec() == plus_modulus.ValueSpec();
      assert candidate.ValueSpec() == d + WORD_MODULUS4;
      // plus_modulus = (candidate + MODULUS) % 2^256 = (d + 2^256 + p) % 2^256
      // Since -p < d < 0: 2^256 <= d + 2^256 + p < 2^256 + p < 2 * 2^256
      // But actually d + 2^256 + p >= 2^256, and < 2^256 + p < 2^257, so mod 2^256 = d + p
      assert d < 0;
      assert d >= -p + 1 || d == -p;
      assert d + p >= 0;
      TwoModulusLt2Pow256Lemma();
      assert 0 <= d + p < p;
      assert d + p < WORD_MODULUS4;
      // candidate.ValueSpec() + p = d + WORD_MODULUS4 + p
      // wrapping_add gives (candidate.ValueSpec() + p) % WORD_MODULUS4
      assert plus_modulus.ValueSpec() == (candidate.ValueSpec() + p) % WORD_MODULUS4;
      assert candidate.ValueSpec() + p == d + WORD_MODULUS4 + p;
      assert d + WORD_MODULUS4 + p == (d + p) + WORD_MODULUS4;
      // (d + p) + WORD_MODULUS4 mod WORD_MODULUS4 == d + p since 0 <= d+p < WORD_MODULUS4
      DropCarryModLemma(d + p, 1, (d + p) + WORD_MODULUS4);
      assert plus_modulus.ValueSpec() == d + p;
      assert 0 <= d + p < p;
      Modular.LessThanModulusMeansIsReducedLemma(d + p, p);
      FieldSubModLemma(av, bv, p);
    }
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L187-L193
  // field_neg: conditional_select(&neg, &Self::ZERO, self.is_zero())
  // NOTE: Rust uses constant-time conditional_select; Dafny uses if/else branch (VT).
  method {:timeLimit 240} {:isolate_assertions} field_neg(a: HelioseleneField) returns (result: HelioseleneField)
    requires ValidField(a)
    ensures ValidField(result)
    ensures fresh(result.inner) && fresh(result.inner.limbs)
    ensures result.inner.ValueSpec() == (ModulusValueSpec() - a.inner.ValueSpec()) % ModulusValueSpec()
  {
    // original code:
    // HelioseleneField(MODULUS.wrapping_sub(&self.0))
    var MODULUS := Modulus();
    var neg_inner := MODULUS.wrapping_sub(a.inner);

    // original code:
    // self.is_zero()
    // Computes OR of all limbs, then ct_eq with zero.
    // is_zero is true when a == 0, false otherwise.
    var a_as_limbs := a.inner.as_limbs();
    var all_zero := true;
    for l := 0 to U256_LIMBS
      invariant all_zero <==> (forall k :: 0 <= k < l ==> a_as_limbs[k] == ZeroLimb())
    {
      if a_as_limbs[l] != ZeroLimb() {
        all_zero := false;
      }
    }

    // original code:
    // conditional_select(&neg, &Self::ZERO, is_zero)
    // When is_zero: select ZERO. Otherwise: select neg.
    var out: U256;
    if all_zero {
      out := U256_Zero();
    } else {
      out := neg_inner;
    }
    result := HelioseleneField(out);

    // LEMMAS
    ghost var p := ModulusValueSpec();
    ghost var av := a.inner.ValueSpec();
    assert MODULUS.ValueSpec() == p;
    assert neg_inner.ValueSpec() == (p - av) % WORD_MODULUS4;
    assert 0 <= p - av <= p;
    assert p < WORD_MODULUS4;
    assert neg_inner.ValueSpec() == p - av;
    if all_zero {
      assert av == 0;
      assert result.inner.ValueSpec() == 0;
      assert (p - 0) % p == 0;
    } else {
      assert av > 0;
      assert result.inner.ValueSpec() == p - av;
      assert 0 < p - av < p;
      Modular.LessThanModulusMeansIsReducedLemma(p - av, p);
    }
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L456-L458
  // field_double: HelioseleneField(red1(self.0.shl_vartime(1)))
  method field_double(a: HelioseleneField) returns (result: HelioseleneField)
    requires ValidField(a)
    ensures ValidField(result)
    ensures fresh(result.inner) && fresh(result.inner.limbs)
    ensures result.inner.ValueSpec() == (2 * a.inner.ValueSpec()) % ModulusValueSpec()
  {
    // original code: HelioseleneField(red1(self.0.shl_vartime(1)))
    var shifted := a.inner.shl_vartime(1);

    // LEMMAS: a < p < 2^255, so 2a < 2^256, no wrap
    ghost var p := ModulusValueSpec();
    ghost var av := a.inner.ValueSpec();
    TwoModulusLt2Pow256Lemma();
    assert av < p;
    assert 2 * av < 2 * p;
    assert 2 * p < WORD_MODULUS4;
    assert shifted.ValueSpec() == (2 * av) % WORD_MODULUS4;
    assert shifted.ValueSpec() == 2 * av;
    assert shifted.ValueSpec() < 2 * p;

    // original code: HelioseleneField(red1(...))
    var reduced := red1(shifted);
    result := HelioseleneField(reduced);
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L336-L338
  // field_mul: red512(self.0.mul_wide(&b.0))
  method field_mul(a: HelioseleneField, b: HelioseleneField) returns (result: HelioseleneField)
    requires ValidField(a)
    requires ValidField(b)
    ensures ValidField(result)
    ensures result.inner.ValueSpec() == (a.inner.ValueSpec() * b.inner.ValueSpec()) % ModulusValueSpec()
    ensures fresh(result.inner) && fresh(result.inner.limbs)
  {
    // original code: red512(self.0.mul_wide(&b.0))
    var wide := a.inner.mul_wide(b.inner);
    // LEMMAS: connect mul_wide postcondition to Wide512ValueSpec
    ghost var lo := wide.0.ValueSpec();
    ghost var hi := wide.1.ValueSpec();
    Pow256EqWordModulus4Lemma();
    assert Wide512ValueSpec(wide.0, wide.1) == lo + hi * WORD_MODULUS4;
    assert lo + hi * WORD_MODULUS4 == a.inner.ValueSpec() * b.inner.ValueSpec();
    result := red512(wide);
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L461-L463
  // field_square: red512(self.0.square_wide())
  method field_square(a: HelioseleneField) returns (result: HelioseleneField)
    requires ValidField(a)
    ensures ValidField(result)
    ensures result.inner.ValueSpec() == (a.inner.ValueSpec() * a.inner.ValueSpec()) % ModulusValueSpec()
    ensures fresh(result.inner) && fresh(result.inner.limbs)
  {
    // original code: red512(self.0.square_wide())
    var wide := a.inner.square_wide();
    // LEMMAS: connect square_wide postcondition to Wide512ValueSpec
    ghost var lo := wide.0.ValueSpec();
    ghost var hi := wide.1.ValueSpec();
    Pow256EqWordModulus4Lemma();
    assert Wide512ValueSpec(wide.0, wide.1) == lo + hi * WORD_MODULUS4;
    assert lo + hi * WORD_MODULUS4 == a.inner.ValueSpec() * a.inner.ValueSpec();
    result := red512(wide);
  }
}
