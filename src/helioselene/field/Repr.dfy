include "Arith.dfy"

module FieldRepr {
  import opened FieldBase
  import opened FieldRed256
  import opened FieldArith
  import opened CryptoBigint_0_5_5_Limb
  import opened CryptoBigint_0_5_5_U256
  import opened CryptoBigint_0_5_5_U128
  import opened Limbs
  import DivMod = Std.Arithmetic.DivMod

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L734-L755
  // from_repr: validate that a U256 represents a reduced field element (value < p).
  // In Rust, this takes [u8; 32] and parses as little-endian; here we take U256 directly.
  //
  // Algorithm: add MODULUS_255_DISTANCE to the value; if the sum fits below 2^255
  // (no top bit set in limb[3], no carry out), then the original value is < p.
  // Correctness: a + dist < 2^255 iff a < 2^255 - dist = p.
  //
  // NOTE: If valid, result.inner aliases input a (no copy). Caller must not modify a.limbs.
  method {:fuel LimbsSumSpec,5} field_from_repr(a: U256) returns (valid: bool, result: HelioseleneField)
    requires a.Valid()
    ensures valid <==> a.ValueSpec() < ModulusValueSpec()
    ensures valid ==> result.inner == a && ValidField(result)
  {
    // original code (inner `reduced` function):
    // let mut b_limbs = MODULUS_255_DISTANCE.as_limbs().iter();
    // let mut last = Limb::ZERO;
    // let mut carry = Limb::ZERO;
    // for a in a.as_limbs() {
    //   let b = b_limbs.next().unwrap_or(&Limb::ZERO);
    //   (last, carry) = add_with_bounded_overflow(*a, *b, carry);
    // }
    // ((last & (Limb::ONE << (Limb::BITS - 1))) | carry).ct_eq(&Limb::ZERO)
    var distance := Modulus255Distance();
    var dist_limbs := distance.as_limbs();
    var a_limbs := a.as_limbs();
    var last := ZeroLimb();
    var carry := ZeroLimb();

    // GHOST CODE: define the 4-limb distance sequence (upper two limbs are zero)
    ghost var dist4 := [dist_limbs[0], dist_limbs[1], ZeroLimb(), ZeroLimb()];
    ghost var a4 := a_limbs[..];

    // GHOST CODE: the 4-limb distance has the same value as Modulus255DistanceSpec
    assert dist4 == [Modulus255DistanceLimbs()[0], Modulus255DistanceLimbs()[1], ZeroLimb(), ZeroLimb()];
    assert LimbsValueSpec(dist4) == Modulus255DistanceSpec();

    // GHOST CODE: compute the full sum spec
    ghost var fullSum := LimbsSumSpec(a4, dist4, ZeroLimb());
    // LimbsSumSpec ensures: LimbsValueSpec(fullSum) == a.ValueSpec() + Modulus255DistanceSpec()

    // i=0: dist_limbs[0] = 0x067af49720ee20ad
    last, carry := add_with_bounded_overflow(a_limbs[0], dist_limbs[0], carry);
    ghost var r0 := last;
    ghost var c0 := carry;
    // Post: AddAndCarryLimbSpec(a4[0], dist4[0], ZeroLimb()) == (r0, c0)

    // i=1: dist_limbs[1] = 0x08cab7e2e6960ce8
    last, carry := add_with_bounded_overflow(a_limbs[1], dist_limbs[1], carry);
    ghost var r1 := last;
    ghost var c1 := carry;
    // Post: AddAndCarryLimbSpec(a4[1], dist4[1], c0) == (r1, c1)

    // i=2,3: MODULUS_255_DISTANCE is 128-bit, upper limbs of distance are zero
    last, carry := add_with_bounded_overflow(a_limbs[2], ZeroLimb(), carry);
    ghost var r2 := last;
    ghost var c2 := carry;
    // Post: AddAndCarryLimbSpec(a4[2], ZeroLimb(), c1) == (r2, c2)

    last, carry := add_with_bounded_overflow(a_limbs[3], ZeroLimb(), carry);
    // Post: AddAndCarryLimbSpec(a4[3], ZeroLimb(), c2) == (last, carry)

    // GHOST CODE: connect our computation to LimbsSumSpec
    assert AddAndCarryLimbSpec(a4[0], dist4[0], ZeroLimb()) == (r0, c0);
    assert AddAndCarryLimbSpec(a4[1], dist4[1], c0) == (r1, c1);
    assert AddAndCarryLimbSpec(a4[2], dist4[2], c1) == (r2, c2);
    assert AddAndCarryLimbSpec(a4[3], dist4[3], c2) == (last, carry);

    // LimbsSumSpec produces [r0, r1, r2, last, carry]
    assert fullSum == [r0, r1, r2, last, carry];

    // LEMMAS: connect sum to value specs
    // fullSum has 5 elements; first 4 are the sum limbs, 5th is carry
    WrappingAddLemma(fullSum, LimbToInt(carry));
    // ==> LimbsValueSpec(fullSum[..4]) + LimbToInt(carry) * WORD_MODULUS4
    //     == LimbsValueSpec(fullSum)
    //     == a.ValueSpec() + Modulus255DistanceSpec()

    // Check: MSB of last limb clear AND no carry out
    // Equivalent to: (last & (1 << 63)) | carry == 0
    valid := (LimbToInt(last) < WORD_MODULUS / 2) && (carry == ZeroLimb());

    // GHOST CODE: prove valid <==> a.ValueSpec() < ModulusValueSpec()
    ghost var sumVal := LimbsValueSpec(fullSum[..4]);
    ghost var carryVal := LimbToInt(carry);

    // Build a ghost U256 from fullSum[..4] to use U256MostSignificantBitLemma
    ghost var sumU256limbs := [r0, r1, r2, last];
    assert sumU256limbs == fullSum[..4];

    // Key connection: sumVal + carryVal * W^4 == a.ValueSpec() + Modulus255DistanceSpec()
    assert sumVal + carryVal * WORD_MODULUS4 == a.ValueSpec() + Modulus255DistanceSpec();

    // Case 1: carry == 0
    // Then sumVal == a.ValueSpec() + Modulus255DistanceSpec()
    // valid <==> LimbToInt(last) < W/2
    //        <==> sumVal < W^4/2  (by U256MostSignificantBitLemma-like reasoning on limbs)
    //        <==> a.ValueSpec() + dist < 2^255
    //        <==> a.ValueSpec() < 2^255 - dist = p

    // Case 2: carry == 1
    // Then sumVal + W^4 == a.ValueSpec() + dist, so a.ValueSpec() + dist >= W^4 >= W^4/2
    // Hence a.ValueSpec() >= W^4 - dist = 2^256 - dist > p, so not valid

    if carry == ZeroLimb() {
      assert carryVal == 0;
      assert sumVal == a.ValueSpec() + Modulus255DistanceSpec();

      // Connect LimbToInt(last) < W/2 to sumVal < W^4/2
      // LimbsValueSpec([r0, r1, r2, last]) < W^4/2
      //   <==> LimbToInt(last) < W/2
      // This is the U256MostSignificantBitLemma pattern applied to our 4 limbs
      assert LimbsValueSpec(sumU256limbs) == LimbToInt(r0) + LimbToInt(r1) * WORD_MODULUS + LimbToInt(r2) * WORD_MODULUS2 + LimbToInt(last) * WORD_MODULUS3;
      FromReprMsbLemma(r0, r1, r2, last);

      // Now: valid <==> sumVal < WORD_MODULUS4 / 2
      //          <==> a.ValueSpec() + Modulus255DistanceSpec() < WORD_MODULUS4 / 2
      //          <==> a.ValueSpec() < WORD_MODULUS4 / 2 - Modulus255DistanceSpec()
      //          <==> a.ValueSpec() < ModulusValueSpec()
      FromReprModulusRelationLemma();
    } else {
      assert carryVal == 1;
      assert sumVal + WORD_MODULUS4 == a.ValueSpec() + Modulus255DistanceSpec();
      // a.ValueSpec() + dist >= W^4 > W^4/2 > p + dist, so a.ValueSpec() > p
      assert a.ValueSpec() + Modulus255DistanceSpec() >= WORD_MODULUS4;
      assert a.ValueSpec() >= WORD_MODULUS4 - Modulus255DistanceSpec();
      FromReprModulusRelationLemma();
      assert ModulusValueSpec() == WORD_MODULUS4 / 2 - Modulus255DistanceSpec();
      assert a.ValueSpec() >= ModulusValueSpec();
    }

    if valid {
      result := HelioseleneField(a);
    } else {
      var zero_limbs: array<Limb> := new Limb[U256_LIMBS][ZeroLimb(), ZeroLimb(), ZeroLimb(), ZeroLimb()];
      var zero_u256 := new U256(zero_limbs);
      result := HelioseleneField(zero_u256);
    }
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L754-L756
  // to_repr: serialize a field element as its inner U256.
  // In Rust, this returns [u8; 32] (little-endian bytes); we return the U256 directly.
  method field_to_repr(a: HelioseleneField) returns (result: U256)
    requires ValidField(a)
    ensures result.Valid()
    ensures result.ValueSpec() == a.inner.ValueSpec()
  {
    // original code: self.0.to_le_bytes()
    result := a.inner;
  }
}
