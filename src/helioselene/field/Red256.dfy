include "Base.dfy"

module FieldRed256 {
  import opened FieldBase
  import opened CryptoBigint_0_5_5_Limb
  import opened CryptoBigint_0_5_5_U256
  import opened CryptoBigint_0_5_5_U128
  import Modular
  import opened Limbs
  import DivMod = Std.Arithmetic.DivMod

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L111-L119
  method {:rlimit 372002} red1(a: U256) returns (ret: U256)
    requires a.Valid()
    requires a.ValueSpec() < 2 * ModulusValueSpec()
    ensures ret.Valid()
    ensures fresh(ret) && fresh(ret.limbs)
    ensures 0 <= ret.ValueSpec() < ModulusValueSpec()
    ensures ret.ValueSpec() == a.ValueSpec() % ModulusValueSpec()
  {
    // original code:
    // let (reduced, borrow) = sub_value(a, MODULUS);
    // let mut out = U256::ZERO;
    var MODULUS := Modulus();
    var reduced, borrow := sub_value(a, MODULUS);
    var out := U256_Zero();

    // GHOST CODE
    assert fresh(out.limbs);

    // original code:
    // for j in 0 .. U256::LIMBS {
    //   out.as_limbs_mut()[j] = select_word(reduced.as_limbs()[j], a.as_limbs()[j], borrow);
    // }
    for j:int := 0 to U256_LIMBS
      invariant 0 <= j <= U256_LIMBS
      invariant a.Valid()
      invariant reduced.Valid()
      invariant out.Valid()
      invariant out.limbs[..j] == if borrow == ZeroLimb()
          then reduced.limbs[..j]
          else a.limbs[..j]
      invariant fresh(out.limbs)
      modifies out.limbs
    {
      // original code:
      // out.as_limbs_mut()[j] = select_word(reduced.as_limbs()[j], a.as_limbs()[j], borrow);
      var a_as_limbs := a.as_limbs();
      var reduced_as_limbs := reduced.as_limbs();
      var out_as_limbs_mut := out.as_limbs_mut();
      out_as_limbs_mut[j] := select_word(reduced_as_limbs[j], a_as_limbs[j], borrow);
    }

    // original code:
    // out
    ret := out;

    // LEMMAS
    ghost var MODULUS_int := ModulusValueSpec();
    ghost var a_int := a.ValueSpec();
    ghost var reduced_int := reduced.ValueSpec();
    ghost var ret_int := LimbsValueSpec(ret.limbs[..]);
    if borrow == ZeroLimb() {
      assert reduced_int == a_int - MODULUS_int;
      assert reduced_int < MODULUS_int;
      assert ret.limbs[..] == reduced.limbs[..];
      assert ret_int == a_int - MODULUS_int;
    }
    else {
      assert 0 <= a_int < MODULUS_int;
      assert ret.limbs[..] == a.limbs[..];
      assert ret_int == a_int;
    }
    assert 0 <= ret_int < MODULUS_int;
    assert ret_int == a_int || ret_int == a_int - MODULUS_int ;
    Modular.Red1Lemma(ret_int, a_int, MODULUS_int);
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L120-L141
  // NOTE: Rust takes `mut a: U256` by value; Dafny takes class reference with `modifies a.limbs`.
  method {:fuel LimbsSumSpec,5} {:isolate_assertions} {:rlimit 105000} red256(a: U256) returns (out: HelioseleneField)
    requires a.Valid()
    modifies a.limbs
    ensures ValidField(out)
    ensures out.inner.ValueSpec() == a.ValueSpec() % ModulusValueSpec()
    ensures out.inner.ValueSpec() == old(a.ValueSpec()) % ModulusValueSpec()
    ensures out.inner.ValueSpec() < ModulusValueSpec()
    ensures fresh(out.inner) && fresh(out.inner.limbs)
  {
    // Ghost code
    ghost var input_limbs := a.limbs[..];
    ghost var input_int := a.ValueSpec();

    // original code:
    // // If the highest bit is set, we clear it and add the distance to the modulus
    // let high_bit = (a.as_limbs()[U256::LIMBS - 1] >> (Limb::BITS - 1)).wrapping_neg();
    var a_as_limbs := a.as_limbs();
    var msb_bit := LimbShr(a_as_limbs[U256_LIMBS - 1], WORD_BITS - 1);
    var high_bit := wrapping_neg(msb_bit);

    // Lemmas
    ghost var TWO_POW_255 := MathHelpers.pow2(255);
    MathHelpers.Pow2DoubleLemma(63);
    MathHelpers.Pow2To64Lemma();
    assert MathHelpers.pow2(63) == WORD_MODULUS / 2;
    assert LimbToInt(msb_bit) == LimbToInt(a_as_limbs[U256_LIMBS - 1]) / (WORD_MODULUS / 2);
    assert 0 <= LimbToInt(msb_bit) < 2;
    if LimbToInt(msb_bit) == 0 {
      assert msb_bit == ZeroLimb();
    } else {
      assert LimbToInt(msb_bit) == 1;
      assert msb_bit == LimbFromInt(1);
    }
    WrappingNegOfBitLemma(msb_bit, high_bit);
    assert high_bit == ZeroLimb() || high_bit == MaxLimb();
    Pow256EqWordModulus4Lemma();
    MathHelpers.Pow2DoubleLemma(255);
    assert WORD_MODULUS4 == 2 * TWO_POW_255;
    assert WORD_MODULUS4 / 2 == TWO_POW_255;
    U256MostSignificantBitLemma(a);
    assert msb_bit == ZeroLimb() ==> LimbToInt(a_as_limbs[U256_LIMBS - 1]) < WORD_MODULUS / 2;
    assert msb_bit == LimbFromInt(1) ==> LimbToInt(a_as_limbs[U256_LIMBS - 1]) >= WORD_MODULUS / 2;
    assert high_bit == ZeroLimb() ==> input_int < TWO_POW_255;
    assert high_bit != ZeroLimb() ==> input_int >= TWO_POW_255;
    assert {:split_here} true;

    // original code:
    // a.as_limbs_mut()[U256::LIMBS - 1] = a.as_limbs()[U256::LIMBS - 1] & (Limb::MAX >> 1);
    var a_as_limbs_mut := a.as_limbs_mut();
    a_as_limbs_mut[U256_LIMBS - 1] := LimbAnd(a_as_limbs[U256_LIMBS - 1], LimbShr(MaxLimb(), 1));

    // Lemmas
    assert LimbToInt(a_as_limbs_mut[U256_LIMBS - 1]) == LimbToInt(input_limbs[U256_LIMBS - 1]) % (WORD_MODULUS/2);
    LimbsValueSpecLastLimbLemma(input_limbs);
    LimbsValueSpecLastLimbLemma(a.limbs[..]);
    assert input_int == LimbsValueSpec(input_limbs[..3]) + LimbToInt(input_limbs[3]) * WORD_MODULUS3;
    assert a.ValueSpec() == LimbsValueSpec(a.limbs[..3]) + LimbToInt(a.limbs[3]) * WORD_MODULUS3;
    assert a.limbs[..3] == input_limbs[..3];
    assert WORD_MODULUS4 / 2 == (WORD_MODULUS / 2) * WORD_MODULUS3;
    if high_bit == ZeroLimb() {
      assert LimbToInt(input_limbs[3]) < WORD_MODULUS / 2;
      assert LimbToInt(a_as_limbs_mut[U256_LIMBS - 1]) == LimbToInt(input_limbs[U256_LIMBS - 1]);
      assert a.ValueSpec() == input_int;
      assert input_int < WORD_MODULUS4 / 2;
    } else {
      assert high_bit == MaxLimb();
      assert msb_bit == LimbFromInt(1);
      assert LimbToInt(input_limbs[3]) >= WORD_MODULUS / 2;
      assert LimbToInt(a_as_limbs_mut[U256_LIMBS - 1]) == LimbToInt(input_limbs[U256_LIMBS - 1]) - WORD_MODULUS / 2;
      assert a.ValueSpec() == input_int - WORD_MODULUS4 / 2;
      assert WORD_MODULUS4 / 2 <= input_int < WORD_MODULUS4;
      assert input_int % (WORD_MODULUS4 / 2) == input_int - WORD_MODULUS4 / 2;
    }
    assert a.ValueSpec() == input_int % (WORD_MODULUS4 / 2);
    ghost var a_mod_255_limbs: seq<Limb> := a.limbs[..];
    assert a.limbs[..U128_LIMBS] == input_limbs[..U128_LIMBS];
    assert {:split_here} true;

    // original code:
    // let mut carry = Limb::ZERO;
    var carry := ZeroLimb();

    // original code:
    // for j in 0 .. U128::LIMBS {
    //   (a.as_limbs_mut()[j], carry) = add_with_bounded_overflow(
    //     a.as_limbs()[j],
    //     high_bit & MODULUS_255_DISTANCE.as_limbs()[j],
    //     carry,
    //   );
    // }
    var MODULUS_255_DISTANCE := Modulus255Distance();
    ghost var partialLow := LimbsSumSpec(a_mod_255_limbs[..0], MODULUS_255_DISTANCE.limbs[..0], ZeroLimb());
    for j := 0 to U128_LIMBS
      invariant 0 <= j <= U128_LIMBS
      modifies a.limbs
      invariant carry == ZeroLimb() || carry == LimbFromInt(1)
      invariant high_bit == ZeroLimb() ==> carry == ZeroLimb()
      invariant high_bit == ZeroLimb() ==> a.limbs[..j] == input_limbs[..j]
      invariant a.limbs[j..] == a_mod_255_limbs[j..]
      invariant high_bit != ZeroLimb() ==> partialLow == LimbsSumSpec(a_mod_255_limbs[..j], MODULUS_255_DISTANCE.limbs[..j], ZeroLimb())
      invariant {:isolate} high_bit != ZeroLimb() ==> a.limbs[..j] == partialLow[..j]
      invariant high_bit != ZeroLimb() ==> carry == partialLow[j]
    {
      // Ported implementation:
      var a_as_limbs_mut := a.as_limbs_mut();
      var MODULUS_255_DISTANCE_as_limbs := MODULUS_255_DISTANCE.as_limbs();

      // Ghost code
      ghost var carryBefore := carry;
      ghost var rhsToAdd := LimbAnd(high_bit, MODULUS_255_DISTANCE_as_limbs[j]);
      ghost var limbsPrefix := a.limbs[..j];
      ghost var lhsBefore := a.limbs[j];
      assert a.limbs[j..] == a_mod_255_limbs[j..];
      assert lhsBefore == a.limbs[j..][0];
      assert a_mod_255_limbs[j] == a_mod_255_limbs[j..][0];
      assert lhsBefore == a_mod_255_limbs[j];

      // Ported implementation:
      a_as_limbs_mut[j], carry := add_with_bounded_overflow(
        a_as_limbs[j],
        LimbAnd(high_bit, MODULUS_255_DISTANCE_as_limbs[j]),
        carry
      );

      // Ghost code
      ghost var nextPartial := limbsPrefix + [a_as_limbs_mut[j], carry];
      if high_bit == ZeroLimb() {
        assert rhsToAdd == ZeroLimb();
        assert carryBefore == ZeroLimb();
        assert a_mod_255_limbs[j] == input_limbs[j];
        assert lhsBefore == input_limbs[j];
        assert a_as_limbs_mut[j] == lhsBefore;
        assert carry == ZeroLimb();
        assert a.limbs[..j + 1] == input_limbs[..j + 1];
      } else {
        assert high_bit == MaxLimb();
        assert rhsToAdd == MODULUS_255_DISTANCE_as_limbs[j];
        assert (a_as_limbs_mut[j], carry) == AddAndCarryLimbSpec(
          lhsBefore,
          MODULUS_255_DISTANCE_as_limbs[j],
          carryBefore);
        assert partialLow == limbsPrefix + [carryBefore];
        LimbsSumStepLemma(
          a_mod_255_limbs[..j],
          MODULUS_255_DISTANCE.limbs[..j],
          ZeroLimb(),
          a_mod_255_limbs[j],
          MODULUS_255_DISTANCE_as_limbs[j],
          limbsPrefix,
          carryBefore,
          a_as_limbs_mut[j],
          carry);
      }
      partialLow := nextPartial;
    }

    // GHOST CODE
    var MODULUS_255_DISTANCE_extended : seq<Limb> := [
      MODULUS_255_DISTANCE.limbs[0],
      MODULUS_255_DISTANCE.limbs[1],
      ZeroLimb(),
      ZeroLimb()
    ];
    assert {:split_here} true;
    ghost var partialExtended := partialLow;
    assert MODULUS_255_DISTANCE_extended[..U128_LIMBS] == MODULUS_255_DISTANCE.limbs[..];
    assert {:split_here} true;
    assert {:isolate} high_bit != ZeroLimb() ==> partialExtended == LimbsSumSpec(
      a_mod_255_limbs[..U128_LIMBS],
      MODULUS_255_DISTANCE_extended[..U128_LIMBS],
      ZeroLimb());
    assert {:isolate} high_bit != ZeroLimb() ==> a.limbs[..U128_LIMBS] == partialExtended[..U128_LIMBS];
    assert {:isolate} high_bit != ZeroLimb() ==> carry == partialExtended[U128_LIMBS];
    assert {:split_here} true;

    // original code:
    // for j in U128::LIMBS .. U256::LIMBS {
    //   let (limb, carry_bool) = a.as_limbs()[j].0.overflowing_add(carry.0);
    //   (a.as_limbs_mut()[j], carry) = (Limb(limb), Limb(Word::from(carry_bool)));
    // }
    for j := U128_LIMBS to U256_LIMBS
      invariant U128_LIMBS <= j <= U256_LIMBS
      modifies a.limbs
      invariant a.limbs[j..] == a_mod_255_limbs[j..]
      invariant high_bit == ZeroLimb() ==> carry == ZeroLimb()
      invariant high_bit == ZeroLimb() ==> a.limbs[..j] == input_limbs[..j]
      invariant high_bit != ZeroLimb() ==> partialExtended == LimbsSumSpec(a_mod_255_limbs[..j], MODULUS_255_DISTANCE_extended[..j], ZeroLimb())
      invariant {:isolate} high_bit != ZeroLimb() ==> a.limbs[..j] == partialExtended[..j]
      invariant high_bit != ZeroLimb() ==> carry == partialExtended[j]
    {
      // Ported implementation:
      var a_as_limbs := a.as_limbs();
      var limb_and_carry_bool := overflowing_add(a_as_limbs[j].word, carry.word);
      var limb := limb_and_carry_bool.0;
      var carry_bool := limb_and_carry_bool.1;

      // Ghost code
      ghost var limbsPrefix := a.limbs[..j];
      ghost var nextPartial := limbsPrefix + [Limb(limb), Limb(WordFromBool(carry_bool))];

      // Ported implementation:
      var a_as_limbs_mut := a.as_limbs_mut();
      a_as_limbs_mut[j] := Limb(limb);
      carry := Limb(WordFromBool(carry_bool));

      // Ghost code
      if high_bit == ZeroLimb() {
        assert limb == a_as_limbs[j].word;
        assert carry_bool == false;
      } else {
        ghost var sumAndCarry := AddAndCarryLimbSpec(a_mod_255_limbs[j], MODULUS_255_DISTANCE_extended[j], partialExtended[j]);
        assert MODULUS_255_DISTANCE_extended[j] == ZeroLimb();
        OverflowingAddZeroCarryLemma(
          a_mod_255_limbs[j],
          partialExtended[j],
          limb_and_carry_bool.0,
          limb_and_carry_bool.1);
        assert Limb(limb) == sumAndCarry.0;
        assert Limb(WordFromBool(carry_bool)) == sumAndCarry.1;
        LimbsSumStepLemma(
          a_mod_255_limbs[..j],
          MODULUS_255_DISTANCE_extended[..j],
          ZeroLimb(),
          a_mod_255_limbs[j],
          MODULUS_255_DISTANCE_extended[j],
          limbsPrefix,
          partialExtended[j],
          Limb(limb),
          Limb(WordFromBool(carry_bool)));
      }
      partialExtended := nextPartial;
    }

    // LEMMAS
    ghost var a_int := a.ValueSpec();
    if high_bit == ZeroLimb() {
      assert a.limbs[..] == input_limbs[..];
      assert a_int < TWO_POW_255;
      ModulusUpperBoundLemma();
      assert a_int < WORD_MODULUS4 / 2 + WORD_MODULUS3 + WORD_MODULUS2 + WORD_MODULUS;
      assert a_int < 2 * ModulusValueSpec();
      assert a_int == input_int;
    }
    else {
      assert {:split_here} true;
      ghost var fullSum := partialExtended;
      ghost var carryVal := LimbToInt(carry);
      assert 0 <= carryVal <= 1;
      assert carry == fullSum[4];
      assert a.limbs[..] == fullSum[..4];
      assert a_int == LimbsValueSpec(a.limbs[..]);
      WrappingAddLemma(fullSum, carryVal);
      assert LimbsValueSpec(MODULUS_255_DISTANCE_extended[..]) == Modulus255DistanceSpec();
      assert {:isolate} LimbsValueSpec(fullSum)
        == LimbsValueSpec(a_mod_255_limbs[..]) + LimbsValueSpec(MODULUS_255_DISTANCE_extended[..]);
      FromReprModulusRelationLemma();
      assert Modulus255DistanceSpec() < WORD_MODULUS4 / 2;
      assert LimbsValueSpec(a_mod_255_limbs[..]) < WORD_MODULUS4 / 2;
      assert LimbsValueSpec(fullSum) < WORD_MODULUS4;
      assert carryVal == 0;
      assert {:isolate} a_int == LimbsValueSpec(a_mod_255_limbs[..]) + Modulus255DistanceSpec();
      Modulus255DistanceLemma(input_int, a_int);
      assert a_int < 2 * ModulusValueSpec();
      assert a_int % ModulusValueSpec() == input_int % ModulusValueSpec();
    }

    // original code:
    // HelioseleneField(red1(a))
    var reduced := red1(a);
    out := HelioseleneField(reduced);

    // LEMMAS
    assert reduced.ValueSpec() == input_int % ModulusValueSpec();
  }

  lemma OverflowingAddZeroCarryLemma(a: Limb, carry: Limb, limb: Word, carryBool: bool)
    requires carry == ZeroLimb() || carry == LimbFromInt(1)
    requires (limb, carryBool) == overflowing_add(a.word, carry.word)
    ensures Limb(limb) == AddAndCarryLimbSpec(a, ZeroLimb(), carry).0
    ensures Limb(WordFromBool(carryBool)) == AddAndCarryLimbSpec(a, ZeroLimb(), carry).1
  {
  }

}
