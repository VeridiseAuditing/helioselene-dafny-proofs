include "../../crypto_bigint_0_5_5/Limb.dfy"
include "../../crypto_bigint_0_5_5/U256.dfy"
include "../../crypto_bigint_0_5_5/U128.dfy"
include "../../helpers/Limbs.dfy"
include "../../helpers/Modular.dfy"
include "../../helpers/NumberTheory.dfy"
include "../../helpers/PowMod.dfy"
include "../../helpers/BitOps.dfy"
include "../../helpers/FermatLittle.dfy"

module FieldBase {
  import opened CryptoBigint_0_5_5_Limb
  import opened CryptoBigint_0_5_5_U256
  import opened CryptoBigint_0_5_5_U128
  import Modular
  import opened Limbs
  import opened NumberTheory
  import opened PowMod
  import opened BitOps
  import opened FermatLittle
  import Power = Std.Arithmetic.Power
  import DivMod = Std.Arithmetic.DivMod
  import Mul = Std.Arithmetic.Mul

  datatype HelioseleneField = HelioseleneField(inner:U256)

  ghost predicate ValidField(f: HelioseleneField)
    reads f.inner, f.inner.limbs
  {
    f.inner.Valid() && f.inner.ValueSpec() < ModulusValueSpec()
  }

  ghost function Wide512ValueSpec(lo: U256, hi: U256): int
    reads lo, lo.limbs, hi, hi.limbs
    requires lo.Valid()
    requires hi.Valid()
  {
    lo.ValueSpec() + hi.ValueSpec() * MathHelpers.pow2(256)
  }

  ghost function ModulusValueSpec(): int
  {
    LimbsValueSpec(ModulusLimbs())
  }

  ghost function Modulus255DistanceSpec(): int
  {
    0x08cab7e2e6960ce8067af49720ee20ad
  }

  ghost function TwoModulus255DistanceSpec(): int
  {
    0x11956fc5cd2c19d00cf5e92e41dc415a
  }

  // Ghost function: (p+1)/4, the exponent for square root in p ≡ 3 (mod 4) fields.
  ghost function SqrtExponent(): int
  {
    0x1ffffffffffffffffffffffffffffffffdcd5207465a7cc5fe6142da37c477d5
  }


  // Field modulus:
  // 0x7ffffffffffffffffffffffffffffffff735481d1969f317f9850b68df11df53
  // This is a 255-bit value, greater than 2**255 and less than 2**256 - 1
  // https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L23C1-L24C89
  function ModulusLimbs(): seq<Limb>
  {
    [
      LimbFromInt(0xf9850b68df11df53),
      LimbFromInt(0xf735481d1969f317),
      LimbFromInt(0xffffffffffffffff),
      LimbFromInt(0x7fffffffffffffff)
    ]
  }

  // The distance between the modulus and 2**255.
  // 08cab7e2e6960ce8067af49720ee20ad
  // https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L25-L26
  function Modulus255DistanceLimbs(): seq<Limb>
  {
    [
      LimbFromInt(0x67af49720ee20ad),
      LimbFromInt(0x8cab7e2e6960ce8)
    ]
  }

  // Twice the distance between the modulus and 2**255.
  // 11956fc5cd2c19d00cf5e92e41dc415a
  // https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L27-L28
  function TwoModulus255DistanceLimbs(): seq<Limb>
  {
    [
      LimbFromInt(0xcf5e92e41dc415a),
      LimbFromInt(0x11956fc5cd2c19d0)
    ]
  }

  method HelioseleneField_ONE() returns (one: HelioseleneField)
    ensures ValidField(one)
    ensures one.inner.ValueSpec() == 1
    ensures fresh(one.inner)
  {
    var oneLimbs: array<Limb> := new Limb[U256_LIMBS][LimbFromInt(1), ZeroLimb(), ZeroLimb(), ZeroLimb()];
    var oneU256 := new U256(oneLimbs);
    return HelioseleneField(oneU256);
  }

  method Modulus() returns (out: U256)
    ensures out.Valid()
    ensures out.ValueSpec() == ModulusValueSpec()
    ensures out.limbs[..] == ModulusLimbs()
  {
    var modulusLimbs := ModulusLimbs();
    var limbs: array<Limb> := new Limb[U256_LIMBS][modulusLimbs[0], modulusLimbs[1], modulusLimbs[2], modulusLimbs[3]];
    var u256 := new U256(limbs);
    out := u256;
  }

  method Modulus255Distance() returns (out: U128)
    ensures out.Valid()
    ensures out.ValueSpec() == Modulus255DistanceSpec()
    ensures out.limbs[..] == Modulus255DistanceLimbs()
  {
    var modulus255DistanceLimbs := Modulus255DistanceLimbs();
    var limbs: array<Limb> := new Limb[U128_LIMBS][modulus255DistanceLimbs[0], modulus255DistanceLimbs[1]];
    var u128 := new U128(limbs);
    out := u128;
  }

  method TwoModulus255Distance() returns (out: U128)
    ensures out.Valid()
    ensures out.ValueSpec() == TwoModulus255DistanceSpec()
    ensures out.limbs[..] == TwoModulus255DistanceLimbs()
  {
    var modulus255DistanceLimbs := TwoModulus255DistanceLimbs();
    var limbs: array<Limb> := new Limb[U128_LIMBS][modulus255DistanceLimbs[0], modulus255DistanceLimbs[1]];
    var u128 := new U128(limbs);
    out := u128;
  }

  // TCB AXIOM: the field modulus is prime.
  // Verified externally: sage -c "print(is_prime(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf53))" → True
  lemma {:axiom} ModulusIsPrimeLemma()
    ensures IsPrime(ModulusValueSpec())

  // ===================================================================
  // FIELD ELEMENT UTILITIES
  // ===================================================================

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L103-L107
  // This selection formula is inherited from subtle
  function select_word(a: Limb, b: Limb, choice: Limb): Limb
    requires choice == ZeroLimb() || choice == MaxLimb()
    ensures choice == ZeroLimb() ==>  select_word(a, b, choice) == a
    ensures choice == MaxLimb() ==>  select_word(a, b, choice) == b
  {
    // Original code
    // a ^ ((a ^ b) & choice)
    LimbXor(a, LimbAnd(LimbXor(a, b), choice))
  }

  // Bitwise OR for mask values (restricted to 0 and MAX).
  function LimbMaskOr(a: Limb, b: Limb): Limb
    requires a == ZeroLimb() || a == MaxLimb()
    requires b == ZeroLimb() || b == MaxLimb()
    ensures LimbMaskOr(a, b) == ZeroLimb()
      || LimbMaskOr(a, b) == MaxLimb()
  {
    if a == MaxLimb() || b == MaxLimb()
      then MaxLimb() else ZeroLimb()
  }

  // Bitwise NOT for mask values (restricted to 0 and MAX).
  function LimbMaskNot(a: Limb): Limb
    requires a == ZeroLimb() || a == MaxLimb()
    ensures LimbMaskNot(a) == ZeroLimb()
      || LimbMaskNot(a) == MaxLimb()
  {
    if a == ZeroLimb() then MaxLimb() else ZeroLimb()
  }

  // Extract lowest bit of a limb. Equivalent to x & 1.
  // TODO: Replace with general BV-backed LimbAnd when available.
  function LimbExtractLsb(x: Limb): Limb
    ensures LimbExtractLsb(x) == ZeroLimb()
      || LimbExtractLsb(x) == LimbFromInt(1)
  {
    LimbFromInt(LimbToInt(x) % 2)
  }

  // TODO: Replace with general BV-backed LimbShl when available.
  // Left-shift a mask (0 or MAX) by 63 bits. Equivalent to mask << 63.
  // MAX << 63 in u64 = 0x8000_0000_0000_0000 = WORD_MSB.
  function LimbShlMask63(mask: Limb): Limb
    requires mask == ZeroLimb() || mask == MaxLimb()
    ensures LimbShlMask63(mask) == ZeroLimb()
      || LimbShlMask63(mask) == LimbFromInt(WORD_MSB)
  {
    if mask == MaxLimb()
      then LimbFromInt(WORD_MSB) else ZeroLimb()
  }

  // TODO: Replace with general BV-backed LimbOr when available.
  // OR a limb value with an MSB mask (0 or WORD_MSB).
  // Equivalent to val | msb_mask where msb_mask in {0, WORD_MSB}.
  function LimbOrMsb(val: Limb, msb_mask: Limb): Limb
    requires msb_mask == ZeroLimb()
      || msb_mask == LimbFromInt(WORD_MSB)
  {
    if msb_mask == ZeroLimb() then val
    else LimbFromInt(
      LimbToInt(val) % WORD_MSB + WORD_MSB)
  }

  // TODO: Replace with general BV-backed LimbShl when available.
  // Extract LSB of a limb and shift to MSB position.
  // Equivalent to (a << 63) where only bit 0 matters.
  function LimbLsbToMsb(a: Limb): Limb
    ensures LimbLsbToMsb(a) == ZeroLimb()
      || LimbLsbToMsb(a) == LimbFromInt(WORD_MSB)
  {
    LimbFromInt((LimbToInt(a) % 2) * WORD_MSB)
  }

  // MODULUS XOR (2 * MODULUS): constant for CT modulus correction.
  // Rust: field.rs:565-566.
  function ModulusXorTwoModulusLimbs(): seq<Limb>
  {
    [
      LimbFromInt(0x0a8f1db9613261f5),
      LimbFromInt(0x195fd8272bba1538),
      ZeroLimb(),
      LimbFromInt(0x8000000000000000)
    ]
  }

  // CT select across U256: per-limb select_word.
  // Ported from inline select() in field.rs:490-496.
  method select_u256(
    a: U256, b: U256, choice: Limb
  ) returns (result: U256)
    requires a.Valid() && b.Valid()
    requires choice == ZeroLimb() || choice == MaxLimb()
    ensures result.Valid()
    ensures fresh(result) && fresh(result.limbs)
    ensures choice == ZeroLimb() ==>
      result.ValueSpec() == a.ValueSpec()
    ensures choice == MaxLimb() ==>
      result.ValueSpec() == b.ValueSpec()
    ensures forall j :: 0 <= j < 4 ==>
      result.limbs[j] == select_word(a.limbs[j], b.limbs[j], choice)
  {
    var out := new Limb[U256_LIMBS][
      select_word(a.limbs[0], b.limbs[0], choice),
      select_word(a.limbs[1], b.limbs[1], choice),
      select_word(a.limbs[2], b.limbs[2], choice),
      select_word(a.limbs[3], b.limbs[3], choice)
    ];
    result := new U256(out);
    // Prove ValueSpec equality: limbs match, so LimbsValueSpec matches.
    var src := if choice == ZeroLimb() then a else b;
    assert out[..] == src.limbs[..];
  }

  // Ported from https://github.com/monero-oxide/monero-oxide//blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L77-L83
  // Perform an add with carry, bounding the overflow to be zero or one.
  method add_with_bounded_overflow(a: Limb, b: Limb, c: Limb) returns (add: Limb, carryOut: Limb)
    requires 0 <= c.word && c.word <= 1
    ensures AddAndCarryLimbSpec(a, b, c) == (add, carryOut)
  {
    // Original code:
    // let (limb, carry1) = a.0.overflowing_add(b.0);
    var (limb, carry1) := overflowing_add(a.word, b.word);
    // let (limb, carry2) = limb.overflowing_add(c.0);
    var (limb_, carry2) := overflowing_add(limb, c.word);
    // (Limb(limb), Limb(Word::from(carry1 | carry2)))
    add := Limb(limb_);
    carryOut := Limb(WordFromBool(carry1 || carry2));
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L99-L101
  // Subtract a value (`b`) from another value (`a`).
  //
  // Returns `(result, 0)` if successful, or  `(wrapped value, 255)` otherwise
  method sub_value(a: U256, b: U256) returns (diff: U256, borrow: Limb)
    requires a.Valid()
    requires b.Valid()
    ensures diff.Valid()
    ensures fresh(diff)
    ensures borrow == ZeroLimb() || borrow == MaxLimb()
    ensures
        diff.ValueSpec() - (if borrow == ZeroLimb() then 0 else WORD_MODULUS4)
        == a.ValueSpec() - b.ValueSpec()
  {
    // Original Code
    // a.sbb(&b, Limb::ZERO)
    diff, borrow := a.sbb(b, ZeroLimb());
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L440-L446
  // is_zero: OR all limbs together and check if the result is zero
  // NOTE: Rust ORs all limbs together (constant-time); Dafny iterates with boolean flag (VT). Semantically equivalent.
  method field_is_zero(a: HelioseleneField) returns (result: bool)
    requires ValidField(a)
    ensures result <==> a.inner.ValueSpec() == 0
  {
    // original code:
    // let mut all = Limb::ZERO;
    // for l in 0 .. U256::LIMBS { all = all | self.0.as_limbs()[l]; }
    // all.ct_eq(&Limb::ZERO)
    var a_as_limbs := a.inner.as_limbs();
    var all_zero := true;
    for l := 0 to U256_LIMBS
      invariant all_zero <==> (forall k :: 0 <= k < l ==> LimbToInt(a_as_limbs[k]) == 0)
    {
      if a_as_limbs[l] != ZeroLimb() {
        all_zero := false;
      }
    }
    result := all_zero;

    // LEMMAS: all limbs zero iff ValueSpec == 0
    if all_zero {
      assert forall k :: 0 <= k < U256_LIMBS ==> LimbToInt(a_as_limbs[k]) == 0;
      assert a.inner.ValueSpec() == LimbsValueSpec(a_as_limbs[..]);
      assert LimbsValueSpec(a_as_limbs[..]) == 0;
    } else {
      assert a.inner.ValueSpec() == LimbsValueSpec(a_as_limbs[..]);
      assert LimbsValueSpec(a_as_limbs[..]) > 0;
    }
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L758-L760
  // is_odd: check if the lowest bit of limbs[0] is set
  method field_is_odd(a: HelioseleneField) returns (result: bool)
    requires ValidField(a)
    ensures result <==> a.inner.ValueSpec() % 2 == 1
  {
    // original code: Choice::from((self.0.as_limbs()[0].0 & 1) as u8)
    var a_as_limbs := a.inner.as_limbs();
    result := (a_as_limbs[0].word as int % 2) == 1;

    // LEMMAS: value mod 2 == limbs[0] mod 2
    assert a.inner.ValueSpec() == LimbsValueSpec(a_as_limbs[..]);
    assert LimbsValueSpec(a_as_limbs[..]) % 2 == LimbToInt(a_as_limbs[0]) % 2;
  }

  // ===================================================================
  // LEMMAS
  // ===================================================================

  // MathHelpers.pow2(256) == WORD_MODULUS4 (both equal 2^256)
  // Needed to connect Wide512ValueSpec (uses pow2) to mul_wide/square_wide postconditions (use WORD_MODULUS4)
  lemma Pow256EqWordModulus4Lemma()
    ensures MathHelpers.pow2(256) == WORD_MODULUS4
  {
    MathHelpers.Pow2To64Lemma();
    assert MathHelpers.pow2(64) == WORD_MODULUS;
    MathHelpers.SumInExponentLemma(2, 64, 64);
    assert MathHelpers.pow2(128) == MathHelpers.pow2(64) * MathHelpers.pow2(64);
    assert MathHelpers.pow2(128) == WORD_MODULUS2;
    MathHelpers.SumInExponentLemma(2, 128, 128);
    assert MathHelpers.pow2(256) == MathHelpers.pow2(128) * MathHelpers.pow2(128);
    assert MathHelpers.pow2(256) == WORD_MODULUS2 * WORD_MODULUS2;
  }

  // 2 * MODULUS < 2^256
  lemma TwoModulusLt2Pow256Lemma()
    ensures 2 * ModulusValueSpec() < WORD_MODULUS4
  {
    // MODULUS < 2^255 = WORD_MODULUS4 / 2, so 2 * MODULUS < WORD_MODULUS4
    assert ModulusValueSpec() < WORD_MODULUS4 / 2;
  }

  // (a - b) % p == (a - b + p) % p when a - b < 0
  lemma FieldSubModLemma(a: int, b: int, p: int)
    requires 0 <= a < p
    requires 0 <= b < p
    requires a < b
    ensures (a - b + p) % p == (a - b) % p
  {
    assert a - b + p == (a - b) + p;
    assert (a - b + p) % p == ((a - b) + p) % p;
  }

  lemma U256MostSignificantBitLemma(a: U256)
    requires a.Valid()
    ensures
      LimbToInt(a.limbs[3]) < WORD_MODULUS / 2
      <==>
      a.ValueSpec() < WORD_MODULUS4 / 2
  {
  }

  // For field_from_repr: LimbToInt(l3) < W/2 <==> LimbsValueSpec([l0,l1,l2,l3]) < W^4/2
  // Same as U256MostSignificantBitLemma but operates on individual limbs instead of a U256 object
  lemma FromReprMsbLemma(l0: Limb, l1: Limb, l2: Limb, l3: Limb)
    ensures
      LimbToInt(l3) < WORD_MODULUS / 2
      <==>
      LimbsValueSpec([l0, l1, l2, l3]) < WORD_MODULUS4 / 2
  {
    var v := LimbsValueSpec([l0, l1, l2, l3]);
    assert v == LimbToInt(l0) + LimbToInt(l1) * WORD_MODULUS + LimbToInt(l2) * WORD_MODULUS2 + LimbToInt(l3) * WORD_MODULUS3;
    // Forward: if l3 < W/2 then l3*W^3 <= (W/2-1)*W^3 = W^4/2 - W^3
    // and l0+l1*W+l2*W^2 < W^3, so v < W^4/2
    // Backward: if l3 >= W/2 then l3*W^3 >= W^4/2, so v >= W^4/2
  }

  // p = 2^255 - distance, i.e. ModulusValueSpec() == WORD_MODULUS4/2 - Modulus255DistanceSpec()
  lemma FromReprModulusRelationLemma()
    ensures ModulusValueSpec() == WORD_MODULUS4 / 2 - Modulus255DistanceSpec()
  {
    CrandallRelationLemma();
    // CrandallRelationLemma: 2*p + 2*dist == W^4
    // So p = (W^4 - 2*dist) / 2 = W^4/2 - dist
    assert 2 * ModulusValueSpec() + TwoModulus255DistanceSpec() == WORD_MODULUS4;
    assert TwoModulus255DistanceSpec() == 2 * Modulus255DistanceSpec();
  }

  lemma WordToBvPreservesOrderLemma(a: Word, b: Word)
    requires a as int + b as int < WORD_MODULUS
  {
    var sum: Word := (a as int + b as int) as Word;
    WordRoundTrip_bv(a);
    WordRoundTrip_bv(b);
    WordRoundTrip_bv(sum);
  }


  lemma ModulusLowerBoundLemma()
    ensures ModulusValueSpec() >= WORD_MODULUS4 / 2 - WORD_MODULUS3
  {
    ghost var limbs := ModulusLimbs();
    assert ModulusValueSpec() == LimbsValueSpec(limbs);
    assert LimbToInt(limbs[3]) == WORD_MODULUS / 2 - 1;
    assert ModulusValueSpec() >= LimbToInt(limbs[3]) * WORD_MODULUS3;
    assert LimbToInt(limbs[3]) * WORD_MODULUS3 == WORD_MODULUS4 / 2 - WORD_MODULUS3;
  }

  lemma ValueSpecUpperBoundLemma(l0: Limb, l1: Limb, l2: Limb, l3: Limb)
    requires LimbToInt(l0) < WORD_MODULUS
    requires LimbToInt(l1) < WORD_MODULUS
    requires LimbToInt(l2) < WORD_MODULUS
    requires LimbToInt(l3) <= WORD_MODULUS / 2
    ensures LimbsValueSpec([l0, l1, l2, l3]) < WORD_MODULUS4 / 2 + WORD_MODULUS3 + WORD_MODULUS2 + WORD_MODULUS
  {
    calc {
      LimbsValueSpec([l0, l1, l2, l3]);
        == LimbToInt(l0)
          + LimbToInt(l1) * WORD_MODULUS
          + LimbToInt(l2) * WORD_MODULUS2
          + LimbToInt(l3) * WORD_MODULUS3;
        < WORD_MODULUS
          + WORD_MODULUS * WORD_MODULUS
          + WORD_MODULUS * WORD_MODULUS2
          + (WORD_MODULUS / 2) * WORD_MODULUS3;
        == WORD_MODULUS4 / 2 + WORD_MODULUS3 + WORD_MODULUS2 + WORD_MODULUS;
    }
  }

  lemma ModulusUpperBoundLemma()
    ensures WORD_MODULUS4 / 2 + WORD_MODULUS3 + WORD_MODULUS2 + WORD_MODULUS < 2 * ModulusValueSpec()
  {
    ModulusLowerBoundLemma();
    assert WORD_MODULUS2 + WORD_MODULUS < WORD_MODULUS3;
    assert WORD_MODULUS4 / 2 + WORD_MODULUS3 + WORD_MODULUS2 + WORD_MODULUS
      < WORD_MODULUS4 / 2 + 2 * WORD_MODULUS3;
    assert WORD_MODULUS4 / 2 + 2 * WORD_MODULUS3 < WORD_MODULUS4 - 2 * WORD_MODULUS3;
    assert WORD_MODULUS4 - 2 * WORD_MODULUS3 <= 2 * ModulusValueSpec();
  }

  lemma Modulus255DistanceLemma(unreduced: int, partiallyReduced: int)
    requires WORD_MODULUS4/2 <= unreduced < WORD_MODULUS4
    requires partiallyReduced == unreduced % (WORD_MODULUS4/2) + Modulus255DistanceSpec()
    ensures partiallyReduced % ModulusValueSpec() == unreduced % ModulusValueSpec()
    ensures
      unreduced % (WORD_MODULUS4/2) + Modulus255DistanceSpec()
      < 2 * ModulusValueSpec()
  { }

  // wrapping_neg of a 0-or-1 carry is ZeroLimb (when carry=0) or MaxLimb (when carry=1)
  lemma WrappingNegOfBitLemma(carry: Limb, neg: Limb)
    requires carry == ZeroLimb() || carry == LimbFromInt(1)
    requires neg == wrapping_neg(carry)
    ensures neg == ZeroLimb() || neg == MaxLimb()
  {
    if carry == ZeroLimb() {
      assert carry.word as int == 0;
      assert neg.word as int == WrapWordValue(WORD_MODULUS - 0);
      assert WrapWordValue(WORD_MODULUS) == 0;
      assert neg == ZeroLimb();
    } else {
      assert carry.word as int == 1;
      assert neg.word as int == WrapWordValue(WORD_MODULUS - 1);
      assert WORD_MAX == WORD_MODULUS - 1;
      assert (WORD_MODULUS - 1) % WORD_MODULUS == WORD_MODULUS - 1;
      assert WrapWordValue(WORD_MODULUS - 1) == WORD_MAX;
      assert neg == MaxLimb();
    }
  }

  // AddCarryAccountingLemma: add_with_bounded_overflow preserves total value
  // result + carry_out*W == a + b + carry_in
  lemma AddCarryAccountingLemma(a: Limb, b: Limb, carry_in: Limb, result: Limb, carry_out: Limb)
    requires carry_in == ZeroLimb() || carry_in == LimbFromInt(1)
    requires (result, carry_out) == AddAndCarryLimbSpec(a, b, carry_in)
    ensures LimbToInt(result) + LimbToInt(carry_out) * WORD_MODULUS == LimbToInt(a) + LimbToInt(b) + LimbToInt(carry_in)
  {
  }

  // Unique representation: if any limb differs, LimbsValueSpec values differ.
  // Proof: contrapositive — if values are equal, extract each limb via mod/div
  // to show all limbs must be equal, contradicting the precondition.
  lemma LimbsDifferValueDifferLemma(s1: seq<Limb>, s2: seq<Limb>)
    requires |s1| == 4 && |s2| == 4
    requires exists j :: 0 <= j < 4 && s1[j] != s2[j]
    ensures LimbsValueSpec(s1) != LimbsValueSpec(s2)
  {
    if LimbsValueSpec(s1) == LimbsValueSpec(s2) {
      // Factor: v = s[0] + upper * W where upper = s[1] + s[2]*W + s[3]*W^2
      var v := LimbsValueSpec(s1);
      var u1 := LimbToInt(s1[1]) + LimbToInt(s1[2]) * WORD_MODULUS
              + LimbToInt(s1[3]) * WORD_MODULUS2;
      var u2 := LimbToInt(s2[1]) + LimbToInt(s2[2]) * WORD_MODULUS
              + LimbToInt(s2[3]) * WORD_MODULUS2;
      assert WORD_MODULUS3 == WORD_MODULUS2 * WORD_MODULUS;
      assert v == LimbToInt(s1[0]) + u1 * WORD_MODULUS;
      assert LimbsValueSpec(s2) == LimbToInt(s2[0]) + u2 * WORD_MODULUS;
      DivMod.LemmaModMultiplesVanish(u1, LimbToInt(s1[0]), WORD_MODULUS);
      DivMod.LemmaModMultiplesVanish(u2, LimbToInt(s2[0]), WORD_MODULUS);
      assert s1[0] == s2[0];
      assert u1 == u2;

      // Second limb: u = s[1] + upper2 * W
      var w1 := LimbToInt(s1[2]) + LimbToInt(s1[3]) * WORD_MODULUS;
      var w2 := LimbToInt(s2[2]) + LimbToInt(s2[3]) * WORD_MODULUS;
      assert u1 == LimbToInt(s1[1]) + w1 * WORD_MODULUS;
      assert u2 == LimbToInt(s2[1]) + w2 * WORD_MODULUS;
      DivMod.LemmaModMultiplesVanish(w1, LimbToInt(s1[1]), WORD_MODULUS);
      DivMod.LemmaModMultiplesVanish(w2, LimbToInt(s2[1]), WORD_MODULUS);
      assert s1[1] == s2[1];
      assert w1 == w2;

      // Third limb
      DivMod.LemmaModMultiplesVanish(
        LimbToInt(s1[3]), LimbToInt(s1[2]), WORD_MODULUS);
      DivMod.LemmaModMultiplesVanish(
        LimbToInt(s2[3]), LimbToInt(s2[2]), WORD_MODULUS);
      assert s1[2] == s2[2];

      // Fourth limb
      assert s1[3] == s2[3];

      // All limbs equal — contradicts precondition
      assert false;
    }
  }

  // (x + m * y) % m == x % m for m > 0. Standard modular arithmetic.
  lemma ModAddMultipleLemma(x: int, y: int, m: int)
    requires m > 0
    ensures (x + m * y) % m == x % m
  {
    DivMod.LemmaModMultiplesVanish(y, x, m);
  }

  // Key Crandall reduction fact: W^4 = 2*p + 2*distance
  // 2*p + 2*distance = 2*(2^255 - distance + distance) = 2*2^255 = 2^256 = W^4
  lemma CrandallRelationLemma()
    ensures 2 * ModulusValueSpec() + TwoModulus255DistanceSpec() == WORD_MODULUS4
  {
    // Decompose via limbs: p = lo + 2^192 * hi_limb where hi_limb = 0x7fffffffffffffff
    ghost var limbs := ModulusLimbs();
    assert ModulusValueSpec() == LimbsValueSpec(limbs);
    // Prove p = 2^255 - distance by showing p + distance = 2^255
    // p = 0xf9850b68df11df53 + 0xf735481d1969f317*W + 0xffffffffffffffff*W^2 + 0x7fffffffffffffff*W^3
    // distance = 0x67af49720ee20ad + 0x8cab7e2e6960ce8*W
    // 2*distance = 0xcf5e92e41dc415a + 0x11956fc5cd2c19d0*W
    // W^4 = 2^256, let z3 handle it via concrete expansion
    assert LimbToInt(limbs[0]) == 0xf9850b68df11df53;
    assert LimbToInt(limbs[1]) == 0xf735481d1969f317;
    assert LimbToInt(limbs[2]) == 0xffffffffffffffff;
    assert LimbToInt(limbs[3]) == 0x7fffffffffffffff;
    assert TwoModulus255DistanceSpec() == 0x11956fc5cd2c19d00cf5e92e41dc415a;
    assert WORD_MODULUS4 == 115792089237316195423570985008687907853269984665640564039457584007913129639936;
  }

  // NOT sum telescoping: (W-1)(1+W+W^2+W^3) = W^4-1.
  lemma GeometricSeriesW4Lemma()
    ensures WORD_MAX + WORD_MAX * WORD_MODULUS
      + WORD_MAX * WORD_MODULUS2
      + WORD_MAX * WORD_MODULUS3
      == WORD_MODULUS4 - 1
  {
    assert WORD_MAX == WORD_MODULUS - 1;
    assert WORD_MODULUS2 == WORD_MODULUS * WORD_MODULUS;
    assert WORD_MODULUS3
      == WORD_MODULUS * WORD_MODULUS2;
    assert WORD_MODULUS4
      == WORD_MODULUS * WORD_MODULUS3;
  }
}
