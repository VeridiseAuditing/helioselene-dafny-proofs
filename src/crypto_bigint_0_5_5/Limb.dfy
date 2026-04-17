include "../helpers/Math.dfy"

module CryptoBigint_0_5_5_Limb {
  import MathHelpers
  import Power = Std.Arithmetic.Power
  import Power2 = Std.Arithmetic.Power2
  import opened Std.BoundedInts

  const WORD_BITS: nat := 64
  const WIDE_WORD_BITS: nat := 128
  // 2**64
  const WORD_MODULUS: int := 18446744073709551616
  // 2**63
  const WORD_MSB: int := 9223372036854775808
  const WIDE_WORD_MODULUS: int := 340282366920938463463374607431768211456
  const WORD_MAX: int := WORD_MODULUS - 1
  const LIMB_MAX: int := WORD_MAX
  const ALL_ONES_BV: bv64 := (0xFFFFFFFFFFFFFFFF) as bv64
  const LIMB_MODULUS: int := WORD_MODULUS
  const LIMB_BITS : nat := WORD_BITS

  // https://github.com/RustCrypto/crypto-bigint/blob/395bb171178990a93ef571664271dabc50749043/src/limb.rs#L38
  newtype Word = w: int | 0 <= w < WORD_MODULUS
  // https://github.com/RustCrypto/crypto-bigint/blob/395bb171178990a93ef571664271dabc50749043/src/limb.rs#L42
  newtype WideWord = w: int | 0 <= w < WIDE_WORD_MODULUS

  // https://github.com/RustCrypto/crypto-bigint/blob/395bb171178990a93ef571664271dabc50749043/src/limb.rs#L65
  datatype Limb = Limb(word: Word)

  // ===================================================================
  // HELPER FUNCTIONS
  // ===================================================================

  function {:rlimit 21} WrapWordValue(x: int): int
    ensures 0 <= WrapWordValue(x) < WORD_MODULUS
  {
    ((x % WORD_MODULUS) + WORD_MODULUS) % WORD_MODULUS
  }

  function {:rlimit 140} WordToBv(w: Word): bv64
    ensures WordToBv(w) as int == w as int
    ensures 0 <= WordToBv(w) as int < WORD_MODULUS
  {
    var w_int := (w as int);
    assert 0 <= w_int < WORD_MODULUS;
    assert w_int % WORD_MODULUS == w_int;
    w_int as bv64
  }

  function {:rlimit 61} BvToWord(x: bv64): Word
    ensures BvToWord(x) as int == x as int
    ensures WordToBv(BvToWord(x)) == x
  {
    WordFromInt(x as int)
  }

  function {:rlimit 23} WideWordToWord(w: WideWord): Word
  {
    var w_int := (w as int);
    WordFromInt(w_int % WORD_MODULUS)
  }

  function {:rlimit 112} WideWordToBv(w: WideWord): bv128
    ensures WideWordToBv(w) as int == w as int
  {
    var w_int := (w as int);

    assert 0 <= w_int < WIDE_WORD_MODULUS;
    assert w_int % WIDE_WORD_MODULUS == w_int;
    assert w_int % WIDE_WORD_MODULUS == w_int as bv128 as int;

    w_int as bv128
  }

  function {:rlimit 30} BvToWideWord(x: bv128): WideWord
  {
    x as int as WideWord
  }

  function {:rlimit 25} WrapWord(x: int): Word
    ensures WrapWord(x) as int == WrapWordValue(x)
  {
    WrapWordValue(x) as Word
  }

  function {:rlimit 17} ZeroWord(): Word
  {
    0 as Word
  }

  function {:rlimit 18} MaxWord(): Word
  {
    WORD_MAX as Word
  }

  function {:rlimit 443831} ZeroLimb(): Limb
  {
    Limb(ZeroWord())
  }

  function {:rlimit 13} WordFromInt(x: int): Word
    requires 0 <= x < WORD_MODULUS
  {
    x as Word
  }

  function {:rlimit 21} WordFromBool(x: bool): Word
  {
    WordFromInt(if x then 1 else 0)
  }

  function {:rlimit 56} WordShr(x: Word, bits: int): Word
  requires 0 <= bits < WORD_BITS
  {
    (x as int / MathHelpers.pow2(bits)) as Word
  }

  function {:rlimit 55} WideWordShr(x: WideWord, bits: int): WideWord
  requires 0 <= bits < 128
  {
    (x as int / MathHelpers.pow2(bits)) as WideWord
  }

  function {:rlimit 24} LimbFromInt(x: int): Limb
    requires 0 <= x < WORD_MODULUS
  {
    Limb(WordFromInt(x))
  }

  function {:rlimit 443831} LimbToInt(x: Limb): int
  {
    x.word as int
  }

  function {:rlimit 20} AllOnesWord(): Word
  {
    WordFromInt(WORD_MAX)
  }

  function {:rlimit 443831} MaxLimb(): Limb
  {
    Limb(AllOnesWord())
  }

  function {:rlimit 443831} AllOnesLimb(): Limb
  {
    Limb(AllOnesWord())
  }

  function {:rlimit 21} WrapWideValue(x: int): int
    ensures 0 <= WrapWideValue(x) < WIDE_WORD_MODULUS
  {
    ((x % WIDE_WORD_MODULUS) + WIDE_WORD_MODULUS) % WIDE_WORD_MODULUS
  }

  function {:rlimit 23} BorrowBit(borrow: Word): int
    ensures 0 <= BorrowBit(borrow) < 2
  {
    (borrow as int) / WORD_MSB
  }

  function {:rlimit 443831} LimbXor(a: Limb, b: Limb): Limb
  {
    Limb(BvToWord(WordToBv(a.word) ^ WordToBv(b.word)))
  }

  function {:rlimit 71} IsHalfMask(x: Limb): bool
  {
    x == LimbFromInt(WORD_MODULUS/2 - 1) || x == LimbShr(MaxLimb(), 1)
  }

  // NOTE: Rust Limb::bitand is general (self.0 & rhs.0). Dafny restricts one operand to
  // ZeroLimb/MaxLimb/IsHalfMask and uses conditional logic instead of native AND. Covers all
  // actual call sites but is not a general port.
  // Current use sites: select_word, field_is_odd, field_from_repr. Expand carefully if needed.
  function {:rlimit 109} LimbAnd(a: Limb, b: Limb): (out: Limb)
    requires a == ZeroLimb()
      || b == ZeroLimb()
      || a == MaxLimb()
      || b == MaxLimb()
      || IsHalfMask(a)
      || IsHalfMask(b)
  {
    if a == ZeroLimb() || b == ZeroLimb() then
      ZeroLimb()
    else if a == MaxLimb() then
      b
    else if b == MaxLimb() then
      a
    else if IsHalfMask(a) then
      if LimbToInt(b) < WORD_MODULUS/2
        then b
        else LimbFromInt(LimbToInt(b) - WORD_MODULUS/2)
    else
    // if IsHalfMask(b) then
      if LimbToInt(a) < WORD_MODULUS/2
        then a
        else LimbFromInt(LimbToInt(a) - WORD_MODULUS/2)
  }

  // ===================================================================
  // PORTED FUNCTIONS
  // ===================================================================

  // Ported from Limb::wrapping_neg
  // https://github.com/RustCrypto/crypto-bigint/blob/395bb171178990a93ef571664271dabc50749043/src/limb/neg.rs#L17-L19
  function {:rlimit 201} wrapping_neg(x: Limb) : Limb
    ensures wrapping_neg(x).word as int == WrapWordValue(WORD_MODULUS - (x.word as int))
  {
    var r := WrapWordValue(WORD_MODULUS - (x.word as int));
    Limb(WrapWord(r))
  }

  // Ported from https://github.com/RustCrypto/crypto-bigint/blob/395bb171178990a93ef571664271dabc50749043/src/limb/sub.rs#L10-L16
  /// Computes `self_ - (rhs + borrow)`, returning the result along with the new borrow.
  method {:rlimit 5918}  sbb(self_: Limb, rhs: Limb, borrow: Limb) returns (diff: Limb, borrowOut: Limb)
    requires borrow == ZeroLimb() || borrow == MaxLimb()
    ensures (diff, borrowOut) == SubAndBorrowLimbSpec(self_, rhs, borrow)
  {
    // GHOST COMPUTATION
    ghost var borrow_in := borrow;

    // Original code:
    // let a = self.0 as WideWord;
    var a := self_.word as WideWord;

    // Original code:
    // let b = rhs.0 as WideWord;
    var b := rhs.word as WideWord;

    // Original code:
    // let borrow = (borrow.0 >> (Self::BITS - 1)) as WideWord;
    var borrow := WordShr(borrow.word, (WORD_BITS - 1)) as WideWord;

    // LEMMA
    assert {:isolate} borrow as int == if borrow_in == ZeroLimb() then 0 else 1 by {
      Power2To64Lemma();
      assert {:isolate} Power2.Pow2(WORD_BITS) == TWO_TO_THE_64;
      assert {:isolate} {:fuel Power2.Pow2,64} Power2.Pow2(WORD_BITS - 1) == TWO_TO_THE_63;
    }

    // Original code:
    // let ret = a.wrapping_sub(b + borrow);
    var ret: WideWord := ((a as int - (b as int + borrow as int)) % WIDE_WORD_MODULUS) as WideWord;

    // LEMMAs
    ghost var int_diff := (a as int - (b as int + borrow as int));
    if int_diff >= 0 {
      assert ret as int == int_diff;
      assert {:isolate} WideWordShr(ret, WORD_BITS) == 0 by {
        Power2To64Lemma();
      }
      assert WideWordToWord(ret) as int == ret as int;
    }
    else {
      assert ret as int - WIDE_WORD_MODULUS == int_diff;
      assert int_diff >= -WORD_MODULUS;
      WideWordShrIsAllOnesLemma(ret);
      assert ret as int == WIDE_WORD_MODULUS + int_diff;
      assert ret as int >= WIDE_WORD_MODULUS - WORD_MODULUS;
      assert WideWordShr(ret, WORD_BITS) as int == WORD_MODULUS - 1;
      assert WideWordToWord(ret) as int == int_diff % WORD_MODULUS;
      assert WideWordToWord(ret) as int - WORD_MODULUS == int_diff;
    }

    // Original code:
    // (Limb(ret as Word), Limb((ret >> Self::BITS) as Word))
    return Limb(WideWordToWord(ret) as Word), Limb(WideWordShr(ret, WORD_BITS) as Word);
  }

  // Ported from https://github.com/RustCrypto/crypto-bigint/blob/395bb171178990a93ef571664271dabc50749043/src/limb/mul.rs#L10-L17
  // NOTE: Dafny uses WrapWideValue and restrictive preconditions on carry/c so we can prove correctness.
  // In Rust, the sum
  // a + b*c + carry always fits in u128 so wrapping never triggers.
  // This ensures Dafny proves that mac is never used unsafely
  method {:rlimit 69022} {:isolate_assertions} mac(a: Limb, b: Limb, c: Limb, carry: Limb) returns (low: Limb, high: Limb)
    requires carry == ZeroLimb() || carry == LimbFromInt(1) || LimbToInt(c) < (WORD_MODULUS - 1)
    ensures (low, high) == mAddAndCarryLimbSpec(a, b, c, carry)
  {
    // Original code:
    // let a = self.0 as WideWord;
    var a_u128: WideWord := a.word as WideWord;

    // Original code:
    // let b = b.0 as WideWord;
    var b_u128: WideWord := b.word as WideWord;

    // Original code:
    // let c = c.0 as WideWord;
    var c_u128: WideWord := c.word as WideWord;

    // Original code:
    // let carry = carry.0 as WideWord;
    var carry_u128: WideWord := carry.word as WideWord;

    // Original code:
    // let ret = a + (b * c) + carry;
    var ret: WideWord := a_u128 + (b_u128 * c_u128) + carry_u128 by {
      // GHOST CODE
      assert a_u128 as int <= WORD_MODULUS - 1;
      assert b_u128 as int <= WORD_MODULUS - 1;
      assert c_u128 as int <= WORD_MODULUS - 1;
      assert carry_u128 as int <= WORD_MODULUS - 1;
      assert {:isolate} (b_u128 as int * c_u128 as int) <= (WORD_MODULUS - 1) * (WORD_MODULUS - 1) by {
        assert b_u128 as int <= WORD_MODULUS - 1;
        assert c_u128 as int <= WORD_MODULUS - 1;
      }
      assert (b_u128 * c_u128) as int <= WORD_MODULUS * WORD_MODULUS - 2 * WORD_MODULUS + 1;
      assert (b_u128 * c_u128 + carry_u128) as int <= WORD_MODULUS * WORD_MODULUS - WORD_MODULUS;
      assert (a_u128 + b_u128 * c_u128 + carry_u128) as int <= WORD_MODULUS * WORD_MODULUS - 1;
      assert (WORD_MODULUS * WORD_MODULUS) as int == WIDE_WORD_MODULUS;
      assert (a_u128 + b_u128 * c_u128 + carry_u128) as int <= WIDE_WORD_MODULUS - 1;
    }

    // GHOST CODE
    assert ret as int == a.word as int + (b.word as int * c.word as int) + carry.word as int;

    // Original code:
    // (Limb(ret as Word), Limb((ret >> Self::BITS) as Word))
    low := Limb((ret as int % WORD_MODULUS) as Word);
    high := Limb((WideWordShr(ret, WORD_BITS) as int % WORD_MODULUS) as Word);

    // GHOST CODE
    assert {:isolate} low.word as int + high.word as int * WORD_MODULUS == ret as int by {
      Power2To64Lemma();
    }
  }

  function {:rlimit 45} LimbShr(x: Limb, bits: int) : Limb
    requires 0 <= bits < WORD_BITS
  {
    Limb(WordShr(x.word, bits))
  }

  // Rust u64::overflowing_sub: wrapping subtraction returning (result, underflowed).
  function {:rlimit 36} overflowing_sub(a: Word, b: Word): (Word, bool)
  {
    var diff_mod := (a as int - b as int + WORD_MODULUS) % WORD_MODULUS;
    (WordFromInt(diff_mod), (a as int) < (b as int))
  }

  // Ported from monero-oxide field.rs:89-93
  // Unlike sbb, borrow in/out is 0 or 1 (not 0 or MaxLimb).
  // Spec: diff + borrow_out * WORD_MODULUS == a - b - c.
  method {:rlimit 646} sub_with_bounded_overflow(
    a: Limb, b: Limb, c: Limb
  ) returns (diff: Limb, borrowOut: Limb)
    requires 0 <= c.word && c.word <= 1
    ensures (diff, borrowOut) == SubBoundedSpec(a, b, c)
  {
    var (limb1, borrow1) := overflowing_sub(a.word, b.word);
    var (limb2, borrow2) := overflowing_sub(limb1, c.word);
    diff := Limb(limb2);
    borrowOut := Limb(BoolToInt(borrow1 || borrow2) as Word);
  }

  // https://github.com/rust-lang/rust/blob/d9617c8d9a55773a96b61ba3a4acb107d65615c1/library/core/src/num/uint_macros.rs#L2747C9-L2750C10
  // Rust u64::overflowing_add: wrapping subtraction returning (result, overflowed).
  function {:rlimit 36} overflowing_add(a: Word, b: Word): (Word, bool)
  {
    var sum_mod := (a as int + b as int) % WORD_MODULUS;
    (WordFromInt(sum_mod), (a as int + b as int) >= WORD_MODULUS)
  }

  // Ported from crypto-bigint 0.5.5 Limb::adc (limb/add.rs:8-16)
  // Limb addition with carry: computes a + b + c, returns (sum, carry_out).
  // Rust uses wide-word cast; Dafny uses two overflowing_add (equivalent for carry ∈ {0,1}).
  method {:rlimit 997} limb_adc(a: Limb, b: Limb, c: Limb) returns (add: Limb, carryOut: Limb)
    requires 0 <= c.word && c.word <= 1
    ensures AddAndCarryLimbSpec(a, b, c) == (add, carryOut)
  {
    var (limb1_word, carry1) := overflowing_add(a.word, b.word);
    var (limb2_word, carry2) := overflowing_add(limb1_word, c.word);
    return Limb(limb2_word), Limb(BoolToInt(carry1 || carry2) as Word);
  }

  function {:rlimit 443831} BoolToInt(b: bool): int { if b then 1 else 0 }
  function {:rlimit 443831} IntToBool(i: int): bool requires 0 <= i <= 1 { if i == 1 then true else false }

  // ===================================================================
  // SPECS
  // ===================================================================

  ghost function {:rlimit 125} AddAndCarryLimbSpec(lhs: Limb, rhs: Limb, carryIn: Limb): (sumAndCarry: (Limb, Limb))
  requires carryIn == ZeroLimb() || carryIn == LimbFromInt(1)
  ensures sumAndCarry.1 == ZeroLimb() || sumAndCarry.1 == LimbFromInt(1)
  {
      var l := LimbToInt(lhs);
      var r := LimbToInt(rhs);
      var c := LimbToInt(carryIn);

      var sum := l + r + c;
      var carry := if sum >= WORD_MODULUS then 1 else 0;
      var reduced_sum := if sum >= WORD_MODULUS then sum - WORD_MODULUS else sum;
      assert 0 <= reduced_sum < WORD_MODULUS;
      assert 0 <= carry <= 1;
      assert reduced_sum + carry * WORD_MODULUS == l + r + c;

      (LimbFromInt(reduced_sum), LimbFromInt(carry))
  }

  ghost function {:rlimit 15368} mAddAndCarryLimbSpec(constant: Limb, prod0: Limb, prod1: Limb, carryIn: Limb): (maddAndCarry: (Limb, Limb))
  requires
    carryIn == ZeroLimb()
    || carryIn == LimbFromInt(1)
    || LimbToInt(prod1) < WORD_MODULUS - 1
  {
      var k := LimbToInt(constant);
      var l := LimbToInt(prod0);
      var r := LimbToInt(prod1);
      var c := LimbToInt(carryIn);

      var madd := k + l * r + c;
      var reducedMadd := madd % WORD_MODULUS;
      var carry := madd / WORD_MODULUS;
      // ghost code
      assert reducedMadd + carry * WORD_MODULUS == k + l * r + c;

      // ghost code: prove bound on carry
      mAddCarryBoundLemma(k as Word, l as Word, r as Word, c as Word);

      (LimbFromInt(reducedMadd), LimbFromInt(carry))
  }

  ghost function {:rlimit 443831} borrowOutToBorrowInSpec(borrowIn: Limb): (borrowOut: int)
  requires borrowIn == ZeroLimb() || borrowIn == MaxLimb()
  {
    if borrowIn == ZeroLimb() then 0 else 1
  }

  ghost function {:rlimit 443831} borrowOutToShiftSpec(borrowIn: Limb): (borrowOut: int)
  requires borrowIn == ZeroLimb() || borrowIn == MaxLimb()
  {
    if borrowIn == ZeroLimb() then 0 else WORD_MAX
  }

  ghost function {:rlimit 106} SubAndBorrowLimbSpec(lhs: Limb, rhs: Limb, borrowIn: Limb): (diffAndBorrow: (Limb, Limb))
  requires borrowIn == ZeroLimb() || borrowIn == MaxLimb()
  ensures diffAndBorrow.1 == ZeroLimb() || diffAndBorrow.1 == MaxLimb()
  {
      var l := LimbToInt(lhs);
      var r := LimbToInt(rhs);
      var c := borrowOutToBorrowInSpec(borrowIn);

      var difference := l - (r + c);
      var carry := if difference < 0 then WORD_MODULUS-1 else 0;
      var reduced_diff := if difference < 0 then difference + WORD_MODULUS else difference;
      assert 0 <= reduced_diff < WORD_MODULUS;
      assert 0 == carry || carry == WORD_MODULUS-1;
      assert reduced_diff - (if carry == 0 then 0 else WORD_MODULUS) == l - (r + c);

      (LimbFromInt(reduced_diff), LimbFromInt(carry))
  }

  // Spec for sub_with_bounded_overflow: borrow is 0 or 1 (not MaxLimb).
  // diff + borrow_out * WORD_MODULUS == a - b - c.
  // Spec for sub_with_bounded_overflow.
  // diff == (a - b - c) mod WORD_MODULUS; borrow == 1 iff a - b - c < 0.
  ghost function {:rlimit 104} SubBoundedSpec(
    a: Limb, b: Limb, c: Limb
  ): (diffAndBorrow: (Limb, Limb))
    requires 0 <= c.word && c.word <= 1
    ensures diffAndBorrow.1 == ZeroLimb() || diffAndBorrow.1 == LimbFromInt(1)
  {
    var l := LimbToInt(a);
    var r := LimbToInt(b);
    var cin := c.word as int;
    var difference := l - r - cin;
    var borrow := if difference < 0 then 1 else 0;
    var reduced := if difference < 0
      then difference + WORD_MODULUS
      else difference;
    (LimbFromInt(reduced), LimbFromInt(borrow))
  }

  // Key property for chaining: diff == a - b - c + borrow * WORD_MODULUS.
  lemma {:rlimit 82} SubBoundedSpecLemma(a: Limb, b: Limb, c: Limb)
    requires 0 <= c.word && c.word <= 1
    ensures var (diff, borrow) := SubBoundedSpec(a, b, c);
      LimbToInt(diff) == LimbToInt(a) - LimbToInt(b)
        - (c.word as int) + LimbToInt(borrow) * WORD_MODULUS
  {
  }

  // ===================================================================
  // LEMMAS
  // ===================================================================

  lemma {:rlimit 443831} WideWordShrIsAllOnesLemma(wideWord: WideWord)
    requires wideWord as int >= WIDE_WORD_MODULUS - WORD_MODULUS
    ensures WideWordShr(wideWord, WORD_BITS) as int == WORD_MAX
  {
    var lower := wideWord as int % WORD_MODULUS;
    var upper := wideWord as int / WORD_MODULUS;
    assert lower + upper * WORD_MODULUS == wideWord as int;
    assert upper == WORD_MAX;

    var asBV: bv128 := WideWordToBv(wideWord);

    assert (asBV >> WORD_BITS) as int == (asBV as int) / WORD_MODULUS;
    assert {:isolate} (asBV >> WORD_BITS) as int == WideWordShr(wideWord, WORD_BITS) as int by {
      Power2To64Lemma();
    }
    assert {:isolate} (asBV as int) == wideWord as int;
    assert {:isolate} (wideWord as int) / WORD_MODULUS == upper;
  }

  lemma {:rlimit 60} WordRoundTrip_bv(w: Word)
    ensures BvToWord(WordToBv(w)) == w
  {
    assert BvToWord(WordToBv(w)) as int == w as int;
  }

  lemma {:rlimit 19761} mAddCarryBoundLemma_Helper0(constant: Word, prod0: Word, prod1: Word, carryIn: Word)
    requires prod1 as int < WORD_MODULUS - 1
    ensures (constant as int + prod0 as int * prod1 as int + carryIn as int) < WORD_MODULUS * WORD_MODULUS - WORD_MODULUS + 2
  {
  }

  lemma {:rlimit 19} mAddCarryBoundLemma(constant: Word, prod0: Word, prod1: Word, carryIn: Word)
    ensures
      prod1 as int < WORD_MODULUS - 1
      ==>
      (constant as int + prod0 as int * prod1 as int + carryIn as int) < WORD_MODULUS * WORD_MODULUS - WORD_MODULUS + 2
  {
    if prod1 as int < WORD_MODULUS - 1 {
      mAddCarryBoundLemma_Helper0(constant, prod0, prod1, carryIn);
    }
  }
  // BV/int boundary axiom: XOR with ZeroLimb is identity.
  lemma {:rlimit 207} LimbXorZeroLemma(x: Limb)
    ensures LimbXor(x, ZeroLimb()) == x
  {
    // XOR with 0 is identity for bv64
    var bv_x := WordToBv(x.word);
    assert bv_x ^ (0 as bv64) == bv_x;
  }

  // BV→int for XOR with all-ones: proved by recursive bit decomposition.
  // int_not(x, n) computes the bitwise NOT of an n-bit integer in the int domain.
  ghost function {:rlimit 141} int_not(x: nat, n: nat): nat
    requires x < MathHelpers.pow2(n)
    ensures int_not(x, n) < MathHelpers.pow2(n)
    decreases n
  {
    MathHelpers.Pow2PositiveLemma(n);
    if n == 0 then 0
    else
      var bit := x % 2;
      var rest := x / 2;
      MathHelpers.Pow2PositiveLemma(n - 1);
      assert MathHelpers.pow2(n) == 2 * MathHelpers.pow2(n - 1);
      (1 - bit) + 2 * int_not(rest, n - 1)
  }

  // int_not(x, n) == (2^n - 1) - x.
  lemma {:rlimit 275} IntNotValueLemma(x: nat, n: nat)
    requires x < MathHelpers.pow2(n)
    ensures int_not(x, n) == MathHelpers.pow2(n) - 1 - x
    decreases n
  {
    MathHelpers.Pow2PositiveLemma(n);
    if n == 0 {
    } else {
      var bit := x % 2;
      var rest := x / 2;
      MathHelpers.Pow2PositiveLemma(n - 1);
      assert MathHelpers.pow2(n) == 2 * MathHelpers.pow2(n - 1);
      IntNotValueLemma(rest, n - 1);
      assert int_not(rest, n - 1) == MathHelpers.pow2(n - 1) - 1 - rest;
      // int_not(x, n) = (1 - bit) + 2 * (pow2(n-1) - 1 - rest)
      //               = 1 - bit + 2*pow2(n-1) - 2 - 2*rest
      //               = pow2(n) - 1 - bit - 2*rest
      //               = pow2(n) - 1 - x
      assert x == 2 * rest + bit;
    }
  }

  // BV XOR with all-ones equals int_not (BV/int correspondence for NOT).
  // This is the key BV/int crossing lemma.
  lemma {:rlimit 82} {:axiom} BvXorAllOnesLemma(bx: bv64)
    ensures bx as int < MathHelpers.pow2(64)
    ensures (bx ^ ALL_ONES_BV) as int == int_not(bx as int, 64)

  lemma {:rlimit 105} {:fuel Power.Pow,64} {:fuel Power2.Pow2,3} {:auto_apply} Power2To64Lemma()
    ensures Power2.Pow2(64) == WORD_MODULUS
  {
    Power2.Lemma2To64();
    assert {:isolate} Power2.Pow2(64) == TWO_TO_THE_64;
    assert TWO_TO_THE_64 == WORD_MODULUS;
  }

  // XOR with MaxLimb is bitwise NOT: NOT(x) = WORD_MAX - x.
  lemma {:rlimit 21351} {:isolate_assertions} LimbXorMaxLemma(x: Limb)
    ensures LimbToInt(LimbXor(x, MaxLimb()))
      == WORD_MAX - LimbToInt(x)
  {
    var bx: bv64 := WordToBv(x.word);
    BvXorAllOnesLemma(bx);
    MathHelpers.Pow2PositiveLemma(64);
    assert {:isolate} MathHelpers.pow2(64) == WORD_MODULUS by {
      Power2.Lemma2To64();
      assert Power2.Pow2(64) == WORD_MODULUS;
      assert WORD_MODULUS == TWO_TO_THE_64;
    }
    IntNotValueLemma(bx as int, 64);
    assert int_not(bx as int, 64) == WORD_MAX - bx as int;
  }

  // Corollary: XOR with mask selects identity or NOT.
  lemma {:rlimit 113} LimbXorMaskLemma(x: Limb, mask: Limb)
    requires mask == ZeroLimb() || mask == MaxLimb()
    ensures mask == ZeroLimb() ==>
      LimbXor(x, mask) == x
    ensures mask == MaxLimb() ==>
      LimbToInt(LimbXor(x, mask))
        == WORD_MAX - LimbToInt(x)
  {
    if mask == ZeroLimb() {
      LimbXorZeroLemma(x);
    } else {
      LimbXorMaxLemma(x);
    }
  }
}
