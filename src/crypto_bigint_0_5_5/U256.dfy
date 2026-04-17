include "Limb.dfy"
include "../helpers/Limbs.dfy"

module CryptoBigint_0_5_5_U256 {
  import opened CryptoBigint_0_5_5_Limb
  import opened Limbs
  import Power = Std.Arithmetic.Power

  const TWO_POW_256: int := WORD_MODULUS4
  const U256_LIMBS: int := 4

  // NOTE: Rust Uint<LIMBS> is #[derive(Copy, Clone)] stack-allocated. Dafny U256 is heap-allocated
  // with array<Limb>, requiring fresh() ensures and explicit copy() for deep copies.
  class U256 {
    var limbs: array<Limb>

    ghost predicate Valid() reads this {
      limbs.Length == 4
    }

    // =================================================================
    // HELPER FUNCTIONS
    // =================================================================

    constructor(limbs: array<Limb>)
      requires limbs.Length == 4
      ensures this.limbs == limbs
      ensures Valid()
    {
      this.limbs := limbs;
    }

    method {:rlimit 20} AsLimbs() returns (limbs: array<Limb>)
    {
      limbs := this.limbs;
    }

    // Verification helper (no Rust counterpart): Dafny class semantics require explicit deep copy.
    // Deep copy: returns a fresh U256 with the same value.
    method {:rlimit 3360} copy() returns (result: U256)
      requires this.Valid()
      ensures result.Valid()
      ensures fresh(result.limbs)
      ensures result.ValueSpec() == this.ValueSpec()
      ensures result.limbs[..] == this.limbs[..]
    {
      var limbs := new Limb[U256_LIMBS][
        this.limbs[0], this.limbs[1],
        this.limbs[2], this.limbs[3]];
      result := new U256(limbs);
    }

    // =================================================================
    // PORTED FUNCTIONS
    // =================================================================

    // https://github.com/RustCrypto/crypto-bigint/blob/v0.5.5/src/uint/sub.rs#L11-L23
    /// Computes `a - (b + borrow)`, returning the result along with the new borrow.
    method {:rlimit 422698} {:fuel LimbsDiffSpec,5} sbb(rhs: U256, borrow: Limb) returns (diff: U256, borrowOut: Limb)
      requires this.Valid()
      requires rhs.Valid()
      requires borrow == ZeroLimb() || borrow == MaxLimb()
      ensures fresh(diff) && fresh(diff.limbs)
      ensures diff.Valid()
      ensures borrowOut == ZeroLimb() || borrowOut == MaxLimb()
      ensures borrowOut == ZeroLimb() <==>
        this.ValueSpec() - (rhs.ValueSpec() + borrowOutToBorrowInSpec(borrow)) >= 0
      ensures
        diff.ValueSpec() - (if borrowOut == ZeroLimb() then 0 else WORD_MODULUS4)
        == this.ValueSpec() - (rhs.ValueSpec() + borrowOutToBorrowInSpec(borrow))
    {
      // GHOST CODE
      ghost var borrowIn := borrow;
      // Copy borrow to a mutable variable for the loop, to match Rust's mutable borrow of borrow.
      var borrow := borrow;

      // Original code:
      // let mut limbs = [Limb::ZERO; LIMBS];
      // let mut i = 0;
      var limbs := new Limb[U256_LIMBS][ZeroLimb(), ZeroLimb(), ZeroLimb(), ZeroLimb()];
      var i := 0;

      // Ghost code:
      ghost var partialDiff := LimbsDiffSpec(this.limbs[..0], rhs.limbs[..0], borrowIn);
      assert {:split_here} true;

      // Original code:
      // while i < LIMBS {
      //     let (w, b) = self.limbs[i].sbb(rhs.limbs[i], borrow);
      //     limbs[i] = w;
      //     borrow = b;
      //     i += 1;
      // }
      while i < U256_LIMBS
        modifies limbs
        invariant 0 <= i <= U256_LIMBS
        invariant {:isolate} partialDiff == LimbsDiffSpec(this.limbs[..i], rhs.limbs[..i], borrowIn)
        invariant borrow == partialDiff[i]
        invariant limbs[..i] == partialDiff[..i]
        invariant borrow == ZeroLimb() || borrow == MaxLimb()
      {
        // GHOST CODE
        ghost var diffAndBorrow := SubAndBorrowLimbSpec(this.limbs[i], rhs.limbs[i], borrow);
        ghost var limbsPrefix := limbs[..i];

        // Port of original code
        var rhs_limb := rhs.limbs[i];
        var w, b;
        w, b := CryptoBigint_0_5_5_Limb.sbb(this.limbs[i], rhs_limb, borrow);

        // GHOST CODE
        ghost var nextPartial := limbsPrefix + [w, b];
        assert w == diffAndBorrow.0;
        assert b == diffAndBorrow.1;
        assert partialDiff == limbsPrefix + [borrow];
        LimbsDiffStepLemma(this.limbs[..i], rhs.limbs[..i], borrowIn, this.limbs[i], rhs.limbs[i], limbsPrefix, borrow, w, b);

        // Port of original code
        limbs[i] := w;
        borrow := b;
        i := i + 1;

        // GHOST CODE
        partialDiff := nextPartial;
      }

      // LEMMAs
      assert {:split_here} true;
      ghost var fullDiff := partialDiff;
      assert limbs[..] == fullDiff[..U256_LIMBS];
      assert borrow == fullDiff[U256_LIMBS];
      assert Power.Pow(WORD_MODULUS, U256_LIMBS) == WORD_MODULUS4;
      assert this.ValueSpec() == LimbsValueSpec(this.limbs[..]);
      assert rhs.ValueSpec() == LimbsValueSpec(rhs.limbs[..]);
      assert LimbsValueSpec(LimbsDiffSpec(this.limbs[..], rhs.limbs[..], borrowIn)[..U256_LIMBS])
        - (if LimbsDiffSpec(this.limbs[..], rhs.limbs[..], borrowIn)[U256_LIMBS] == ZeroLimb() then 0 else WORD_MODULUS4)
        ==
        this.ValueSpec() - (rhs.ValueSpec() + (if borrowIn == ZeroLimb() then 0 else 1));
      assert {:isolate} LimbsValueSpec(limbs[..])
        - (if borrow == ZeroLimb() then 0 else WORD_MODULUS4)
        ==
        LimbsValueSpec(this.limbs[..]) - (LimbsValueSpec(rhs.limbs[..]) + (if borrowIn == ZeroLimb() then 0 else 1));

      // Original code:
      // (Self { limbs }, borrow)
      diff := new U256(limbs);
      borrowOut := borrow;

      // LEMMAS
      var trueDiff := this.ValueSpec() - (rhs.ValueSpec() + borrowOutToBorrowInSpec(borrowIn));
      assert diff.ValueSpec() - (if borrowOut == ZeroLimb() then 0 else WORD_MODULUS4) == trueDiff;
      assert borrowOut == ZeroLimb() || borrowOut == MaxLimb();
      assert borrowOut == ZeroLimb() <==> diff.ValueSpec() == trueDiff;
      assert -WORD_MODULUS4 <= trueDiff <= WORD_MODULUS4;
      assert 0 <= diff.ValueSpec() < WORD_MODULUS4;
      assert borrowOut == ZeroLimb() ==> trueDiff >= 0;
      assert borrowOut != ZeroLimb() ==> trueDiff < 0;
    }

    // Ported from crypto-bigint 0.5.5 Uint::adc (uint/add.rs)
    // Addition with carry: computes `a + b + carry_in`, returning sum and carry_out.
    // Analogous to sbb for subtraction.
    method {:rlimit 373757} {:fuel LimbsSumSpec,5} adc(b: U256, carry: Limb) returns (sum: U256, carryOut: Limb)
      requires this.Valid()
      requires b.Valid()
      requires carry == ZeroLimb() || carry == LimbFromInt(1)
      ensures fresh(sum.limbs)
      ensures sum.Valid()
      ensures carryOut == ZeroLimb() || carryOut == LimbFromInt(1)
      ensures sum.ValueSpec() + LimbToInt(carryOut) * WORD_MODULUS4
        == this.ValueSpec() + b.ValueSpec() + LimbToInt(carry)
    {
      ghost var carryIn := carry;
      var limbs := new Limb[U256_LIMBS][
        ZeroLimb(), ZeroLimb(), ZeroLimb(), ZeroLimb()];
      var c := carry;
      var i := 0;
      ghost var partialSum := LimbsSumSpec(this.limbs[..0], b.limbs[..0], carryIn);
      assert {:split_here} true;

      while i < U256_LIMBS
        invariant 0 <= i <= U256_LIMBS
        invariant {:isolate} partialSum == LimbsSumSpec(this.limbs[..i], b.limbs[..i], carryIn)
        invariant c == ZeroLimb() || c == LimbFromInt(1)
        invariant c == partialSum[i]
        invariant limbs[..i] == partialSum[..i]
      {
        ghost var limbsPrefix := limbs[..i];
        ghost var sumAndCarry := AddAndCarryLimbSpec(this.limbs[i], b.limbs[i], c);
        var w, c_new := limb_adc(
          this.limbs[i], b.limbs[i], c);
        ghost var nextPartial := limbsPrefix + [w, c_new];

        assert w == sumAndCarry.0;
        assert c_new == sumAndCarry.1;
        assert partialSum == limbsPrefix + [c];
        LimbsSumStepLemma(this.limbs[..i], b.limbs[..i], carryIn, this.limbs[i], b.limbs[i], limbsPrefix, c, w, c_new);

        limbs[i] := w;
        c := c_new;
        i := i + 1;
        partialSum := nextPartial;
      }

      assert {:split_here} true;
      ghost var fullSum := partialSum;
      sum := new U256(limbs);
      carryOut := c;

      // LEMMAS
      assert c == fullSum[4];
      assert limbs[..] == fullSum[..4];
      ghost var carryVal := LimbToInt(c);
      assert 0 <= carryVal <= 1;
      WrappingAddLemma(fullSum, carryVal);
      assert sum.ValueSpec() == LimbsValueSpec(limbs[..]);
      assert sum.ValueSpec() + LimbToInt(carryOut) * WORD_MODULUS4
        == LimbsValueSpec(fullSum);
      assert this.ValueSpec() == LimbsValueSpec(this.limbs[..]);
      assert b.ValueSpec() == LimbsValueSpec(b.limbs[..]);
      assert LimbsValueSpec(fullSum)
        == this.ValueSpec() + b.ValueSpec() + LimbToInt(carryIn);
    }

    // Ported from https://github.com/RustCrypto/crypto-bigint/blob/395bb171178990a93ef571664271dabc50749043/src/uint.rs#L156-159
    method {:rlimit 27} as_limbs() returns (limbs: array<Limb>)
      requires this.Valid()
      ensures limbs == this.limbs
    {
      // Original Code:
      // &self.limbs
      limbs := this.limbs;
    }

    // Ported from https://github.com/RustCrypto/crypto-bigint/blob/395bb171178990a93ef571664271dabc50749043/src/uint.rs#L161-L164
    method {:rlimit 27} as_limbs_mut() returns (limbs: array<Limb>)
      requires this.Valid()
      ensures limbs == this.limbs
    {
      // Original Code:
      // &mut self.limbs
      limbs := this.limbs;
    }

    // Ported from https://github.com/RustCrypto/crypto-bigint/blob/395bb171178990a93ef571664271dabc50749043/src/uint/add.rs
    // Computes `self + rhs` mod 2^256 (wrapping addition, ignoring final carry)
    // NOTE: Rust uses Limb::adc; Dafny calls limb_adc (ported from crypto-bigint limb/add.rs).
    method {:rlimit 831010} {:fuel LimbsSumSpec,5} wrapping_add(b: U256) returns (result: U256)
      requires this.Valid()
      requires b.Valid()
      ensures result.Valid()
      ensures fresh(result.limbs)
      ensures result.ValueSpec() == (this.ValueSpec() + b.ValueSpec()) % WORD_MODULUS4
    {
      // original code:
      // let mut limbs = [Limb::ZERO; LIMBS];
      // let mut carry = Limb::ZERO;
      // while i < LIMBS { let (w, c) = adc(self.limbs[i], rhs.limbs[i], carry); ... }
      // Self { limbs }
      var limbs := new Limb[U256_LIMBS][ZeroLimb(), ZeroLimb(), ZeroLimb(), ZeroLimb()];
      var carry := ZeroLimb();
      var i := 0;

      // GHOST CODE
      ghost var fullSum := LimbsSumSpec(this.limbs[..], b.limbs[..], ZeroLimb());

      while i < U256_LIMBS
        invariant 0 <= i <= U256_LIMBS
        invariant carry == ZeroLimb() || carry == LimbFromInt(1)
        invariant limbs[..i] == fullSum[..i]
        invariant carry == LimbsSumSpec(this.limbs[..i], b.limbs[..i], ZeroLimb())[i]
      {
        var w, c := limb_adc(this.limbs[i], b.limbs[i], carry);
        limbs[i] := w;
        carry := c;
        i := i + 1;
      }

      result := new U256(limbs);

      // LEMMAS: carry == fullSum[4] since invariant holds at i==4
      assert carry == fullSum[4];
      assert limbs[..] == fullSum[..4];
      ghost var carryVal := LimbToInt(carry);
      assert 0 <= carryVal <= 1;
      WrappingAddLemma(fullSum, carryVal);
      assert result.ValueSpec() + carryVal * WORD_MODULUS4
        == this.ValueSpec() + b.ValueSpec();
      DropCarryModLemma(result.ValueSpec(), carryVal, this.ValueSpec() + b.ValueSpec());
    }

    // Ported from https://github.com/RustCrypto/crypto-bigint/blob/395bb171178990a93ef571664271dabc50749043/src/uint/shl.rs
    // Shift left by `shift` bits. Currently only shift == 1 is proven.
    method {:rlimit 13995} shl_vartime(shift: nat) returns (result: U256)
      requires this.Valid()
      requires shift == 1
      ensures result.Valid()
      ensures fresh(result.limbs)
      ensures result.ValueSpec() == (this.ValueSpec() * 2) % WORD_MODULUS4
    {
      // original code (shift by 1):
      // result[i] = (self[i] << 1) | (self[i-1] >> 63)
      var limbs := new Limb[U256_LIMBS][ZeroLimb(), ZeroLimb(), ZeroLimb(), ZeroLimb()];

      // First limb: just shift left by 1
      var shifted := (this.limbs[0].word as int * 2) % WORD_MODULUS;
      limbs[0] := LimbFromInt(shifted);

      var i := 1;
      while i < U256_LIMBS
        invariant 1 <= i <= U256_LIMBS
        invariant limbs[0] == LimbFromInt((this.limbs[0].word as int * 2) % WORD_MODULUS)
        invariant forall j :: 1 <= j < i ==>
          limbs[j] == LimbFromInt(
            ((this.limbs[j].word as int * 2) % WORD_MODULUS) +
            (this.limbs[j-1].word as int / (WORD_MODULUS / 2))
          )
      {
        var lo := this.limbs[i].word as int * 2;
        var hi_bit := this.limbs[i-1].word as int / (WORD_MODULUS / 2);
        assert 0 <= hi_bit <= 1;
        limbs[i] := LimbFromInt((lo % WORD_MODULUS) + hi_bit);
        i := i + 1;
      }

      result := new U256(limbs);

      // LEMMAS: prove result == (2 * input) % 2^256
      Shl1Lemma(this.limbs[0], this.limbs[1], this.limbs[2], this.limbs[3],
                 limbs[0], limbs[1], limbs[2], limbs[3]);
    }

    // Specialized from crypto-bigint 0.5.5 Uint::shr_vartime (uint/shr.rs) for shift=1.
    // Right shift by 1 bit.
    method {:rlimit 5076} shr_vartime_1() returns (result: U256)
      requires this.Valid()
      ensures result.Valid()
      ensures fresh(result.limbs)
      ensures result.ValueSpec() == this.ValueSpec() / 2
    {
      var limbs := new Limb[U256_LIMBS](
        _ => ZeroLimb());
      // result[i] = (self[i] >> 1) | (self[i+1] << 63)
      limbs[0] := LimbFromInt(
        this.limbs[0].word as int / 2
        + (this.limbs[1].word as int % 2) * (WORD_MODULUS / 2));
      limbs[1] := LimbFromInt(
        this.limbs[1].word as int / 2
        + (this.limbs[2].word as int % 2) * (WORD_MODULUS / 2));
      limbs[2] := LimbFromInt(
        this.limbs[2].word as int / 2
        + (this.limbs[3].word as int % 2) * (WORD_MODULUS / 2));
      limbs[3] := LimbFromInt(this.limbs[3].word as int / 2);
      result := new U256(limbs);
      Shr1Lemma(
        this.limbs[0], this.limbs[1],
        this.limbs[2], this.limbs[3],
        limbs[0], limbs[1], limbs[2], limbs[3]);
    }

    // Ported from https://github.com/RustCrypto/crypto-bigint/blob/395bb171178990a93ef571664271dabc50749043/src/uint/sub.rs
    // Computes `self - rhs` mod 2^256 (wrapping subtraction)
    method {:rlimit 1933} wrapping_sub(b: U256) returns (result: U256)
      requires this.Valid()
      requires b.Valid()
      ensures result.Valid()
      ensures fresh(result) && fresh(result.limbs)
      ensures result.ValueSpec() == (this.ValueSpec() - b.ValueSpec()) % WORD_MODULUS4
    {
      // Use sbb and drop the borrow
      var diff, borrow := this.sbb(b, ZeroLimb());
      result := diff;

      // LEMMAS
      ghost var d := this.ValueSpec() - b.ValueSpec();
      assert diff.ValueSpec() - (if borrow == ZeroLimb() then 0 else WORD_MODULUS4) == d;
      ghost var borrowVal := if borrow == ZeroLimb() then 0 else 1;
      // When borrowVal==0: result = d (no borrow). When borrowVal==1: result = d + M4.
      assert result.ValueSpec() == d + borrowVal * WORD_MODULUS4;
      DropBorrowModLemma(result.ValueSpec(), borrowVal, d);
    }

    // TCB AXIOM: crypto_bigint 0.5.5 Uint::mul_wide (uint/mul.rs)
    // {:axiom} — library code, no implementation, trusted spec
    method {:rlimit 107} {:axiom} mul_wide(b: U256) returns (result: (U256, U256))
      requires this.Valid()
      requires b.Valid()
      ensures result.0.Valid()
      ensures result.1.Valid()
      ensures fresh(result.0.limbs)
      ensures fresh(result.1.limbs)
      ensures result.0 != result.1 && result.0.limbs != result.1.limbs
      ensures LimbsValueSpec(result.0.limbs[..]) + LimbsValueSpec(result.1.limbs[..]) * WORD_MODULUS4
        == this.ValueSpec() * b.ValueSpec()

    // TCB AXIOM: crypto_bigint 0.5.5 Uint::square (uint/mul.rs)
    // {:axiom} — library code, no implementation, trusted spec
    method {:rlimit 102} {:axiom} square_wide() returns (result: (U256, U256))
      requires this.Valid()
      ensures result.0.Valid()
      ensures result.1.Valid()
      ensures fresh(result.0.limbs)
      ensures fresh(result.1.limbs)
      ensures result.0 != result.1 && result.0.limbs != result.1.limbs
      ensures LimbsValueSpec(result.0.limbs[..]) + LimbsValueSpec(result.1.limbs[..]) * WORD_MODULUS4
        == this.ValueSpec() * this.ValueSpec()

    // =================================================================
    // SPECS
    // =================================================================

    ghost function {:rlimit 1536} {:inline} {:fuel 2} ValueSpec(): int
    reads this
    reads this.limbs
    requires this.Valid()
    ensures 0 <= this.ValueSpec() < WORD_MODULUS4
    {
      LimbsValueSpec(this.limbs[..])
    }

    // =================================================================
    // LEMMAS
    // =================================================================
  }

  // ===================================================================
  // HELPER FUNCTIONS
  // ===================================================================

  method {:rlimit 109} U256_Zero() returns (zero: U256)
    ensures zero.limbs[..] == [ZeroLimb(), ZeroLimb(), ZeroLimb(), ZeroLimb()]
    ensures zero.Valid()
    ensures fresh(zero)
    ensures fresh(zero.limbs)
  {
    var limbs: array<Limb> := new Limb[U256_LIMBS][ZeroLimb(), ZeroLimb(), ZeroLimb(), ZeroLimb()];
    zero := new U256(limbs);
  }

  // ===================================================================
  // LEMMAS
  // ===================================================================

  // If result + carry * M == total, and 0 <= result < M, and carry is 0 or 1,
  // then result == total % M
  lemma {:rlimit 161} DropCarryModLemma(result: int, carry: int, total: int)
    requires 0 <= result < WORD_MODULUS4
    requires 0 <= carry <= 1
    requires result + carry * WORD_MODULUS4 == total
    ensures result == total % WORD_MODULUS4
  {
    if carry == 0 {
      assert result == total;
      assert 0 <= total < WORD_MODULUS4;
    } else {
      assert result == total - WORD_MODULUS4;
      assert WORD_MODULUS4 <= total < 2 * WORD_MODULUS4;
    }
  }

  // For wrapping_sub: if result = d + borrowVal * M4 and 0 <= result < M4
  // and borrowVal is 0 or 1, then result == d % M4
  lemma {:rlimit 167} DropBorrowModLemma(result: int, borrowVal: int, d: int)
    requires 0 <= result < WORD_MODULUS4
    requires 0 <= borrowVal <= 1
    requires result == d + borrowVal * WORD_MODULUS4
    ensures result == d % WORD_MODULUS4
  {
    if borrowVal == 0 {
      assert result == d;
      assert 0 <= d < WORD_MODULUS4;
    } else {
      assert result == d + WORD_MODULUS4;
      assert -WORD_MODULUS4 <= d < 0;
    }
  }

  // LimbsSumSpec of 4 limbs produces 5 elements; the first 4 are the sum, the 5th is carry.
  // LimbsValueSpec of first 4 + carry * WORD_MODULUS4 == LimbsValueSpec of all 5
  lemma {:rlimit 1668} WrappingAddLemma(fullSum: seq<Limb>, carryVal: int)
    requires |fullSum| == 5
    requires carryVal == LimbToInt(fullSum[4])
    requires 0 <= carryVal <= 1
    ensures LimbsValueSpec(fullSum[..4]) + carryVal * WORD_MODULUS4 == LimbsValueSpec(fullSum)
  {
    assert fullSum[..4] == [fullSum[0], fullSum[1], fullSum[2], fullSum[3]];
  }

  lemma {:rlimit 194} LimbsSumSnocLemma(prefixLhs: seq<Limb>, prefixRhs: seq<Limb>, carryIn: Limb, lastLhs: Limb, lastRhs: Limb)
    requires |prefixLhs| == |prefixRhs|
    requires carryIn == ZeroLimb() || carryIn == LimbFromInt(1)
    ensures LimbsSumSpec(prefixLhs + [lastLhs], prefixRhs + [lastRhs], carryIn)
      == LimbsSumSpec(prefixLhs, prefixRhs, carryIn)[..|prefixLhs|]
        + [AddAndCarryLimbSpec(lastLhs, lastRhs, LimbsSumSpec(prefixLhs, prefixRhs, carryIn)[|prefixLhs|]).0,
           AddAndCarryLimbSpec(lastLhs, lastRhs, LimbsSumSpec(prefixLhs, prefixRhs, carryIn)[|prefixLhs|]).1]
  {
  }

  lemma {:rlimit 158} LimbsSumStepLemma(
    prefixLhs: seq<Limb>,
    prefixRhs: seq<Limb>,
    carryIn: Limb,
    lastLhs: Limb,
    lastRhs: Limb,
    limbsPrefix: seq<Limb>,
    carry: Limb,
    w: Limb,
    cNew: Limb
  )
    requires |prefixLhs| == |prefixRhs|
    requires carryIn == ZeroLimb() || carryIn == LimbFromInt(1)
    requires limbsPrefix == LimbsSumSpec(prefixLhs, prefixRhs, carryIn)[..|prefixLhs|]
    requires carry == LimbsSumSpec(prefixLhs, prefixRhs, carryIn)[|prefixLhs|]
    requires w == AddAndCarryLimbSpec(lastLhs, lastRhs, LimbsSumSpec(prefixLhs, prefixRhs, carryIn)[|prefixLhs|]).0
    requires cNew == AddAndCarryLimbSpec(lastLhs, lastRhs, LimbsSumSpec(prefixLhs, prefixRhs, carryIn)[|prefixLhs|]).1
    ensures LimbsSumSpec(prefixLhs + [lastLhs], prefixRhs + [lastRhs], carryIn)
      == limbsPrefix + [w, cNew]
  {
    LimbsSumSnocLemma(prefixLhs, prefixRhs, carryIn, lastLhs, lastRhs);
  }

  lemma {:rlimit 155} LimbsDiffStepLemma(
    prefixLhs: seq<Limb>,
    prefixRhs: seq<Limb>,
    borrowIn: Limb,
    lastLhs: Limb,
    lastRhs: Limb,
    limbsPrefix: seq<Limb>,
    borrow: Limb,
    w: Limb,
    b: Limb
  )
    requires |prefixLhs| == |prefixRhs|
    requires borrowIn == ZeroLimb() || borrowIn == MaxLimb()
    requires limbsPrefix == LimbsDiffSpec(prefixLhs, prefixRhs, borrowIn)[..|prefixLhs|]
    requires borrow == LimbsDiffSpec(prefixLhs, prefixRhs, borrowIn)[|prefixLhs|]
    requires w == SubAndBorrowLimbSpec(lastLhs, lastRhs, LimbsDiffSpec(prefixLhs, prefixRhs, borrowIn)[|prefixLhs|]).0
    requires b == SubAndBorrowLimbSpec(lastLhs, lastRhs, LimbsDiffSpec(prefixLhs, prefixRhs, borrowIn)[|prefixLhs|]).1
    ensures LimbsDiffSpec(prefixLhs + [lastLhs], prefixRhs + [lastRhs], borrowIn)
      == limbsPrefix + [w, b]
  {
    LimbsDiffSnocLemma(prefixLhs, prefixRhs, borrowIn, lastLhs, lastRhs);
  }

  lemma {:rlimit 342} LimbsDiffSnocLemma(prefixLhs: seq<Limb>, prefixRhs: seq<Limb>, borrowIn: Limb, lastLhs: Limb, lastRhs: Limb)
    requires |prefixLhs| == |prefixRhs|
    requires borrowIn == ZeroLimb() || borrowIn == MaxLimb()
    ensures LimbsDiffSpec(prefixLhs + [lastLhs], prefixRhs + [lastRhs], borrowIn)
      == LimbsDiffSpec(prefixLhs, prefixRhs, borrowIn)[..|prefixLhs|]
        + [SubAndBorrowLimbSpec(lastLhs, lastRhs, LimbsDiffSpec(prefixLhs, prefixRhs, borrowIn)[|prefixLhs|]).0,
           SubAndBorrowLimbSpec(lastLhs, lastRhs, LimbsDiffSpec(prefixLhs, prefixRhs, borrowIn)[|prefixLhs|]).1]
  {
  }

  // 4-limb subtraction chain via sub_with_bounded_overflow.
  // Telescopes to: d_val == a_val - b_val + final_borrow * 2^256.
  // Establishes: final_borrow == 1 ↔ a_val < b_val.
  // Used by invert_step_ct to connect limb-level operations to ValueSpec.
  lemma {:rlimit 4892} SubBoundedChain4Lemma(
    a0: Limb, a1: Limb, a2: Limb, a3: Limb,
    b0: Limb, b1: Limb, b2: Limb, b3: Limb
  )
    ensures
      var (d0, c0) := SubBoundedSpec(a0, b0, ZeroLimb());
      var (d1, c1) := SubBoundedSpec(a1, b1, c0);
      var (d2, c2) := SubBoundedSpec(a2, b2, c1);
      var (d3, c3) := SubBoundedSpec(a3, b3, c2);
      var a_val := LimbToInt(a0) + LimbToInt(a1) * WORD_MODULUS
        + LimbToInt(a2) * WORD_MODULUS2
        + LimbToInt(a3) * WORD_MODULUS3;
      var b_val := LimbToInt(b0) + LimbToInt(b1) * WORD_MODULUS
        + LimbToInt(b2) * WORD_MODULUS2
        + LimbToInt(b3) * WORD_MODULUS3;
      var d_val := LimbToInt(d0) + LimbToInt(d1) * WORD_MODULUS
        + LimbToInt(d2) * WORD_MODULUS2
        + LimbToInt(d3) * WORD_MODULUS3;
      && d_val == a_val - b_val
        + (c3.word as int) * WORD_MODULUS4
      && (c3.word as int == 0 || c3.word as int == 1)
      && (c3.word as int == 1 <==> a_val < b_val)
  {
    SubBoundedSpecLemma(a0, b0, ZeroLimb());
    var (d0, c0) := SubBoundedSpec(a0, b0, ZeroLimb());
    SubBoundedSpecLemma(a1, b1, c0);
    var (d1, c1) := SubBoundedSpec(a1, b1, c0);
    SubBoundedSpecLemma(a2, b2, c1);
    var (d2, c2) := SubBoundedSpec(a2, b2, c1);
    SubBoundedSpecLemma(a3, b3, c2);
    var (d3, c3) := SubBoundedSpec(a3, b3, c2);

    ghost var a_val := LimbToInt(a0) + LimbToInt(a1) * WORD_MODULUS
      + LimbToInt(a2) * WORD_MODULUS2
      + LimbToInt(a3) * WORD_MODULUS3;
    ghost var b_val := LimbToInt(b0) + LimbToInt(b1) * WORD_MODULUS
      + LimbToInt(b2) * WORD_MODULUS2
      + LimbToInt(b3) * WORD_MODULUS3;
    ghost var d_val := LimbToInt(d0) + LimbToInt(d1) * WORD_MODULUS
      + LimbToInt(d2) * WORD_MODULUS2
      + LimbToInt(d3) * WORD_MODULUS3;

    // Telescoping from SubBoundedSpecLemma:
    //   d_i = a_i - b_i - c_{i-1} + c_i * W
    // Sum with weights W^i cancels all intermediate borrows.
    assert WORD_MODULUS2 == WORD_MODULUS * WORD_MODULUS;
    assert WORD_MODULUS3 == WORD_MODULUS2 * WORD_MODULUS;
    assert WORD_MODULUS4 == WORD_MODULUS2 * WORD_MODULUS2;

    // a < b ↔ a - b < 0 ↔ borrow needed
    assert 0 <= d_val < WORD_MODULUS4;
    assert 0 <= a_val < WORD_MODULUS4;
    assert 0 <= b_val < WORD_MODULUS4;
  }

  // wrapping_neg converts sub_with_bounded_overflow borrow {0,1} to mask {0,MAX}.
  // Needed by invert_step_ct to convert borrow to a_lt_b mask.
  lemma {:rlimit 543} WrappingNegBorrowLemma(borrow: Limb)
    requires borrow == ZeroLimb() || borrow == LimbFromInt(1)
    ensures wrapping_neg(borrow) == ZeroLimb()
      || wrapping_neg(borrow) == MaxLimb()
    ensures borrow == ZeroLimb() ==>
      wrapping_neg(borrow) == ZeroLimb()
    ensures borrow == LimbFromInt(1) ==>
      wrapping_neg(borrow) == MaxLimb()
  {}

  lemma {:rlimit 1418354} Shl1Lemma(
    a0: Limb, a1: Limb, a2: Limb, a3: Limb,
    r0: Limb, r1: Limb, r2: Limb, r3: Limb
  )
    requires r0 == LimbFromInt((a0.word as int * 2) % WORD_MODULUS)
    requires r1 == LimbFromInt(((a1.word as int * 2) % WORD_MODULUS) + (a0.word as int / (WORD_MODULUS / 2)))
    requires r2 == LimbFromInt(((a2.word as int * 2) % WORD_MODULUS) + (a1.word as int / (WORD_MODULUS / 2)))
    requires r3 == LimbFromInt(((a3.word as int * 2) % WORD_MODULUS) + (a2.word as int / (WORD_MODULUS / 2)))
    ensures LimbsValueSpec([r0, r1, r2, r3]) == (LimbsValueSpec([a0, a1, a2, a3]) * 2) % WORD_MODULUS4
  {
    ghost var a0v := a0.word as int;
    ghost var a1v := a1.word as int;
    ghost var a2v := a2.word as int;
    ghost var a3v := a3.word as int;

    // Key identity: for 0 <= x < M, (2*x) % M = 2*x - (x / (M/2)) * M
    assert (a0v * 2) % WORD_MODULUS == a0v * 2 - (a0v / (WORD_MODULUS / 2)) * WORD_MODULUS;
    assert (a1v * 2) % WORD_MODULUS == a1v * 2 - (a1v / (WORD_MODULUS / 2)) * WORD_MODULUS;
    assert (a2v * 2) % WORD_MODULUS == a2v * 2 - (a2v / (WORD_MODULUS / 2)) * WORD_MODULUS;
    assert (a3v * 2) % WORD_MODULUS == a3v * 2 - (a3v / (WORD_MODULUS / 2)) * WORD_MODULUS;

    ghost var dropped := a3v / (WORD_MODULUS / 2);
    assert 0 <= dropped <= 1;

    ghost var a := LimbsValueSpec([a0, a1, a2, a3]);
    ghost var r := LimbsValueSpec([r0, r1, r2, r3]);
    assert r == 2 * a - dropped * WORD_MODULUS4;
    DropCarryModLemma(r, dropped, 2 * a);
  }

  lemma {:rlimit 1605305} Shr1Lemma(
    a0: Limb, a1: Limb, a2: Limb, a3: Limb,
    r0: Limb, r1: Limb, r2: Limb, r3: Limb
  )
    requires r0 == LimbFromInt(
      a0.word as int / 2 + (a1.word as int % 2) * (WORD_MODULUS / 2))
    requires r1 == LimbFromInt(
      a1.word as int / 2 + (a2.word as int % 2) * (WORD_MODULUS / 2))
    requires r2 == LimbFromInt(
      a2.word as int / 2 + (a3.word as int % 2) * (WORD_MODULUS / 2))
    requires r3 == LimbFromInt(a3.word as int / 2)
    ensures LimbsValueSpec([r0, r1, r2, r3])
         == LimbsValueSpec([a0, a1, a2, a3]) / 2
  {
    ghost var a0v := a0.word as int;
    ghost var a1v := a1.word as int;
    ghost var a2v := a2.word as int;
    ghost var a3v := a3.word as int;
    ghost var a := LimbsValueSpec([a0, a1, a2, a3]);
    ghost var r := LimbsValueSpec([r0, r1, r2, r3]);
    // r = a0/2 + (a1%2)*(W/2)
    //   + (a1/2 + (a2%2)*(W/2))*W
    //   + (a2/2 + (a3%2)*(W/2))*W^2
    //   + (a3/2)*W^3
    // = a0/2 + a1*W/2 + a2*W^2/2 + a3*W^3/2
    // = (a0 + a1*W + a2*W^2 + a3*W^3) / 2
    // = a / 2
    assert r == a0v / 2 + (a1v % 2) * (WORD_MODULUS / 2)
      + (a1v / 2 + (a2v % 2) * (WORD_MODULUS / 2)) * WORD_MODULUS
      + (a2v / 2 + (a3v % 2) * (WORD_MODULUS / 2)) * WORD_MODULUS2
      + (a3v / 2) * WORD_MODULUS3;
    // Key: x%2 * (W/2) + (x/2)*W = (x%2)*(W/2) + (x/2)*W
    //    = x/2 * W + (x%2)*(W/2) = (2*(x/2) + x%2)*(W/2) = x*(W/2)
    assert (a1v % 2) * (WORD_MODULUS / 2) + (a1v / 2) * WORD_MODULUS
        == a1v * (WORD_MODULUS / 2);
    assert (a2v % 2) * (WORD_MODULUS / 2) + (a2v / 2) * WORD_MODULUS
        == a2v * (WORD_MODULUS / 2);
    assert (a3v % 2) * (WORD_MODULUS / 2) + (a3v / 2) * WORD_MODULUS
        == a3v * (WORD_MODULUS / 2);
    assert WORD_MODULUS / 2 * WORD_MODULUS == WORD_MODULUS2 / 2;
    assert WORD_MODULUS / 2 * WORD_MODULUS2 == WORD_MODULUS3 / 2;
    assert WORD_MODULUS / 2 * WORD_MODULUS3 == WORD_MODULUS4 / 2;
    assert r == a / 2;
  }
}
