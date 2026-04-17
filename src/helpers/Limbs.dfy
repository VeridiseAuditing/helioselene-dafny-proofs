include "../crypto_bigint_0_5_5/Limb.dfy"

module Limbs {
  import opened CryptoBigint_0_5_5_Limb
  import Power = Std.Arithmetic.Power

  const WORD_MODULUS2: int := WORD_MODULUS * WORD_MODULUS
  const WORD_MODULUS3: int := WORD_MODULUS2 * WORD_MODULUS
  const WORD_MODULUS4: int := WORD_MODULUS2 * WORD_MODULUS2
  const WORD_MODULUS5: int := WORD_MODULUS4 * WORD_MODULUS
  const WORD_MODULUS6: int := WORD_MODULUS4 * WORD_MODULUS2
  const WORD_MODULUS7: int := WORD_MODULUS4 * WORD_MODULUS3

  // ===================================================================
  // PORTED IMPLS
  // ===================================================================

  method {:rlimit 279} copy_from_slice(self: array<Limb>, src: seq<Limb>, start: int, stop: int)
    requires 0 <= start <= stop <= self.Length
    requires stop - start == |src|
    modifies self
    ensures self[start..stop] == src[..]
    ensures self[..start] == old(self[..start])
    ensures stop == self.Length || self[stop..] == old(self[stop..])
  {
    for i:int := 0 to stop - start
      invariant 0 <= i <= stop - start
      invariant self[start..start + i] == src[..i]
      invariant self[..start] == old(self[..start])
      invariant self[stop..] == old(self[stop..])
      modifies self
    {
      self[start + i] := src[i];
    }
  }

  // ===================================================================
  // SPECS
  // ===================================================================

  function {:rlimit 50} {:fuel 5} LimbsValueSpec(limbs: seq<Limb>): int
  {
      if |limbs| == 0 then 0 else
        LimbToInt(limbs[0]) + LimbsValueSpec(limbs[1..]) * WORD_MODULUS
  }

  // convenience function for computing LimbsValueSpec from the last limb, rather
  // than from the first
  ghost function {:rlimit 121} LimbsValueSpecBackward(limbs: seq<Limb>): int
    ensures LimbsValueSpec(limbs) == LimbsValueSpecBackward(limbs)
  {
      if |limbs| == 0 then
        0
      else
        var head := limbs[..|limbs| - 1];
        var tail := LimbToInt(limbs[|limbs| - 1]);
        var result := LimbsValueSpecBackward(head) + Power.Pow(WORD_MODULUS, |limbs| - 1) * tail;

        assert result == LimbsValueSpec(limbs) by {
          assert LimbsValueSpecBackward(head) == LimbsValueSpec(head);
          assert LimbsValueSpec(limbs) == LimbsValueSpec(head) + tail * Power.Pow(WORD_MODULUS, |limbs|-1) by
          {
            LimbsValueSpecLastLimbLemma(limbs);
          }
        }

        result
  }

  ghost function {:rlimit 67303} BorrowValue(borrow: Limb, exp: nat): int
    requires borrow == ZeroLimb() || borrow == MaxLimb()
  {
    if borrow == ZeroLimb() then 0 else Power.Pow(WORD_MODULUS, exp)
  }

  ghost function {:rlimit 1763} {:induction lhs,rhs} LimbsSumSpec(lhs: seq<Limb>, rhs: seq<Limb>, carryIn: Limb): (sumAndCarry: seq<Limb>)
  requires |lhs| == |rhs|
  requires carryIn.word as int == 0 || carryIn.word as int == 1
  ensures |sumAndCarry| == |lhs| + 1
  ensures LimbsValueSpec(sumAndCarry) == LimbToInt(carryIn) + LimbsValueSpec(lhs) + LimbsValueSpec(rhs)
  ensures sumAndCarry[|lhs|] == ZeroLimb() || sumAndCarry[|lhs|] == LimbFromInt(1)
  {
    if |lhs| == 0 then
      [carryIn]
    else
      var head := LimbsSumSpec(lhs[..|lhs| - 1], rhs[..|lhs| - 1], carryIn);
      var lastSumAndCarry := AddAndCarryLimbSpec(lhs[|lhs| - 1], rhs[|lhs| - 1], head[|lhs| - 1]);
      var result := head[..|lhs|-1] + [lastSumAndCarry.0, lastSumAndCarry.1];

      LinearOverHeadAndTailImpliesLinearOverValues(
          lhs,
          1,
          rhs,
          LimbToInt(carryIn),
          head,
          lastSumAndCarry.0,
          lastSumAndCarry.1
      );

      result
  }

  ghost function {:rlimit 67303} {:induction lhs,rhs} LimbsDiffSpec(lhs: seq<Limb>, rhs: seq<Limb>, borrowIn: Limb): (diffsAndBorrow: seq<Limb>)
  requires |lhs| == |rhs|
  requires borrowIn == ZeroLimb() || borrowIn == MaxLimb()
  ensures |lhs| + 1 == |diffsAndBorrow|
  ensures diffsAndBorrow[|lhs|] == ZeroLimb() || diffsAndBorrow[|lhs|] == MaxLimb()
  ensures
    LimbsValueSpec(diffsAndBorrow[..|lhs|])
    - (if diffsAndBorrow[|lhs|] == ZeroLimb() then 0 else
        Power.Pow(WORD_MODULUS, |lhs|)
      )
    ==
    LimbsValueSpec(lhs) - (LimbsValueSpec(rhs) + (if borrowIn == ZeroLimb() then 0 else 1))
  {
    if |lhs| == 0 then
      [borrowIn]
    else
      var head := LimbsDiffSpec(lhs[0..|lhs| - 1], rhs[0..|lhs| - 1], borrowIn);
      var headBorrow := head[|lhs| - 1];
      var diffAndBorrow := SubAndBorrowLimbSpec(lhs[|lhs| - 1], rhs[|lhs| - 1], headBorrow);
      var result := head[..|lhs| - 1] + [diffAndBorrow.0, diffAndBorrow.1];

      ghost var result_borrow := BorrowValue(result[|lhs|], |lhs|);
      ghost var result_value_without_borrow := LimbsValueSpec(result[..|lhs|]);
      ghost var result_value := result_value_without_borrow - result_borrow;
      ghost var head_borrow := BorrowValue(headBorrow, |lhs| - 1);
      ghost var head_value_without_borrow := LimbsValueSpec(head[..|lhs| - 1]);
      ghost var head_value := head_value_without_borrow - head_borrow;

      assert result[..|lhs|] == head[..|lhs| - 1] + [diffAndBorrow.0];
      LimbsValueSpecLastLimbLemma(result[..|lhs|]);

      assert result_value_without_borrow
        == head_value_without_borrow + LimbToInt(diffAndBorrow.0) * Power.Pow(WORD_MODULUS, |lhs| - 1);

      assert LimbToInt(diffAndBorrow.0)
        == LimbToInt(lhs[|lhs| - 1])
        - (LimbToInt(rhs[|lhs| - 1]) + (if headBorrow == ZeroLimb() then 0 else 1))
        + (if diffAndBorrow.1 == ZeroLimb() then 0 else WORD_MODULUS)
        ;

      assert result_value_without_borrow
        == head_value_without_borrow +
        (
          LimbToInt(lhs[|lhs| - 1])
          - (LimbToInt(rhs[|lhs| - 1]) + (if headBorrow == ZeroLimb() then 0 else 1))
          + (if diffAndBorrow.1 == ZeroLimb() then 0 else WORD_MODULUS)
        ) * Power.Pow(WORD_MODULUS, |lhs| - 1);

      assert result_value_without_borrow
        == head_value_without_borrow +
          LimbToInt(lhs[|lhs| - 1]) * Power.Pow(WORD_MODULUS, |lhs| - 1)
          - LimbToInt(rhs[|lhs| - 1]) * Power.Pow(WORD_MODULUS, |lhs| - 1)
          - (if headBorrow == ZeroLimb() then 0 else 1) * Power.Pow(WORD_MODULUS, |lhs| - 1)
          + (if diffAndBorrow.1 == ZeroLimb() then 0 else WORD_MODULUS) * Power.Pow(WORD_MODULUS, |lhs| - 1);

      assert (if headBorrow == ZeroLimb() then 0 else 1) * Power.Pow(WORD_MODULUS, |lhs| - 1) == head_borrow;

      assert result_value_without_borrow
        == head_value +
          LimbToInt(lhs[|lhs| - 1]) * Power.Pow(WORD_MODULUS, |lhs| - 1)
          - LimbToInt(rhs[|lhs| - 1]) * Power.Pow(WORD_MODULUS, |lhs| - 1)
          + (if diffAndBorrow.1 == ZeroLimb() then 0 else WORD_MODULUS) * Power.Pow(WORD_MODULUS, |lhs| - 1);

      LimbsValueSpecLastLimbLemma(lhs);
      LimbsValueSpecLastLimbLemma(rhs);

      result
  }

  // Like LimbsSumSpec/LimbsDiffSpec, but for a chained multiply-add-carry pattern.
  // Uses forward induction which aligns with LimbsValueSpec definition:
  // LimbsValueSpec(s) = s[0] + LimbsValueSpec(s[1..]) * WORD_MODULUS
  ghost function {:rlimit 26440} LimbsMacSpec(
    lhs: seq<Limb>,
    high: Limb,
    coeffs: seq<Limb>,
    carryIn: Limb
  ): (macAndCarry: seq<Limb>)
    requires |lhs| == |coeffs|
    ensures |macAndCarry| == |lhs| + 1
    ensures LimbsValueSpec(macAndCarry)
      == LimbsValueSpec(lhs) + LimbToInt(high) * LimbsValueSpec(coeffs) + LimbToInt(carryIn)
    decreases |lhs|
  {
    if |lhs| == 0 then
      [carryIn]
    else
      var macVal := LimbToInt(lhs[0])
        + LimbToInt(high) * LimbToInt(coeffs[0])
        + LimbToInt(carryIn);
      MacStepBoundLemma(
        LimbToInt(lhs[0]), LimbToInt(high),
        LimbToInt(coeffs[0]), LimbToInt(carryIn));
      var low := LimbFromInt(macVal % WORD_MODULUS);
      var carry := LimbFromInt(macVal / WORD_MODULUS);
      var tail := LimbsMacSpec(lhs[1..], high, coeffs[1..], carry);

      // IH: LimbsValueSpec(tail) == LimbsValueSpec(lhs[1..]) + high*LimbsValueSpec(coeffs[1..]) + macVal/W
      var result := [low] + tail;

      // LimbsValueSpec(result) = LimbToInt(low) + LimbsValueSpec(tail) * W
      //   = macVal%W + (LimbsValueSpec(lhs[1..]) + high*LimbsValueSpec(coeffs[1..]) + macVal/W) * W
      // Need: macVal%W + (macVal/W)*W = macVal
      // Then: = macVal + (LimbsValueSpec(lhs[1..]) + high*LimbsValueSpec(coeffs[1..]))*W
      //   = lhs[0] + high*coeffs[0] + carryIn + LimbsValueSpec(lhs[1..])*W + high*LimbsValueSpec(coeffs[1..])*W
      //   = LimbsValueSpec(lhs) + high*(coeffs[0] + LimbsValueSpec(coeffs[1..])*W) + carryIn
      //   = LimbsValueSpec(lhs) + high*LimbsValueSpec(coeffs) + carryIn
      assert macVal % WORD_MODULUS + (macVal / WORD_MODULUS) * WORD_MODULUS == macVal;
      MulDistributesOverAddLemma(
        LimbToInt(high),
        LimbToInt(coeffs[0]),
        LimbsValueSpec(coeffs[1..]) * WORD_MODULUS);

      result
  }

  // Spec for inner loop of mac: multiply one sequence of limbs by a single limb,
  // then add them to another sequence of limbs
  //
  // i.e. computes lhs + scale * coeffs + carryIn
  //
  // where scale, carryIn are individual limbs
  ghost function {:rlimit 151} {:isolate_assertions}  LimbsMultiplyLimbAndAddSpec(
    lhs: seq<Limb>,
    scale: Limb,
    rhs: seq<Limb>,
    carryIn: Limb
  ): (macAndCarry: seq<Limb>)
    requires |lhs| == |rhs|
    ensures |macAndCarry| == |lhs| + 1
    ensures LimbsValueSpec(macAndCarry)
      == LimbsValueSpec(lhs) + LimbToInt(scale) * LimbsValueSpec(rhs) + LimbToInt(carryIn)
    decreases |lhs|
  {
    if |lhs| == 0 then
      [carryIn]
    else
      var headLhs := lhs[..|lhs| - 1];
      var tailLhs := lhs[|lhs| - 1];
      var headRhs := rhs[..|rhs| - 1];
      var tailRhs := rhs[|rhs| - 1];

      var headSum := LimbsMultiplyLimbAndAddSpec(headLhs, scale, headRhs, carryIn);
      var headResult := headSum[..|headSum| - 1];
      var carryOut := headSum[|headSum| - 1];

      var macVal := LimbToInt(tailLhs) + LimbToInt(scale) * LimbToInt(tailRhs) + LimbToInt(carryOut);
      assert 0 <= macVal / WORD_MODULUS < WORD_MODULUS by {
        MacStepBoundLemma(LimbToInt(tailLhs), LimbToInt(scale), LimbToInt(tailRhs), LimbToInt(carryOut));
      }
      var tailResult := [LimbFromInt(macVal % WORD_MODULUS), LimbFromInt(macVal / WORD_MODULUS)];

      var result := headResult + tailResult;

      LinearOverHeadAndTailImpliesLinearOverValues(
          lhs,
          LimbToInt(scale),
          rhs,
          LimbToInt(carryIn),
          headSum,
          LimbFromInt(macVal % WORD_MODULUS),
          LimbFromInt(macVal / WORD_MODULUS)
      );

      result
  }

  // ===================================================================
  // LEMMAS
  // ===================================================================

  lemma {:rlimit 87} PowerPlusPowerPlusOneLemma(c1: int, c2: int, base: nat, exp: nat)
    ensures c1 * Power.Pow(base, exp) + c2 * Power.Pow(base, exp + 1)
      == (c1 + c2 * base) * Power.Pow(base, exp)
  {
    var powExp := Power.Pow(base, exp);
    assert Power.Pow(base, exp + 1) == base * Power.Pow(base, exp);
    assert c1 * Power.Pow(base, exp) + c2 * Power.Pow(base, exp + 1)
      == c1 * powExp + c2 * base * powExp;
    assert c1 * powExp + c2 * base* powExp
      == (c1) * powExp + (c2 * base) * powExp;
    assert c1 * powExp + c2 * base * powExp
      == (c1 + c2 * base) * powExp;
  }

  lemma {:rlimit 18} MulDistributesOverAddLemma(a: int, b: int, c: int)
    ensures a * (b + c) == a * b + a * c
  {}

  // Proves that a + b*c + carry fits in 2 Limbs
  lemma {:rlimit 23} MulMonotoneLemma(a: int, b: int, c: int, d: int)
    requires 0 <= a <= c
    requires 0 <= b <= d
    ensures a * b <= c * d
  {}

  lemma {:rlimit 48} MacStepBoundLemma(a: int, b: int, c: int, carry: int)
    requires 0 <= a < WORD_MODULUS
    requires 0 <= b < WORD_MODULUS
    requires 0 <= c < WORD_MODULUS
    requires 0 <= carry < WORD_MODULUS
    ensures 0 <= a + b * c + carry < WORD_MODULUS * WORD_MODULUS
    ensures 0 <= (a + b * c + carry) / WORD_MODULUS < WORD_MODULUS
  {
    MulMonotoneLemma(0, 0, b, c);
    assert b * c >= 0;
    MulMonotoneLemma(b, c, WORD_MODULUS - 1, WORD_MODULUS - 1);
    assert b * c <= (WORD_MODULUS - 1) * (WORD_MODULUS - 1);
    assert a + b * c + carry
      <= (WORD_MODULUS - 1) + (WORD_MODULUS - 1) * (WORD_MODULUS - 1) + (WORD_MODULUS - 1);
    // (W-1)^2 + 2(W-1) = W^2 - 2W + 1 + 2W - 2 = W^2 - 1
    assert (WORD_MODULUS - 1) * (WORD_MODULUS - 1) + 2 * (WORD_MODULUS - 1)
      == WORD_MODULUS * WORD_MODULUS - 1;
  }

  // Technical helper lemma for the inductive step applying linear relations
  // over limbs to linear relations over values
  lemma {:rlimit 17354} {:isolate_assertions} LinearOverHeadAndTailImpliesLinearOverValues(
      lhs: seq<Limb>,
      rhsCoeff: int,
      rhs: seq<Limb>,
      constant: int,
      resultHead: seq<Limb>,
      resultTail0: Limb,
      resultTail1: Limb
    )
    requires |lhs| == |rhs|
    requires |lhs| == |resultHead|
    requires |lhs| >= 1
    requires
      var lhsHead := lhs[..|lhs| - 1];
      var rhsHead := rhs[..|rhs| - 1];
      LimbsValueSpec(lhsHead) + rhsCoeff * LimbsValueSpec(rhsHead) + constant == LimbsValueSpec(resultHead)
    requires
      var lhsTail := LimbToInt(lhs[|lhs| - 1]);
      var rhsTail := LimbToInt(rhs[|rhs| - 1]);
      var carryIn := LimbToInt(resultHead[|resultHead| - 1]);
      lhsTail + rhsCoeff * rhsTail + carryIn == LimbToInt(resultTail0) + LimbToInt(resultTail1) * WORD_MODULUS
    ensures
      var result := resultHead[..|resultHead| - 1] + [resultTail0, resultTail1];
      LimbsValueSpec(lhs) + rhsCoeff * LimbsValueSpec(rhs) + constant == LimbsValueSpec(result)
  {
    var lhsHead := lhs[..|lhs| - 1];
    var rhsHead := rhs[..|rhs| - 1];
    var lhsTail := LimbToInt(lhs[|lhs| - 1]);
    var rhsTail := LimbToInt(rhs[|rhs| - 1]);
    var carryIn := LimbToInt(resultHead[|resultHead| - 1]);
    var result := resultHead[..|resultHead| - 1] + [resultTail0, resultTail1];

    var tailPow := Power.Pow(WORD_MODULUS, |lhs| - 1);

    assert LimbsValueSpec(lhs) + rhsCoeff * LimbsValueSpec(rhs) + constant == LimbsValueSpec(result) by
    {
      assert LimbsValueSpec(lhs) == LimbsValueSpecBackward(lhs);
      assert LimbsValueSpec(rhs) == LimbsValueSpecBackward(rhs);
      assert LimbsValueSpec(result) == LimbsValueSpecBackward(result);
      assert LimbsValueSpecBackward(lhs) + rhsCoeff * LimbsValueSpecBackward(rhs) + constant == LimbsValueSpecBackward(result) by
      {
        assert LimbsValueSpecBackward(lhs) + rhsCoeff * LimbsValueSpecBackward(rhs) + constant
          ==
          (LimbsValueSpecBackward(lhsHead) +
          lhsTail * tailPow) +
          rhsCoeff * (
            LimbsValueSpecBackward(rhsHead) +
            rhsTail * tailPow
          ) + constant by
        {
          assert LimbsValueSpecBackward(lhs) == (LimbsValueSpecBackward(lhsHead) + lhsTail * tailPow) by {
            LimbsValueSpecBackwardLemma(lhs);
          }
          assert LimbsValueSpecBackward(rhs) == (LimbsValueSpecBackward(rhsHead) + rhsTail * tailPow) by {
            LimbsValueSpecBackwardLemma(rhs);
          }
        }
        assert LimbsValueSpecBackward(lhs) + rhsCoeff * LimbsValueSpecBackward(rhs) + constant
          ==
          LimbsValueSpec(lhsHead) +
          rhsCoeff * LimbsValueSpec(rhsHead) +
          (lhsTail + rhsCoeff * rhsTail) * tailPow +
          constant by
        {
          LinearOverHeadAndTailImpliesLinearOverValues_Helper0(
            LimbsValueSpec(lhsHead),
            lhsTail,
            rhsCoeff,
            LimbsValueSpec(rhsHead),
            rhsTail,
            constant,
            |lhs| - 1
          );
        }

        assert LimbsValueSpecBackward(lhs) + rhsCoeff * LimbsValueSpecBackward(rhs) + constant
          ==
          LimbsValueSpecBackward(resultHead) +
          (lhsTail + rhsCoeff * rhsTail) * tailPow;

        assert LimbsValueSpecBackward(lhs) + rhsCoeff * LimbsValueSpecBackward(rhs) + constant
          ==
          LimbsValueSpecBackward(resultHead[..|resultHead| - 1]) +
          carryIn * tailPow +
          (lhsTail + rhsCoeff * rhsTail) * tailPow;

        assert LimbsValueSpecBackward(lhs) + rhsCoeff * LimbsValueSpecBackward(rhs) + constant
          ==
          LimbsValueSpecBackward(resultHead[..|resultHead| - 1]) +
          (lhsTail + rhsCoeff * rhsTail + carryIn) * tailPow by
        {
          LinearOverHeadAndTailImpliesLinearOverValues_Helper1(
            lhsTail, rhsCoeff, rhsTail, carryIn, tailPow
          );
        }

        assert LimbsValueSpecBackward(lhs) + rhsCoeff * LimbsValueSpecBackward(rhs) + constant
          ==
          LimbsValueSpecBackward(result[..|result| - 2]) +
          (LimbToInt(resultTail0 )+ LimbToInt(resultTail1) * WORD_MODULUS) * tailPow;

        assert LimbsValueSpecBackward(lhs) + rhsCoeff * LimbsValueSpecBackward(rhs) + constant
          ==
          LimbsValueSpecBackward(result[..|result| - 2]) +
          LimbToInt(resultTail0) * tailPow +
          LimbToInt(resultTail1) * Power.Pow(WORD_MODULUS, |lhs|) by
          {
            PowerPlusPowerPlusOneLemma(LimbToInt(resultTail0), LimbToInt(resultTail1), WORD_MODULUS, |lhs| - 1);
          }

        assert LimbsValueSpecBackward(lhs) + rhsCoeff * LimbsValueSpecBackward(rhs) + constant
          ==
          LimbsValueSpecBackward(result[..|result| - 1]) +
          LimbToInt(resultTail1) * Power.Pow(WORD_MODULUS, |lhs|) by
        {
          assert LimbsValueSpecBackward(result[..|result| - 2]) + LimbToInt(resultTail0) * tailPow
            == LimbsValueSpecBackward(result[..|result| - 1]) by
          {
            LimbsValueSpecBackwardLemma(result[..|result| - 1]);
            assert result[..|result| - 1] == result[..|result| - 2] + [resultTail0];
            assert tailPow == Power.Pow(WORD_MODULUS, |lhs| - 1);
            assert |lhs| - 1 == |result| - 2;
          }
        }

        assert LimbsValueSpecBackward(lhs) + rhsCoeff * LimbsValueSpecBackward(rhs) + constant
          ==
          LimbsValueSpecBackward(result) by
        {
          LimbsValueSpecBackwardLemma(result);
          assert resultTail1 == result[|result| - 1];
          assert |lhs| == |result| - 1;
        }
      }
    }
  }

  lemma {:rlimit 115} LinearOverHeadAndTailImpliesLinearOverValues_Helper0(
    lhsHeadVal: int,
    lhsTail: int,
    rhsCoeff: int,
    rhsHeadVal: int,
    rhsTail: int,
    constant: int,
    exp: nat
  )
    ensures
      lhsHeadVal +
      rhsCoeff * rhsHeadVal +
      (lhsTail + rhsCoeff * rhsTail) * Power.Pow(WORD_MODULUS, exp) +
      constant
      ==
      lhsHeadVal +
      lhsTail * Power.Pow(WORD_MODULUS, exp) +
      rhsCoeff * (
        rhsHeadVal +
        rhsTail * Power.Pow(WORD_MODULUS, exp)
      ) + constant
  {
  }

  lemma {:rlimit 18} LinearOverHeadAndTailImpliesLinearOverValues_Helper1(
    lhsTail: int, rhsCoeff: int, rhsTail: int, carryIn: int, tailPow: int
  )
    ensures (lhsTail + rhsCoeff * rhsTail + carryIn) * tailPow
      ==
      carryIn * tailPow + (lhsTail + rhsCoeff * rhsTail) * tailPow
  {}

  lemma {:rlimit 84} LimbsValueSpecBackwardLemma(limbs: seq<Limb>)
    requires |limbs| >= 1
    ensures
      var head := limbs[..|limbs| - 1];
      var tail := LimbToInt(limbs[|limbs| - 1]);
      LimbsValueSpecBackward(limbs) == LimbsValueSpecBackward(head) + tail * Power.Pow(WORD_MODULUS, |limbs| - 1)
  {
    var head := limbs[..|limbs| - 1];
    var tail := LimbToInt(limbs[|limbs| - 1]);
    var tailPow0 := Power.Pow(WORD_MODULUS, |limbs| - 1);

    assert tail * tailPow0 == tailPow0 * tail;
    assert LimbsValueSpecBackward(head) + tail * Power.Pow(WORD_MODULUS, |limbs| - 1)
      == LimbsValueSpecBackward(head) + Power.Pow(WORD_MODULUS, |limbs| - 1) * tail;
  }

  lemma {:rlimit 438} {:isolate_assertions} LimbsValueSpecLastLimbLemma(limbs: seq<Limb>)
  requires |limbs| > 0
  decreases |limbs|
  ensures LimbsValueSpec(limbs) == LimbsValueSpec(limbs[..|limbs|-1]) + LimbToInt(limbs[|limbs|-1]) * Power.Pow(WORD_MODULUS, |limbs|-1)
  {
    if |limbs| <= 1 {
      assert LimbsValueSpec(limbs) == LimbsValueSpec(limbs[..0]) + LimbToInt(limbs[0]) * Power.Pow(WORD_MODULUS, 0);
    } else {
      var tail := limbs[1..];
      var tailValue := LimbsValueSpec(tail);

      LimbsValueSpecLastLimbLemma(tail);
      assert tailValue == LimbsValueSpec(tail[..|tail|-1]) + LimbToInt(tail[|tail|-1]) * Power.Pow(WORD_MODULUS, |tail|-1);
      assert tail[..|tail| - 1] == limbs[1..|limbs|-1];
      assert tail[|tail| - 1] == limbs[|limbs| - 1];
      assert |tail| - 1 == |limbs| - 2;
      assert tailValue == (LimbsValueSpec(limbs[1..|limbs|-1]) + LimbToInt(limbs[|limbs|-1]) * Power.Pow(WORD_MODULUS, |limbs|-2));

      var middleValue := LimbsValueSpec(limbs[1..|limbs|-1]);

      LimbsValueSpecLastLimbLemma_Helper0(limbs, middleValue);

      assert LimbsValueSpec(limbs) == LimbToInt(limbs[0]) + WORD_MODULUS * tailValue
        == LimbToInt(limbs[0]) + WORD_MODULUS * (middleValue + LimbToInt(limbs[|limbs|-1]) * Power.Pow(WORD_MODULUS, |limbs|-2))
        == LimbToInt(limbs[0]) + WORD_MODULUS * middleValue + LimbToInt(limbs[|limbs|-1]) * Power.Pow(WORD_MODULUS, |limbs|-1);

      assert LimbToInt(limbs[0]) + WORD_MODULUS * middleValue == LimbsValueSpec(limbs[..|limbs|-1]);
      assert LimbsValueSpec(limbs) == LimbsValueSpec(limbs[..|limbs|-1]) + LimbToInt(limbs[|limbs|-1]) * Power.Pow(WORD_MODULUS, |limbs|-1);
    }
  }

  lemma {:rlimit 246} LimbsValueSpecLastLimbLemma_Helper0(limbs: seq<Limb>, middleValue: int)
    requires |limbs| > 1
    ensures WORD_MODULUS * (middleValue + LimbToInt(limbs[|limbs|-1]) * Power.Pow(WORD_MODULUS, |limbs|-2))
      == WORD_MODULUS * middleValue + WORD_MODULUS * LimbToInt(limbs[|limbs|-1]) * Power.Pow(WORD_MODULUS, |limbs|-2)
      == WORD_MODULUS * middleValue + LimbToInt(limbs[|limbs|-1]) * Power.Pow(WORD_MODULUS, |limbs|-1)
  { }

  lemma {:rlimit 200} LimbsBoundLemma(limbs: seq<Limb>)
    ensures LimbsValueSpec(limbs) < Power.Pow(WORD_MODULUS, |limbs|)
   {
    if |limbs| == 0 {
      assert LimbsValueSpec(limbs) == 0;
    } else {
      assert LimbsValueSpec(limbs) == LimbsValueSpec(limbs[..|limbs|-1]) + LimbToInt(limbs[|limbs|-1]) * Power.Pow(WORD_MODULUS, |limbs|-1) by {
        LimbsValueSpecLastLimbLemma(limbs);
      }
      assert LimbsValueSpec(limbs[..|limbs|-1]) < Power.Pow(WORD_MODULUS, |limbs|-1) by {
        LimbsBoundLemma(limbs[..|limbs|-1]);
      }
      assert LimbToInt(limbs[|limbs|-1]) <= WORD_MODULUS - 1;
      assert {:isolate} LimbsValueSpec(limbs) < Power.Pow(WORD_MODULUS, |limbs|-1) + (WORD_MODULUS - 1) * Power.Pow(WORD_MODULUS, |limbs|-1);
    }
   }

   lemma {:rlimit 100} {:fuel Power.Pow,4} WordModulusPowLemma()
    ensures Power.Pow(WORD_MODULUS, 0) == 1
    ensures Power.Pow(WORD_MODULUS, 1) == WORD_MODULUS
    ensures Power.Pow(WORD_MODULUS, 2) == WORD_MODULUS2
    ensures Power.Pow(WORD_MODULUS, 3) == WORD_MODULUS3
    ensures Power.Pow(WORD_MODULUS, 4) == WORD_MODULUS4
   {
   }
}
