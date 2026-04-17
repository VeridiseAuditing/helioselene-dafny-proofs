include "Arith.dfy"

module FieldInvert {
  import opened FieldBase
  import opened FieldRed256
  import opened FieldArith
  import opened CryptoBigint_0_5_5_Limb
  import opened CryptoBigint_0_5_5_U256
  import Modular
  import opened Limbs
  import opened NumberTheory
  import opened PowMod
  import opened BitOps
  import DivMod = Std.Arithmetic.DivMod

  // ===================================================================
  // PORTED IMPLEMENTATIONS — 1:1 Rust ports of field.rs
  // ===================================================================

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/7551826bbd31ba8d2b188403a0000586e8e07dc8/crypto/helioselene/src/field.rs#L467-L631
  // Binary GCD Algorithm 1, https://eprint.iacr.org/2020/972.
  method {:rlimit 200000}
    field_invert(
    a: HelioseleneField
  ) returns (invertible: bool, result: HelioseleneField)
    requires ValidField(a)
    ensures ValidField(result)
    ensures invertible <==> a.inner.ValueSpec() != 0
    ensures invertible ==>
      (result.inner.ValueSpec()
        * a.inner.ValueSpec())
        % ModulusValueSpec() == 1
  {
    // Original code: (field.rs:468):
    //   let mut a = self.0;
    var a_val := a.inner;

    // Original code: (field.rs:469):
    //   let mut b = MODULUS;
    var modulus_limbs: array<Limb> := new Limb[U256_LIMBS](
      i requires 0 <= i < U256_LIMBS => ModulusLimbs()[i]
    );
    var b_val := new U256(modulus_limbs);

    // GHOST CODE
    assert b_val.limbs[..] == ModulusLimbs()[..];

    // Original code: (field.rs:470):
    //   let mut u = U256::ONE;
    var one_limbs: array<Limb> := new Limb[U256_LIMBS](i => if i == 0 then LimbFromInt(1) else ZeroLimb());
    var u_val := new U256(one_limbs);

    // Original code: (field.rs:471):
    //   let mut v = U256::ZERO;
    var zero_limbs: array<Limb> := new Limb[U256_LIMBS](i => ZeroLimb());
    var v_val := new U256(zero_limbs);

    // GHOST CODE
    ghost var orig := a.inner.ValueSpec();
    ghost var p := ModulusValueSpec();
    ghost var steps_done: nat := 0;

    // Initial Bezout invariant
    assert a_val.ValueSpec() == orig;
    assert u_val.ValueSpec() == 1 by {
      assert u_val.limbs[..] == [LimbFromInt(1), ZeroLimb(), ZeroLimb(), ZeroLimb()][..];
    }
    assert a_val.ValueSpec() % p
      == (u_val.ValueSpec() * orig) % p;
    assert b_val.ValueSpec() == p;
    assert v_val.ValueSpec() == 0;
    assert b_val.ValueSpec() % p
      == (v_val.ValueSpec() * orig) % p;

    // Convergence setup
    MathHelpers.Pow2PositiveLemma(255);
    Pow256EqWordModulus4Lemma();
    MathHelpers.Pow2DoubleLemma(255);
    TwoModulusLt2Pow256Lemma();
    assert 2 * p < WORD_MODULUS4;
    assert WORD_MODULUS4 == 2 * MathHelpers.pow2(255);
    assert p < WORD_MODULUS4 / 2;
    assert WORD_MODULUS4 / 2 == MathHelpers.pow2(255);
    assert p < MathHelpers.pow2(255);
    assert orig < p;
    assert orig < MathHelpers.pow2(255);
    BitLengthUpperBoundLemma(orig, 255);
    BitLengthUpperBoundLemma(p, 255);

    // Original code: (field.rs:621-625):
    //   for limbs in (2 ..= U256::LIMBS).rev() {
    //     for _ in 0 .. (2 * Limb::BITS) {
    //       step(&mut a, &mut b, &mut u, &mut v, limbs);
    //     }
    //   }
    // NOTE: (2 ..= 4).rev() = [4, 3, 2]; 2 * 64 = 128 iterations each.
    for limbs := U256_LIMBS + 1 downto 2
      invariant 2 <= limbs <= 5
      invariant InvertBezoutCondition(a_val, b_val, u_val, v_val, orig)
      invariant u_val.ValueSpec() <= p
      invariant v_val.ValueSpec() <= p
      invariant b_val.ValueSpec() % 2 == 1
      invariant steps_done == (5 - limbs) * 128
      invariant a_val.ValueSpec() == 0
        || BitLength(a_val.ValueSpec())
         + BitLength(b_val.ValueSpec())
          <= 510 - steps_done
      invariant gcd(a_val.ValueSpec(),
        b_val.ValueSpec()) == gcd(orig, p)
    {
      // Original code:
      //     for _ in 0 .. (2 * Limb::BITS) {
      //       step(&mut a, &mut b, &mut u, &mut v, limbs);
      //     }
      for i := 0 to (2 * LIMB_BITS)
        invariant 0 <= i <= 128
        invariant InvertBezoutCondition(a_val, b_val, u_val, v_val, orig)
        invariant u_val.ValueSpec() <= p
        invariant v_val.ValueSpec() <= p
        invariant b_val.ValueSpec() % 2 == 1
        invariant steps_done == (4 - limbs) * 128 + i
        invariant a_val.ValueSpec() == 0
          || BitLength(a_val.ValueSpec())
           + BitLength(b_val.ValueSpec())
            <= 510 - steps_done
        invariant gcd(a_val.ValueSpec(),
          b_val.ValueSpec()) == gcd(orig, p)
      {
        // Original code:
        //       step(&mut a, &mut b, &mut u, &mut v, limbs);
        a_val, b_val, u_val, v_val :=
          step(a_val, b_val, u_val, v_val,
            orig, limbs);

        // GHOST CODE
        steps_done := steps_done + 1;
      }
    }

    // Original code: (field.rs:626-628):
    //   for _ in 0 .. ((2 * Limb::BITS) - 2) {
    //     step(&mut a, &mut b, &mut u, &mut v, 1);
    //   }
    for j := 0 to ((2 * LIMB_BITS) - 2)
      invariant 0 <= j <= 126
      invariant InvertBezoutCondition(a_val, b_val, u_val, v_val, orig)
      invariant u_val.ValueSpec() <= p
      invariant v_val.ValueSpec() <= p
      invariant b_val.ValueSpec() % 2 == 1
      invariant steps_done == 384 + j
      invariant a_val.ValueSpec() == 0
        || BitLength(a_val.ValueSpec())
         + BitLength(b_val.ValueSpec())
          <= 510 - steps_done
      invariant gcd(a_val.ValueSpec(),
        b_val.ValueSpec()) == gcd(orig, p)
    {
      // Original Code:
      //     step(&mut a, &mut b, &mut u, &mut v, 1);
      a_val, b_val, u_val, v_val :=
        step(a_val, b_val, u_val, v_val, orig, 1);

      // GHOST CODE
      steps_done := steps_done + 1;
    }

    // Original code: (field.rs:630):
    //   CtOption::new(Self(red1(v)), !self.is_zero())
    // NOTE: We return a bool (isSome, result) rather than using a result struct
    var reduced_v := red1(v_val);
    var a_is_zero := field_is_zero(a);
    invertible := !a_is_zero;
    result := HelioseleneField(reduced_v);

    // PROOF: convergence + inverse (only when orig != 0)
    if orig > 0 {
      // After 510 steps: convergence
      assert steps_done == 510;
      if a_val.ValueSpec() > 0 {
        BitLengthPositiveLemma(a_val.ValueSpec());
        BitLengthPositiveLemma(b_val.ValueSpec());
        assert false;
      }
      assert a_val.ValueSpec() == 0;

      // GCD conclusion
      GcdZeroLemma(b_val.ValueSpec());
      ModulusIsPrimeLemma();
      PrimeGcdLemma(orig, p);
      ghost var b_int := b_val.ValueSpec();
      assert gcd(0, b_int) == b_int;
      assert gcd(orig, p) == 1;
      assert b_int == 1;

      // Final reduction
      ghost var v_int := v_val.ValueSpec();
      InvertFinalLemma(
        b_int, v_int, reduced_v.ValueSpec(),
        orig, p);
    }
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/7551826bbd31ba8d2b188403a0000586e8e07dc8/crypto/helioselene/src/field.rs#L474-L618
  // Constant-time binary GCD step (nested `fn step` inside Rust `fn invert`).
  //
  // NOTE: Rust uses partial-width loops (`for l in 0 .. limbs`) over the
  // `a` / `b` / shift operations, exploiting that the upper (4 - limbs)
  // words of `a` and `b` are zero. The Dafny port performs the matching
  // full-width chains via helpers (invert_step_ct_masks, invert_step_ct_ab);
  // the zero-upper-limbs invariant is implicit in the binary GCD convergence,
  // and the 256-bit value is identical in both cases.
  //
  // NOTE: Rust computes the u update inline as a branchless carry chain that
  // interleaves negation with one-or-two instances of the modulus via
  // MODULUS_XOR_TWO_MODULUS. Dafny uses the branching equivalent
  // invert_step_ct_u_update, which produces the same value modulo p; see
  // that method for the full rewritten Rust block.
  method {:timeLimit 60} {:isolate_assertions} step(
    a: U256, b: U256, u: U256, v: U256,
    ghost orig: int, limbs: nat
  ) returns (a': U256, b': U256, u': U256, v': U256)
    requires a.Valid() && b.Valid()
    requires u.Valid() && v.Valid()
    requires 1 <= limbs <= U256_LIMBS
    // Bezout invariant
    requires InvertBezoutCondition(a, b, u, v, orig)
    requires u.ValueSpec() <= ModulusValueSpec()
    requires v.ValueSpec() <= ModulusValueSpec()
    requires b.ValueSpec() % 2 == 1
    ensures {:isolate} a'.Valid() && b'.Valid()
    ensures {:isolate} u'.Valid() && v'.Valid()
    // Bezout invariant preserved
    ensures {:isolate}
      InvertBezoutCondition(a', b', u', v', orig)
    ensures u'.ValueSpec() <= ModulusValueSpec()
    ensures v'.ValueSpec() <= ModulusValueSpec()
    ensures b'.ValueSpec() % 2 == 1
    // Convergence
    ensures a.ValueSpec() > 0 ==>
      BitLength(a'.ValueSpec())
        + BitLength(b'.ValueSpec())
       <= BitLength(a.ValueSpec())
        + BitLength(b.ValueSpec()) - 1
    ensures a.ValueSpec() == 0 ==>
      a'.ValueSpec() == 0
      && b'.ValueSpec() == b.ValueSpec()
    // GCD preservation
    ensures gcd(a'.ValueSpec(), b'.ValueSpec())
         == gcd(a.ValueSpec(), b.ValueSpec())
  {
    // Original code::
    //   let a_is_odd = a.as_limbs()[0].0 & 1;
    //   let a_is_odd = Limb(a_is_odd).wrapping_neg();
    //
    //   // Calculate `a - b`, which also yields if `a < b` by if it underflows
    //   let mut borrow = Limb::ZERO;
    //   let mut a_sub_b = U256::ZERO;
    //   for l in 0 .. limbs {
    //     (a_sub_b.as_limbs_mut()[l], borrow) =
    //       sub_with_bounded_overflow(a.as_limbs()[l], b.as_limbs()[l], borrow);
    //   }
    //   let a_lt_b = borrow.wrapping_neg();
    //   let both = a_is_odd & a_lt_b;
    //
    //   // Set `b` to `a` (part of the swap)
    //   *b = select(b, a, both, limbs);
    //
    //   // Negate `a_sub_b` to obtain `a_diff_b` if `a_lt_b`, then set
    //   // *a = select(a, &a_diff_b, a_is_odd, limbs), then shift right 1.
    var a_is_odd, a_lt_b, both: Limb;
    a', b', a_is_odd, a_lt_b, both :=
      step_a_b_phase(a, b, limbs);

    // Original code:: (u/v update — see step_u_v_phase for full Rust block
    // and a note on the structural divergence between Rust's branchless
    // carry chain and Dafny's branching helpers)
    u', v' := step_u_v_phase(u, v, a_is_odd, a_lt_b, both);

    // PROOF: connect phase helper specs to
    // Bezout / convergence / GCD postconditions.
    ghost var is_odd := a_is_odd == MaxLimb();
    ghost var is_lt := a_lt_b == MaxLimb();
    ghost var p := ModulusValueSpec();
    InvertStepCtProofLemma(
      a.ValueSpec(), b.ValueSpec(),
      u.ValueSpec(), v.ValueSpec(),
      a'.ValueSpec(), b'.ValueSpec(),
      u'.ValueSpec(), v'.ValueSpec(),
      orig, p,
      is_odd, is_lt);
  }

  // Port of the a/b update half of Rust `fn step` (field.rs:475-516,612-615).
  // Computes a_is_odd / a_lt_b / both masks, the |a - b| value, and performs
  // the two selects and the shift that update a and b. Executable body is a
  // thin wrapper around invert_step_ct_masks + invert_step_ct_ab; the full
  // Rust block is quoted on the enclosing step() method.
  method {:timeLimit 180} step_a_b_phase(
    a: U256, b: U256, limbs: nat
  ) returns (
    a': U256, b': U256,
    a_is_odd: Limb, a_lt_b: Limb, both: Limb
  )
    requires a.Valid() && b.Valid()
    requires 1 <= limbs <= U256_LIMBS
    ensures a'.Valid() && b'.Valid()
    ensures IsMask(a_is_odd)
    ensures (a_is_odd == MaxLimb())
      <==> (a.ValueSpec() % 2 == 1)
    ensures IsMask(a_lt_b)
    ensures (a_lt_b == MaxLimb())
      <==> (a.ValueSpec() < b.ValueSpec())
    ensures IsMask(both)
    ensures (both == MaxLimb())
      <==> (a.ValueSpec() % 2 == 1
        && a.ValueSpec() < b.ValueSpec())
    ensures a_is_odd == MaxLimb() ==>
      a'.ValueSpec() ==
        (if a.ValueSpec() >= b.ValueSpec()
          then a.ValueSpec() - b.ValueSpec()
          else b.ValueSpec() - a.ValueSpec()) / 2
    ensures a_is_odd == ZeroLimb() ==>
      a'.ValueSpec() == a.ValueSpec() / 2
    ensures both == MaxLimb() ==>
      b'.ValueSpec() == a.ValueSpec()
    ensures both == ZeroLimb() ==>
      b'.ValueSpec() == b.ValueSpec()
  {
    // NOTE: Rust uses partial-width (0 .. limbs) loops. Dafny performs the
    // same chain at full width (0 .. U256::LIMBS) via invert_step_ct_masks
    // and invert_step_ct_ab. Under the outer invariant that the upper
    // (4 - limbs) words of `a` and `b` are zero, the two produce identical
    // 256-bit values.
    var asb0, asb1, asb2, asb3: Limb;
    a_is_odd, a_lt_b, both,
      asb0, asb1, asb2, asb3 :=
      invert_step_ct_masks(a, b);

    a', b' :=
      invert_step_ct_ab(
        a, b, a_is_odd, a_lt_b, both,
        asb0, asb1, asb2, asb3);
  }

  // Port of the u/v update half of Rust `fn step` (field.rs:525-617).
  //
  // Original code::
  //   let u_start = *u;
  //   // Calculate `v` or `v - u` depending on if `a & 1`
  //   let mut borrow = Limb::ZERO;
  //   let mut u_sub_v = U256::ZERO;
  //   for l in 0 .. U256::LIMBS {
  //     (u_sub_v.as_limbs_mut()[l], borrow) =
  //       sub_with_bounded_overflow(u.as_limbs()[l], v.as_limbs()[l] & a_is_odd, borrow);
  //   }
  //   let u_sub_v_neg = borrow.wrapping_neg();
  //   // Negate in the case `(a & 1) & (a < b)`
  //   let should_negate = a_is_odd & a_lt_b;
  //   let v_u_sub_u_v_neg = u_sub_v_neg ^ should_negate;
  //   let result_is_odd = (u_sub_v.as_limbs()[0] & Limb::ONE).wrapping_neg();
  //   const MODULUS_XOR_TWO_MODULUS: U256 =
  //     U256::from_be_hex("80000000000000000000000000000000195fd8272bba15380a8f1db9613261f5");
  //   let add_two_modulus = v_u_sub_u_v_neg & (!result_is_odd);
  //   let add_one_modulus = v_u_sub_u_v_neg | result_is_odd;
  //   let mut carry = Limb::ONE & should_negate;
  //   for l in 0 .. U128::LIMBS {
  //     let modulus_instances = (MODULUS.as_limbs()[l] & add_one_modulus) ^
  //       (MODULUS_XOR_TWO_MODULUS.as_limbs()[l] & add_two_modulus);
  //     let (limb, carry_bool) = (u_sub_v.as_limbs()[l] ^ should_negate)
  //       .0
  //       .overflowing_add(modulus_instances.wrapping_add(carry).0);
  //     (u.as_limbs_mut()[l], carry) = (Limb(limb), Limb(Word::from(carry_bool)));
  //   }
  //   for l in U128::LIMBS .. U256::LIMBS {
  //     let modulus_instances = MODULUS.as_limbs()[l] & add_one_modulus;
  //     (u.as_limbs_mut()[l], carry) = add_with_bounded_overflow(
  //       u_sub_v.as_limbs()[l] ^ should_negate,
  //       modulus_instances,
  //       carry,
  //     );
  //   }
  //   u.as_limbs_mut()[U256::LIMBS - 1] =
  //     u.as_limbs()[U256::LIMBS - 1] | (add_two_modulus << (Limb::BITS - 1));
  //   // Set `v` to the `u` from the start if `(a & 1) & (a < b)`
  //   *v = select(v, &u_start, both, U256::LIMBS);
  //   *u = u.shr_vartime(1);
  //
  // NOTE: Structural divergence from Rust. The Rust carry chain above
  // computes halve((u - v * a_is_odd ± modulus instances) mod 2^256)
  // branchlessly, relying on modulus arithmetic to land back in [0, p].
  // The Dafny port splits the three cases (even / odd+ge / odd+lt) and
  // uses branching helpers invert_u_diff + invert_halve_u wrapped by
  // invert_step_ct_u_update. The v-select is identical to Rust.
  // InvertUHalveSpec captures the same modular identity as the Rust block.
  method {:timeLimit 180} step_u_v_phase(
    u: U256, v: U256,
    a_is_odd: Limb, a_lt_b: Limb, both: Limb
  ) returns (u': U256, v': U256)
    requires u.Valid() && v.Valid()
    requires IsMask(a_is_odd)
    requires IsMask(a_lt_b)
    requires IsMask(both)
    requires both == MaxLimb()
      ==> a_is_odd == MaxLimb()
    requires u.ValueSpec() <= ModulusValueSpec()
    requires v.ValueSpec() <= ModulusValueSpec()
    ensures u'.Valid() && v'.Valid()
    ensures u'.ValueSpec() <= ModulusValueSpec()
    ensures both == MaxLimb() ==>
      v'.ValueSpec() == u.ValueSpec()
    ensures both == ZeroLimb() ==>
      v'.ValueSpec() == v.ValueSpec()
    ensures InvertUHalveSpec(
      u', u.ValueSpec(), v.ValueSpec(),
      a_is_odd, both)
  {
    v' := select_u256(v, u, both);
    u' := invert_step_ct_u_update(
      u, v, a_is_odd, both);
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/7551826bbd31ba8d2b188403a0000586e8e07dc8/crypto/helioselene/src/field.rs#L475-L486
  // First fragment of Rust `fn step`: parity mask, `a - b` chain, and
  // the a_lt_b / both masks. Produces the per-limb a_sub_b words
  // (asb0..asb3) so a subsequent cond-neg chain can derive |a - b|.
  method {:timeLimit 180} invert_step_ct_masks(a: U256, b: U256)
    returns (
      a_is_odd: Limb, a_lt_b: Limb,
      both: Limb,
      asb0: Limb, asb1: Limb,
      asb2: Limb, asb3: Limb
    )
    requires a.Valid() && b.Valid()
    ensures IsMask(a_is_odd)
    ensures a_is_odd == MaxLimb()
      <==> a.ValueSpec() % 2 == 1
    ensures IsMask(a_lt_b)
    ensures {:isolate} a_lt_b == MaxLimb()
      <==> a.ValueSpec() < b.ValueSpec()
    ensures IsMask(both)
    ensures both == MaxLimb()
      <==> (a.ValueSpec() % 2 == 1
        && a.ValueSpec() < b.ValueSpec())
    ensures {:isolate}
      var a_val := a.ValueSpec();
      var b_val := b.ValueSpec();
      var asb_val := LimbToInt(asb0)
        + LimbToInt(asb1) * WORD_MODULUS
        + LimbToInt(asb2) * WORD_MODULUS2
        + LimbToInt(asb3) * WORD_MODULUS3;
      && (a_val >= b_val ==>
        asb_val == a_val - b_val)
      && (a_val < b_val ==>
        asb_val == a_val - b_val
          + WORD_MODULUS4)
  {
    // GHOST CODE
    assert WORD_MODULUS % 2 == 0;
    assert a.ValueSpec() % 2
      == LimbToInt(a.limbs[0]) % 2;

    // Original code:
    // let a_is_odd = a.as_limbs()[0].0 & 1;
    // NOTE: We use %2 here instead of & 1
    var a_is_odd_ := LimbFromInt(LimbToInt(a.limbs[0]) % 2);

    // GHOST CODE
    ghost var a_low_bit := a_is_odd_;

    // Original code:
    // let a_is_odd = Limb(a_is_odd).wrapping_neg();
    a_is_odd := wrapping_neg(a_is_odd_);

    // GHOST CODE
    assert a_low_bit == ZeroLimb() || a_low_bit == LimbFromInt(1);
    WrappingNegBorrowLemma(a_low_bit);

    // Original code:
    // // Calculate `a - b`, which also yields if `a < b` by if it underflows
    // let mut borrow = Limb::ZERO;
    var borrow: Limb := ZeroLimb();

    // Original code:
    // let mut a_sub_b = U256::ZERO;
    var zero_limbs := new Limb[U256_LIMBS](i => ZeroLimb());
    var a_sub_b := new U256(zero_limbs);

    // for l in 0 .. limbs {
    //   (a_sub_b.as_limbs_mut()[l], borrow) =
    //     sub_with_bounded_overflow(a.as_limbs()[l], b.as_limbs()[l], borrow);
    // }
    asb0, borrow := sub_with_bounded_overflow(
      a.limbs[0], b.limbs[0], borrow);
    ghost var c0 := borrow;
    assert (asb0, c0) == SubBoundedSpec(
      a.limbs[0], b.limbs[0], ZeroLimb());
    asb1, borrow := sub_with_bounded_overflow(
      a.limbs[1], b.limbs[1], borrow);
    ghost var c1 := borrow;
    assert (asb1, c1) == SubBoundedSpec(
      a.limbs[1], b.limbs[1], c0);
    asb2, borrow := sub_with_bounded_overflow(
      a.limbs[2], b.limbs[2], borrow);
    ghost var c2 := borrow;
    assert (asb2, c2) == SubBoundedSpec(
      a.limbs[2], b.limbs[2], c1);
    asb3, borrow := sub_with_bounded_overflow(
      a.limbs[3], b.limbs[3], borrow);
    assert (asb3, borrow) == SubBoundedSpec(
      a.limbs[3], b.limbs[3], c2);
    // borrow is final carry c3

    // Connect to SubBoundedChain4Lemma
    SubBoundedChain4Lemma(
      a.limbs[0], a.limbs[1],
      a.limbs[2], a.limbs[3],
      b.limbs[0], b.limbs[1],
      b.limbs[2], b.limbs[3]);

    // Comparison mask
    a_lt_b := wrapping_neg(borrow);
    WrappingNegBorrowLemma(borrow);

    // Combined mask
    both := LimbAnd(a_is_odd, a_lt_b);
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/7551826bbd31ba8d2b188403a0000586e8e07dc8/crypto/helioselene/src/field.rs#L500-L510
  // Constant-time conditional negation via XOR + carry chain.
  // mask = 0   : identity (result = input).
  // mask = MAX : 2's complement (result = 2^256 - input).
  // Used to obtain |a - b| from the signed `a_sub_b` chain.
  method invert_step_ct_cond_neg(
    d0: Limb, d1: Limb,
    d2: Limb, d3: Limb,
    mask: Limb
  ) returns (
    r0: Limb, r1: Limb,
    r2: Limb, r3: Limb
  )
    requires IsMask(mask)
    ensures
      var d_val := Limbs4Value(d0, d1, d2, d3);
      var r_val := Limbs4Value(r0, r1, r2, r3);
      && (mask == ZeroLimb() ==>
        r_val == d_val)
      && (mask == MaxLimb() && d_val == 0
        ==> r_val == 0)
      && (mask == MaxLimb() && d_val > 0
        ==> r_val == WORD_MODULUS4 - d_val)
  {
    var cin := LimbAnd(LimbFromInt(1), mask);
    var carry: Limb;

    r0, carry := add_with_bounded_overflow(
      LimbXor(d0, mask), ZeroLimb(), cin);
    ghost var c0 := carry;
    r1, carry := add_with_bounded_overflow(
      LimbXor(d1, mask), ZeroLimb(), carry);
    ghost var c1 := carry;
    r2, carry := add_with_bounded_overflow(
      LimbXor(d2, mask), ZeroLimb(), carry);
    ghost var c2 := carry;
    r3, carry := add_with_bounded_overflow(
      LimbXor(d3, mask), ZeroLimb(), carry);

    if mask == ZeroLimb() {
      LimbXorMaskLemma(d0, ZeroLimb());
      LimbXorMaskLemma(d1, ZeroLimb());
      LimbXorMaskLemma(d2, ZeroLimb());
      LimbXorMaskLemma(d3, ZeroLimb());
      CondNeg256ZeroLemma(
        d0, d1, d2, d3);
    } else {
      LimbXorMaskLemma(d0, MaxLimb());
      LimbXorMaskLemma(d1, MaxLimb());
      LimbXorMaskLemma(d2, MaxLimb());
      LimbXorMaskLemma(d3, MaxLimb());
      CondNeg256MaxLemma(
        d0, d1, d2, d3,
        LimbXor(d0, mask),
        LimbXor(d1, mask),
        LimbXor(d2, mask),
        LimbXor(d3, mask),
        r0, r1, r2, r3,
        c0, c1, c2, carry);
    }
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/7551826bbd31ba8d2b188403a0000586e8e07dc8/crypto/helioselene/src/field.rs#L497-L516,L612-L615
  // Second fragment of Rust `fn step`: the b-select, the |a - b|
  // construction via invert_step_ct_cond_neg, the a-select against
  // |a - b|, and the final shift-right-1 of a.
  method {:rlimit 200000} {:isolate_assertions} invert_step_ct_ab(
    a: U256, b: U256,
    a_is_odd: Limb, a_lt_b: Limb,
    both: Limb,
    asb0: Limb, asb1: Limb,
    asb2: Limb, asb3: Limb
  ) returns (a': U256, b': U256)
    requires a.Valid() && b.Valid()
    requires IsMask(a_is_odd)
    requires IsMask(a_lt_b)
    requires IsMask(both)
    requires a_is_odd == MaxLimb()
      <==> a.ValueSpec() % 2 == 1
    requires a_lt_b == MaxLimb()
      <==> a.ValueSpec() < b.ValueSpec()
    requires both == MaxLimb()
      <==> (a.ValueSpec() % 2 == 1
        && a.ValueSpec() < b.ValueSpec())
    requires
      var a_val := a.ValueSpec();
      var b_val := b.ValueSpec();
      var asb_val := LimbToInt(asb0)
        + LimbToInt(asb1) * WORD_MODULUS
        + LimbToInt(asb2) * WORD_MODULUS2
        + LimbToInt(asb3) * WORD_MODULUS3;
      && (a_val >= b_val ==>
        asb_val == a_val - b_val)
      && (a_val < b_val ==>
        asb_val == a_val - b_val
          + WORD_MODULUS4)
    ensures a'.Valid() && b'.Valid()
    ensures fresh(a') && fresh(a'.limbs)
    ensures fresh(b') && fresh(b'.limbs)
    ensures both == MaxLimb() ==>
      b'.ValueSpec() == a.ValueSpec()
    ensures both == ZeroLimb() ==>
      b'.ValueSpec() == b.ValueSpec()
    ensures a_is_odd == MaxLimb() ==>
      a'.ValueSpec() ==
        (if a.ValueSpec() >= b.ValueSpec()
          then a.ValueSpec() - b.ValueSpec()
          else b.ValueSpec() - a.ValueSpec()) / 2
    ensures a_is_odd == ZeroLimb() ==>
      a'.ValueSpec() == a.ValueSpec() / 2
  {
    ghost var a_val := a.ValueSpec();
    ghost var b_val := b.ValueSpec();
    ghost var asb_val := Limbs4Value(asb0, asb1, asb2, asb3);

    // b' = select(b, a, both)
    b' := select_u256(b, a, both);

    // Conditional negation: |a-b|
    var adb0, adb1, adb2, adb3 :=
      invert_step_ct_cond_neg(
        asb0, asb1, asb2, asb3, a_lt_b);

    ghost var adb_val := Limbs4Value(adb0, adb1, adb2, adb3);

    // Connect cond_neg result to |a-b|
    if a_lt_b == ZeroLimb() {
      // Identity: adb = asb = a - b
      assert adb_val == asb_val == a_val - b_val;
    } else {
      // Negation: adb = W^4 - asb = b - a
      assert asb_val > 0;
      assert adb_val == b_val - a_val;
    }

    // Construct |a-b| as U256
    var adb_arr := new Limb[U256_LIMBS][
      adb0, adb1, adb2, adb3];
    var a_diff_b := new U256(adb_arr);

    // Connect a_diff_b ValueSpec to adb_val
    assert {:isolate} {:rlimit 2000000} a_diff_b.ValueSpec() == adb_val;

    // a' = select(a, |a-b|, a_is_odd) then shr
    a' := select_u256(a, a_diff_b, a_is_odd);
    ghost var a_pre_shr := a'.ValueSpec();
    a' := a'.shr_vartime_1();
  }

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/7551826bbd31ba8d2b188403a0000586e8e07dc8/crypto/helioselene/src/field.rs#L523-L609
  // Halve the appropriate u-difference modulo p for each binary GCD
  // case (even, odd+ge, odd+lt).
  //
  // NOTE: Structural divergence from Rust. The Rust block (quoted on
  // step_u_v_phase) uses a branchless carry chain with
  // MODULUS_XOR_TWO_MODULUS to compute halve((u - v * a_is_odd
  // ± modulus instances) mod 2^256) in a single pass. This Dafny
  // implementation splits the three cases and delegates to the
  // branching helpers invert_u_diff + invert_halve_u, which yield
  // identical results modulo p. The postcondition InvertUHalveSpec
  // captures the same modular identity for both shapes.
  method invert_step_ct_u_update(
    u: U256, v: U256,
    a_is_odd: Limb, both: Limb
  ) returns (u': U256)
    requires u.Valid() && v.Valid()
    requires IsMask(a_is_odd)
    requires IsMask(both)
    requires both == MaxLimb()
      ==> a_is_odd == MaxLimb()
    requires u.ValueSpec() <= ModulusValueSpec()
    requires v.ValueSpec() <= ModulusValueSpec()
    modifies {}
    ensures u'.Valid() && fresh(u'.limbs)
    ensures u'.ValueSpec() <= ModulusValueSpec()
    ensures InvertUHalveSpec(
      u', u.ValueSpec(), v.ValueSpec(),
      a_is_odd, both)
  {
    if a_is_odd == ZeroLimb() {
      // Even: just halve u
      u' := invert_halve_u(u);
    } else if both == ZeroLimb() {
      // Odd+ge: halve(u - v mod p)
      var diff := invert_u_diff(u, v);
      u' := invert_halve_u(diff);
    } else {
      // Odd+lt: halve(v - u mod p)
      var diff := invert_u_diff(v, u);
      u' := invert_halve_u(diff);
    }
  }

  // Helper for invert_step_ct_u_update. Computes (x - y) mod p in
  // [0, p] via sbb + conditional wrapping_add(MODULUS).
  //
  // NOTE: Dafny-specific factoring. The Rust block (quoted on
  // step_u_v_phase) folds the analogous subtract + modulus-correct
  // into the same carry chain that performs the halving; this method
  // isolates the subtract half for clarity of the Dafny proof.
  method {:rlimit 100000} invert_u_diff(x: U256, y: U256) returns (result: U256)
    requires x.Valid() && y.Valid()
    requires x.ValueSpec() <= ModulusValueSpec()
    requires y.ValueSpec() <= ModulusValueSpec()
    ensures result.Valid()
    ensures fresh(result.limbs)
    ensures result.ValueSpec() % ModulusValueSpec()
      == (x.ValueSpec() - y.ValueSpec())
         % ModulusValueSpec()
    // NOTE: Postcondition allows result == p (not < p). Intentional for binary GCD
    // intermediates; final red1(v) ensures canonical form.
    ensures result.ValueSpec() <= ModulusValueSpec()
  {
    ghost var x_val := x.ValueSpec();
    ghost var y_val := y.ValueSpec();
    ghost var p := ModulusValueSpec();

    var diff, borrow := x.sbb(y, ZeroLimb());
    if borrow != ZeroLimb() {
      // x < y: diff = x - y + W4, add p to correct
      assert diff.ValueSpec() == x_val - y_val + WORD_MODULUS4;
      var modulus := Modulus();
      result := diff.wrapping_add(modulus);
      assert x_val - y_val + p >= 0;
      assert x_val - y_val + p < WORD_MODULUS4 by {
        assert x_val - y_val + p < p;
        assert p < WORD_MODULUS4;
      }
      DivMod.LemmaSmallMod(
        x_val - y_val + p, WORD_MODULUS4);
      DivMod.LemmaModMultiplesVanish(
        1, x_val - y_val + p, WORD_MODULUS4);
      assert result.ValueSpec()
        == x_val - y_val + p;
      assert result.ValueSpec() <= p;
      DivMod.LemmaModMultiplesVanish(
        1, x_val - y_val, p);
    } else {
      // x >= y: diff = x - y
      result := diff;
      assert result.ValueSpec() == x_val - y_val;
      assert result.ValueSpec() <= p;
    }
  }

  // Ported from the halve half of https://github.com/monero-oxide/monero-oxide/blob/7551826bbd31ba8d2b188403a0000586e8e07dc8/crypto/helioselene/src/field.rs#L543-L617
  // Halve u modulo p. If u is odd, add p to make it even (safe because
  // p is odd, so u + p has the opposite parity), then shift right 1.
  // Postcondition: 2 * result ≡ u  (mod p).
  //
  // NOTE: Structural divergence from Rust. The Rust block (quoted on
  // step_u_v_phase) folds this halving into the same carry chain that
  // performs the u - v subtract + conditional negate, using the
  // MODULUS_XOR_TWO_MODULUS trick. The Dafny port uses the branching
  // add-p-if-odd / shift-right form, which produces the same value
  // modulo p.
  method {:rlimit 200000}
    invert_halve_u(u: U256) returns (result: U256)
    requires u.Valid()
    requires u.ValueSpec() <= ModulusValueSpec()
    ensures result.Valid()
    ensures fresh(result.limbs)
    ensures (2 * result.ValueSpec()) % ModulusValueSpec()
      == u.ValueSpec() % ModulusValueSpec()
    ensures result.ValueSpec() <= ModulusValueSpec()
  {
    ghost var u_val := u.ValueSpec();
    ghost var p := ModulusValueSpec();

    if LimbToInt(u.limbs[0]) % 2 == 1 {
      // u is odd: add p to make even, then halve
      var modulus := Modulus();
      var u_plus_p, carry := u.adc(modulus, ZeroLimb());

      ghost var carry_val := LimbToInt(carry);
      ghost var sum_val := u_plus_p.ValueSpec();
      // adc postcondition:
      assert sum_val + carry_val * WORD_MODULUS4
        == u_val + p;

      // p is odd (lowest limb ends in 0x...53)
      assert p % 2 == 1;
      // u + p is even (odd + odd)
      assert {:isolate} {:rlimit 200000} (u_val + p) % 2 == 0 by {
        assert {:isolate} (u_val + p) % 2 == (u_val % 2 + p % 2) % 2 by {
          DivMod.LemmaAddModNoop(u_val, p, 2);
        }
      }
      // sum_val has same parity as u+p
      // (since carry_val * WORD_MODULUS4 is even)
      assert sum_val % 2 == 0;

      var shifted := u_plus_p.shr_vartime_1();
      assert shifted.ValueSpec() == sum_val / 2;

      if carry != ZeroLimb() {
        assert carry_val == 1;
        assert sum_val == u_val + p - WORD_MODULUS4;

        // shifted < 2^255
        assert shifted.ValueSpec() < WORD_MODULUS4 / 2;
        // Top limb is bounded: all lower limbs are >= 0
        assert LimbToInt(shifted.limbs[0]) >= 0;
        assert LimbToInt(shifted.limbs[1]) >= 0;
        assert LimbToInt(shifted.limbs[2]) >= 0;
        assert shifted.ValueSpec()
          >= LimbToInt(shifted.limbs[3]) * WORD_MODULUS3;
        assert WORD_MODULUS4 / 2
          == WORD_MODULUS3 * (WORD_MODULUS / 2);
        assert LimbToInt(shifted.limbs[3])
          < WORD_MODULUS / 2;

        var new_limbs := new Limb[U256_LIMBS][
          shifted.limbs[0], shifted.limbs[1],
          shifted.limbs[2],
          LimbFromInt(
            LimbToInt(shifted.limbs[3])
            + WORD_MODULUS / 2)];
        result := new U256(new_limbs);

        // result = shifted + 2^255
        assert (WORD_MODULUS / 2) * WORD_MODULUS3
          == WORD_MODULUS4 / 2;
        assert result.ValueSpec()
          == shifted.ValueSpec() + WORD_MODULUS4 / 2;
        assert result.ValueSpec()
          == sum_val / 2 + WORD_MODULUS4 / 2;
        assert result.ValueSpec()
          == (u_val + p) / 2;

        // 2 * result == u + p
        assert 2 * result.ValueSpec() == u_val + p;
        // Bound: result = (u + p) / 2 <= (p + p) / 2 = p
        assert result.ValueSpec() <= p;
        DivMod.LemmaModMultiplesVanish(1, u_val, p);
      } else {
        assert carry_val == 0;
        assert sum_val == u_val + p;

        result := shifted;
        assert result.ValueSpec() == (u_val + p) / 2;
        assert 2 * result.ValueSpec() == u_val + p;
        // Bound: result = (u + p) / 2 <= (p + p) / 2 = p
        assert result.ValueSpec() <= p;
        DivMod.LemmaModMultiplesVanish(1, u_val, p);
      }
    } else {
      // u is even: just halve
      assert {:isolate} {:rlimit 100000} u_val % 2 == 0 by {
        assert {:isolate} u_val % 2 == LimbToInt(u.limbs[0]) % 2;
        assert 0 <= LimbToInt(u.limbs[0]) % 2 < 2;
        assert LimbToInt(u.limbs[0]) % 2 == 0;
      }
      result := u.shr_vartime_1();
      assert result.ValueSpec() == u_val / 2;
      assert 2 * result.ValueSpec() == u_val;
      // Bound: result = u / 2 <= p / 2 < p
      assert result.ValueSpec() <= p;
    }
  }

  // ===================================================================
  // SPECS / GHOST FUNCTIONS
  // ===================================================================

  // Value of four 64-bit limbs packed in little-endian order.
  ghost function Limbs4Value(
    x0: Limb, x1: Limb, x2: Limb, x3: Limb
  ): int {
    LimbToInt(x0)
      + LimbToInt(x1) * WORD_MODULUS
      + LimbToInt(x2) * WORD_MODULUS2
      + LimbToInt(x3) * WORD_MODULUS3
  }

  // True iff m is a valid CT bitmask (all-zero or all-one).
  ghost predicate IsMask(m: Limb) {
    m == ZeroLimb() || m == MaxLimb()
  }

  // u' satisfies the 3-case halving spec for the binary GCD step.
  // Uses ModulusValueSpec() directly so Dafny can evaluate non-zero.
  // Guards with u'.Valid() (short-circuit) following InvertBezoutCondition pattern.
  ghost predicate InvertUHalveSpec(
    u': U256, u_val: int, v_val: int,
    a_is_odd: Limb, both: Limb
  ) reads u', u'.limbs {
    u'.Valid() &&
    var p := ModulusValueSpec();
    var uv := u'.ValueSpec();
    // even: halve(u)
    (a_is_odd == ZeroLimb() ==>
      (2 * uv) % p == u_val % p)
    // odd+ge: halve(u - v mod p)
    && ((a_is_odd == MaxLimb() && both == ZeroLimb()) ==>
      (2 * uv) % p == (u_val - v_val) % p)
    // odd+lt: halve(v - u mod p)
    && (both == MaxLimb() ==>
      (2 * uv) % p == (v_val - u_val) % p)
  }

  ghost function InvertBezoutCondition(
    a: U256, b: U256, u: U256, v: U256, orig: int
  ): bool
    reads a, b, u, v, a.limbs, b.limbs, u.limbs, v.limbs
  {
    a.Valid() && b.Valid() && u.Valid() && v.Valid() &&
    a.ValueSpec() % ModulusValueSpec()
      == (u.ValueSpec() * orig) % ModulusValueSpec() &&
    b.ValueSpec() % ModulusValueSpec()
      == (v.ValueSpec() * orig) % ModulusValueSpec()
  }

  // ===================================================================
  // LEMMAS
  // Reverse topological order: callers before callees.
  // ===================================================================

  // Helper: connects the Bezout invariant to the final postcondition
  // after convergence (b == 1). In a clean z3 context, this is trivial.
  lemma InvertFinalLemma(
    b_int: int, v_int: int, rv: int, orig: int, p: int)
    requires p > 1
    requires b_int == 1
    requires b_int % p == (v_int * orig) % p
    requires rv == v_int % p
    ensures (rv * orig) % p == 1
  {
    assert 1 % p == 1;
    assert (v_int * orig) % p == 1;
    // rv == v_int % p, so rv % p == v_int % p
    assert rv % p == v_int % p;
    Modular.ModMulCongruenceLemma(rv, v_int, orig, p);
  }

  // Pure-integer proof lemma for invert_step_ct.
  // Case analysis connecting phase helper specs to
  // Bezout, BitLength, GCD postconditions.
  lemma {:rlimit 100000} {:isolate_assertions} InvertStepCtProofLemma(
    a_val: int, b_val: int,
    u_val: int, v_val: int,
    av: int, bv: int,
    uv: int, vv: int,
    orig: int, p: int,
    a_odd: bool, a_lt: bool
  )
    requires p > 1 && p % 2 == 1
    requires a_val >= 0 && b_val >= 0
    requires b_val % 2 == 1
    requires u_val <= p && v_val <= p
    requires a_val % p == (u_val * orig) % p
    requires b_val % p == (v_val * orig) % p
    requires uv <= p
    // Mask semantics
    requires a_odd <==> a_val % 2 == 1
    requires a_lt <==> a_val < b_val
    // Phase 2+3: a' and b' values
    requires a_odd ==>
      av == (if a_val >= b_val
        then a_val - b_val
        else b_val - a_val) / 2
    requires !a_odd ==> av == a_val / 2
    requires (a_odd && a_lt) ==>
      bv == a_val
    requires !(a_odd && a_lt) ==>
      bv == b_val
    // Phase 4: u' (halved diff mod p)
    requires !a_odd ==>
      (2 * uv) % p == u_val % p
    requires a_odd && !a_lt ==>
      (2 * uv) % p == (u_val - v_val) % p
    requires a_odd && a_lt ==>
      (2 * uv) % p == (v_val - u_val) % p
    // Phase 4: v'
    requires (a_odd && a_lt) ==>
      vv == u_val
    requires !(a_odd && a_lt) ==>
      vv == v_val
    // Postconditions
    ensures av % p == (uv * orig) % p
    ensures bv % p == (vv * orig) % p
    ensures uv <= p
    ensures vv <= p
    ensures bv % 2 == 1
    ensures a_val > 0 ==>
      BitLength(av) + BitLength(bv)
        <= BitLength(a_val)
          + BitLength(b_val) - 1
    ensures a_val == 0 ==>
      av == 0 && bv == b_val
    ensures gcd(av, bv) == gcd(a_val, b_val)
  {
    if !a_odd {
      // Even case
      assert a_val % 2 == 0;
      assert av == a_val / 2;
      assert bv == b_val;
      assert vv == v_val;
      assert a_val == 2 * av;
      InvertStepEvenBezoutLemma(
        uv, av, u_val, a_val, orig, p);
      if a_val > 0 {
        BitLengthEvenStepLemma(a_val, b_val);
        GcdEvenOddLemma(a_val, b_val);
      }
    } else if a_lt {
      // Odd+lt case
      assert a_val % 2 == 1;
      assert a_val > 0;
      assert a_val < b_val;
      assert b_val > 0;
      ghost var diff := b_val - a_val;
      assert diff % 2 == 0;
      assert av == diff / 2;
      assert bv == a_val;
      assert vv == u_val;
      InvertStepBezoutLemma(
        uv, diff,
        v_val, u_val, b_val, a_val, orig, p);
      BitLengthOddLtStepLemma(a_val, b_val);
      GcdOddLtLemma(a_val, b_val);
    } else {
      // Odd+ge case
      assert a_val % 2 == 1;
      assert a_val > 0;
      assert a_val >= b_val;
      ghost var diff := a_val - b_val;
      assert diff % 2 == 0;
      assert av == diff / 2;
      assert bv == b_val;
      assert vv == v_val;
      InvertStepBezoutLemma(
        uv, diff,
        u_val, v_val, a_val, b_val, orig, p);
      BitLengthOddGeStepLemma(a_val, b_val);
      GcdOddGeLemma(a_val, b_val);
    }
  }

  // Bezout proof helper for the binary GCD step.
  // Given 2*u' ≡ bx-by (mod p) and X ≡ bx*orig, Y ≡ by*orig,
  // prove u'*orig ≡ (X-Y)/2 (mod p).
  lemma InvertStepBezoutLemma(
    u_prime_val: int, a_pre_shr: int,
    bez_x: int, bez_y: int,
    sub_x: int, sub_y: int,
    orig: int, p: int)
    requires p > 1
    requires p % 2 == 1
    requires a_pre_shr == sub_x - sub_y
    requires a_pre_shr % 2 == 0
    requires (2 * u_prime_val) % p == (bez_x - bez_y) % p
    requires sub_x % p == (bez_x * orig) % p
    requires sub_y % p == (bez_y * orig) % p
    ensures (u_prime_val * orig) % p
      == (a_pre_shr / 2) % p
  {
    Modular.ModSubCongruenceLemma(
      sub_x, bez_x * orig, sub_y, bez_y * orig, p);
    Modular.ModMulCongruenceLemma(
      2 * u_prime_val, bez_x - bez_y, orig, p);
    assert (2 * u_prime_val * orig) % p
      == (a_pre_shr) % p;
    assert 2 * u_prime_val * orig
      == 2 * (u_prime_val * orig);
    assert (2 * (u_prime_val * orig)) % p
      == (2 * (a_pre_shr / 2)) % p;
    Modular.Cancel2ModLemma(
      u_prime_val * orig, a_pre_shr / 2, p);
  }

  // One iteration of binary GCD for field_invert.
  // Preserves Bezout invariant:
  //   a ≡ u * orig (mod p), b ≡ v * orig (mod p)
  // Bezout proof for the even case of the binary GCD step.
  // Given 2*u' ≡ u (mod p) and a ≡ u*orig (mod p) and a even,
  // prove u'*orig ≡ a/2 (mod p).
  lemma InvertStepEvenBezoutLemma(
    uv: int, av: int, u_val: int, a_val: int,
    orig: int, p: int)
    requires p > 1
    requires p % 2 == 1
    requires (2 * uv) % p == u_val % p
    requires a_val % p == (u_val * orig) % p
    requires a_val == 2 * av
    ensures (uv * orig) % p == av % p
  {
    Modular.ModMulCongruenceLemma(2 * uv, u_val, orig, p);
    assert (2 * uv * orig) % p == a_val % p;
    assert 2 * uv * orig == 2 * (uv * orig);
    assert (2 * (uv * orig)) % p == (2 * av) % p;
    Modular.Cancel2ModLemma(uv * orig, av, p);
  }

  // Takes pre-computed XOR'd values and carry chain results.
  // Proves: d_val=0 → r_val=0. d_val>0 → r_val=W^4-d_val.
  lemma CondNeg256MaxLemma(
    d0: Limb, d1: Limb, d2: Limb, d3: Limb,
    x0: Limb, x1: Limb, x2: Limb, x3: Limb,
    r0: Limb, r1: Limb, r2: Limb, r3: Limb,
    c0: Limb, c1: Limb, c2: Limb, c3: Limb
  )
    requires LimbToInt(x0) == WORD_MAX - LimbToInt(d0)
    requires LimbToInt(x1) == WORD_MAX - LimbToInt(d1)
    requires LimbToInt(x2) == WORD_MAX - LimbToInt(d2)
    requires LimbToInt(x3) == WORD_MAX - LimbToInt(d3)
    requires (r0, c0) == AddAndCarryLimbSpec(
      x0, ZeroLimb(), LimbFromInt(1))
    requires (r1, c1) == AddAndCarryLimbSpec(
      x1, ZeroLimb(), c0)
    requires (r2, c2) == AddAndCarryLimbSpec(
      x2, ZeroLimb(), c1)
    requires (r3, c3) == AddAndCarryLimbSpec(
      x3, ZeroLimb(), c2)
    ensures
      var d_val := Limbs4Value(d0, d1, d2, d3);
      var r_val := Limbs4Value(r0, r1, r2, r3);
      && (d_val == 0 ==> r_val == 0)
      && (d_val > 0 ==>
        r_val == WORD_MODULUS4 - d_val)
  {
    GeometricSeriesW4Lemma();

    AddCarryAccountingLemma(
      x0, ZeroLimb(), LimbFromInt(1), r0, c0);
    AddCarryAccountingLemma(
      x1, ZeroLimb(), c0, r1, c1);
    AddCarryAccountingLemma(
      x2, ZeroLimb(), c1, r2, c2);
    AddCarryAccountingLemma(
      x3, ZeroLimb(), c2, r3, c3);

    AddChainTelescope4Lemma(
      LimbToInt(x0), LimbToInt(x1),
      LimbToInt(x2), LimbToInt(x3),
      0, 0, 0, 0,
      LimbToInt(r0), LimbToInt(r1),
      LimbToInt(r2), LimbToInt(r3),
      LimbToInt(c0), LimbToInt(c1),
      LimbToInt(c2), LimbToInt(c3), 1);
  }

  // CondNeg256ZeroLemma: mask=0 case. XOR+carry chain is identity.
  lemma CondNeg256ZeroLemma(
    d0: Limb, d1: Limb, d2: Limb, d3: Limb
  )
    ensures
      var cin := ZeroLimb();
      var (r0, c0) := AddAndCarryLimbSpec(
        d0, ZeroLimb(), cin);
      var (r1, c1) := AddAndCarryLimbSpec(
        d1, ZeroLimb(), c0);
      var (r2, c2) := AddAndCarryLimbSpec(
        d2, ZeroLimb(), c1);
      var (r3, c3) := AddAndCarryLimbSpec(
        d3, ZeroLimb(), c2);
      && LimbToInt(r0) == LimbToInt(d0)
      && LimbToInt(r1) == LimbToInt(d1)
      && LimbToInt(r2) == LimbToInt(d2)
      && LimbToInt(r3) == LimbToInt(d3)
  {
    var (r0, c0) := AddAndCarryLimbSpec(
      d0, ZeroLimb(), ZeroLimb());
    AddCarryAccountingLemma(
      d0, ZeroLimb(), ZeroLimb(), r0, c0);
    assert LimbToInt(c0) == 0;

    var (r1, c1) := AddAndCarryLimbSpec(
      d1, ZeroLimb(), c0);
    AddCarryAccountingLemma(
      d1, ZeroLimb(), c0, r1, c1);
    assert LimbToInt(c1) == 0;

    var (r2, c2) := AddAndCarryLimbSpec(
      d2, ZeroLimb(), c1);
    AddCarryAccountingLemma(
      d2, ZeroLimb(), c1, r2, c2);
    assert LimbToInt(c2) == 0;

    var (r3, c3) := AddAndCarryLimbSpec(
      d3, ZeroLimb(), c2);
    AddCarryAccountingLemma(
      d3, ZeroLimb(), c2, r3, c3);
  }

  // SubBoundedChain4Lemma: 4-limb sub_with_bounded_overflow
  // chain telescopes to a_val - b_val + final_borrow * W^4.
  lemma SubBoundedChain4Lemma(
    a0: Limb, a1: Limb, a2: Limb, a3: Limb,
    b0: Limb, b1: Limb, b2: Limb, b3: Limb
  )
    ensures
      var (d0, c0) := SubBoundedSpec(
        a0, b0, ZeroLimb());
      var (d1, c1) := SubBoundedSpec(
        a1, b1, c0);
      var (d2, c2) := SubBoundedSpec(
        a2, b2, c1);
      var (d3, c3) := SubBoundedSpec(
        a3, b3, c2);
      var a_val := LimbToInt(a0)
        + LimbToInt(a1) * WORD_MODULUS
        + LimbToInt(a2) * WORD_MODULUS2
        + LimbToInt(a3) * WORD_MODULUS3;
      var b_val := LimbToInt(b0)
        + LimbToInt(b1) * WORD_MODULUS
        + LimbToInt(b2) * WORD_MODULUS2
        + LimbToInt(b3) * WORD_MODULUS3;
      var d_val := LimbToInt(d0)
        + LimbToInt(d1) * WORD_MODULUS
        + LimbToInt(d2) * WORD_MODULUS2
        + LimbToInt(d3) * WORD_MODULUS3;
      && (c3 == ZeroLimb() || c3 == LimbFromInt(1))
      && (a_val >= b_val ==>
        c3 == ZeroLimb()
        && d_val == a_val - b_val)
      && (a_val < b_val ==>
        c3 == LimbFromInt(1)
        && d_val == a_val - b_val
          + WORD_MODULUS4)
  {
    var (d0, c0) := SubBoundedSpec(
      a0, b0, ZeroLimb());
    SubBoundedSpecLemma(a0, b0, ZeroLimb());
    var (d1, c1) := SubBoundedSpec(
      a1, b1, c0);
    SubBoundedSpecLemma(a1, b1, c0);
    var (d2, c2) := SubBoundedSpec(
      a2, b2, c1);
    SubBoundedSpecLemma(a2, b2, c1);
    var (d3, c3) := SubBoundedSpec(
      a3, b3, c2);
    SubBoundedSpecLemma(a3, b3, c2);
    SubChainTelescope4Lemma(
      LimbToInt(a0), LimbToInt(a1),
      LimbToInt(a2), LimbToInt(a3),
      LimbToInt(b0), LimbToInt(b1),
      LimbToInt(b2), LimbToInt(b3),
      LimbToInt(d0), LimbToInt(d1),
      LimbToInt(d2), LimbToInt(d3),
      LimbToInt(c0), LimbToInt(c1),
      LimbToInt(c2), LimbToInt(c3));
  }

  lemma WrappingNegBorrowLemma(borrow: Limb)
    requires borrow == ZeroLimb()
      || borrow == LimbFromInt(1)
    ensures
      var neg := wrapping_neg(borrow);
      && (neg == ZeroLimb()
        || neg == MaxLimb())
      && (borrow == ZeroLimb()
        ==> neg == ZeroLimb())
      && (borrow == LimbFromInt(1)
        ==> neg == MaxLimb())
  {
    WrappingNegOfBitLemma(borrow,
      wrapping_neg(borrow));
  }

  // SubChainTelescope4Lemma: 4-limb sub_with_bounded_overflow
  // chain telescopes to a_val - b_val + final_borrow * W^4.
  lemma SubChainTelescope4Lemma(
    a0v: int, a1v: int, a2v: int, a3v: int,
    b0v: int, b1v: int, b2v: int, b3v: int,
    d0v: int, d1v: int, d2v: int, d3v: int,
    c0v: int, c1v: int, c2v: int, c3v: int)
    requires d0v == a0v - b0v + c0v * WORD_MODULUS
    requires d1v == a1v - b1v - c0v
      + c1v * WORD_MODULUS
    requires d2v == a2v - b2v - c1v
      + c2v * WORD_MODULUS
    requires d3v == a3v - b3v - c2v
      + c3v * WORD_MODULUS
    ensures d0v + d1v * WORD_MODULUS
      + d2v * WORD_MODULUS2
      + d3v * WORD_MODULUS3
      == (a0v + a1v * WORD_MODULUS
        + a2v * WORD_MODULUS2
        + a3v * WORD_MODULUS3)
       - (b0v + b1v * WORD_MODULUS
        + b2v * WORD_MODULUS2
        + b3v * WORD_MODULUS3)
       + c3v * WORD_MODULUS4
  {
    assert WORD_MODULUS * WORD_MODULUS
      == WORD_MODULUS2;
    assert WORD_MODULUS * WORD_MODULUS2
      == WORD_MODULUS3;
    assert WORD_MODULUS * WORD_MODULUS3
      == WORD_MODULUS4;
  }


  // chain telescopes to a_val + b_val + cin - final_carry * W^4.
  // Used for conditional negate and modulus correction proofs.
  lemma AddChainTelescope4Lemma(
    a0v: int, a1v: int, a2v: int, a3v: int,
    b0v: int, b1v: int, b2v: int, b3v: int,
    r0v: int, r1v: int, r2v: int, r3v: int,
    c0v: int, c1v: int, c2v: int, c3v: int,
    cin: int)
    requires 0 <= cin <= 1
    requires r0v + c0v * WORD_MODULUS
      == a0v + b0v + cin
    requires r1v + c1v * WORD_MODULUS
      == a1v + b1v + c0v
    requires r2v + c2v * WORD_MODULUS
      == a2v + b2v + c1v
    requires r3v + c3v * WORD_MODULUS
      == a3v + b3v + c2v
    ensures r0v + r1v * WORD_MODULUS
      + r2v * WORD_MODULUS2
      + r3v * WORD_MODULUS3
      == (a0v + a1v * WORD_MODULUS
        + a2v * WORD_MODULUS2
        + a3v * WORD_MODULUS3)
       + (b0v + b1v * WORD_MODULUS
        + b2v * WORD_MODULUS2
        + b3v * WORD_MODULUS3)
       + cin
       - c3v * WORD_MODULUS4
  {
    assert WORD_MODULUS * WORD_MODULUS
      == WORD_MODULUS2;
    assert WORD_MODULUS * WORD_MODULUS2
      == WORD_MODULUS3;
    assert WORD_MODULUS * WORD_MODULUS3
      == WORD_MODULUS4;
  }

}
