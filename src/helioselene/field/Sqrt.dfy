include "Pow.dfy"

module FieldSqrt {
  import opened FieldBase
  import opened FieldArith
  import opened FieldPow
  import opened CryptoBigint_0_5_5_Limb
  import opened CryptoBigint_0_5_5_U256
  import opened Limbs
  import opened PowMod
  import opened BitOps
  import opened NumberTheory
  import opened FermatLittle
  import Modular
  import Power = Std.Arithmetic.Power
  import DivMod = Std.Arithmetic.DivMod

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L633-L705
  // sqrt: computes square root via a^((p+1)/4) for p ≡ 3 (mod 4).
  // Returns (is_sqrt, result): if is_sqrt, result^2 == a mod p; otherwise a has no square root.
  method
    {:timeLimit 500}
    {:fuel pow_mod, 0}
    {:fuel TopBits, 0}
    {:fuel LimbsValueSpec, 0}
    field_sqrt(a: HelioseleneField)
    returns (is_sqrt: bool, result: HelioseleneField)
    requires ValidField(a)
    ensures ValidField(result)
    ensures is_sqrt ==>
      (result.inner.ValueSpec() * result.inner.ValueSpec())
        % ModulusValueSpec() == a.inner.ValueSpec()
    ensures is_sqrt ==> result.inner.ValueSpec() % 2 == 0
    ensures !is_sqrt ==>
      forall x: int :: 0 <= x < ModulusValueSpec() ==>
        (x * x) % ModulusValueSpec() != a.inner.ValueSpec()
  {
    // GHOST CODE
    ghost var a_val := a.inner.ValueSpec();
    ghost var p := ModulusValueSpec();
    ghost var ghost_exp: int := 15;

    // original code:
    // let mut table = [Self::ONE; 16];
    // table[1] = *self;
    // table[2] = self.square();
    // ... table[15] = table[14] * self;
    var table := build_pow_table(a);
    ghost var table_snapshot := table[..];
    ghost var table_ok :=
      forall i :: 0 <= i < 16 ==>
        table_snapshot[i].inner.Valid() &&
        table_snapshot[i].inner.ValueSpec() < p &&
        table_snapshot[i].inner.ValueSpec() == pow_mod(a_val, i, p);
    assert table_ok;

    // original code:
    // let mut res = table[15];
    var res := table[15];

    // LEMMAS
    PowModAddLemma(a_val, 15, 15, p);

    assert {:split_here} true;

    // original code:
    // let four_zero = res.square();
    var four_zero := field_square(res);

    // GHOST CODE
    ghost_exp := 30;

    // LEMMAS
    PowModAddLemma(a_val, 30, 30, p);

    assert {:split_here} true;

    // original code:
    // let four_zero_zero = four_zero.square();
    var four_zero_zero := field_square(four_zero);

    // GHOST CODE
    ghost_exp := 60;

    // LEMMAS
    PowModAddLemma(a_val, 60, 60, p);

    assert {:split_here} true;

    // original code:
    // res = four_zero_zero.square();
    res := field_square(four_zero_zero);

    // GHOST CODE
    ghost_exp := 120;

    // LEMMAS
    PowModAddLemma(a_val, 120, 120, p);

    assert {:split_here} true;

    // original code:
    // res = res.square();
    res := field_square(res);

    // GHOST CODE
    ghost_exp := 240;

    // LEMMAS
    PowModAddLemma(a_val, 240, 15, p);

    assert {:split_here} true;

    // original code:
    // res *= &table[15];
    res := field_mul(res, table[15]);

    // GHOST CODE
    ghost_exp := 255;

    // original code:
    // let old_res = res;
    var old_res := res;

    // GHOST CODE
    ghost var old_ghost_exp: int := ghost_exp;

    // original code:
    // for _ in 0 .. 8 {
    //   res = res.square();
    // }
    assert {:split_here} true;
    assert ghost_exp == 255 * MathHelpers.pow2(0) by {
      assert MathHelpers.pow2(0) == 1;
    }
    for {:isolate_assertions} j := 0 to 8
      modifies {}
      invariant ValidField(res)
      invariant ghost_exp == 255 * MathHelpers.pow2(j)
      invariant res.inner.ValueSpec()
        == pow_mod(a_val, ghost_exp, p)
    {
      // LEMMAS
      ghost var res_val := res.inner.ValueSpec();
      PowModSquareStepLemma(a_val, ghost_exp, p, res_val);

      // Original code:
      // res = res.square()
      res := field_square(res);

      // GHOST CODE
      ghost_exp := ghost_exp * 2;
      MathHelpers.Pow2DoubleLemma(j);
    }
    assert old_res.inner.ValueSpec()
      == pow_mod(a_val, old_ghost_exp, p);

    // LEMMAS
    PowModAddLemma(a_val, ghost_exp, old_ghost_exp, p);

    // original code:
    // res *= &old_res;
    res := field_mul(res, old_res);

    // GHOST CODE
    ghost_exp := ghost_exp + old_ghost_exp;

    // original code:
    // let old_res = res;
    old_res := res;

    // GHOST CODE
    old_ghost_exp := ghost_exp;

    // original code:
    // for _ in 0 .. 16 {
    //   res = res.square();
    // }
    assert {:split_here} true;
    assert ghost_exp == 65535 * MathHelpers.pow2(0) by {
      assert MathHelpers.pow2(0) == 1;
      assert MathHelpers.pow2(8) == 256;
    }
    for {:isolate_assertions} j := 0 to 16
      modifies {}
      invariant ValidField(res)
      invariant ghost_exp == 65535 * MathHelpers.pow2(j)
      invariant res.inner.ValueSpec()
        == pow_mod(a_val, ghost_exp, p)
    {
      // LEMMAS
      ghost var res_val := res.inner.ValueSpec();
      PowModSquareStepLemma(a_val, ghost_exp, p, res_val);

      // Original code:
      // res = res.square();
      res := field_square(res);

      // GHOST CODE
      ghost_exp := ghost_exp * 2;
      MathHelpers.Pow2DoubleLemma(j);
    }
    assert old_res.inner.ValueSpec()
      == pow_mod(a_val, old_ghost_exp, p);

    // LEMMAS
    PowModAddLemma(a_val, ghost_exp, old_ghost_exp, p);

    // original code:
    // res *= old_res;
    res := field_mul(res, old_res);

    // GHOST CODE
    ghost_exp := ghost_exp + old_ghost_exp;

    // original code:
    // let old_res = res;
    old_res := res;

    // GHOST CODE
    old_ghost_exp := ghost_exp;

    // original code:
    // for _ in 0 .. 32 {
    //   res = res.square();
    // }
    assert {:split_here} true;
    assert ghost_exp == 4294967295 * MathHelpers.pow2(0) by {
      assert MathHelpers.pow2(0) == 1;
      assert MathHelpers.pow2(16) == 65536;
    }
    for {:isolate_assertions} j := 0 to 32
      modifies {}
      invariant ValidField(res)
      invariant ghost_exp == 4294967295 * MathHelpers.pow2(j)
      invariant res.inner.ValueSpec()
        == pow_mod(a_val, ghost_exp, p)
    {
      // LEMMAS
      ghost var res_val := res.inner.ValueSpec();
      PowModSquareStepLemma(a_val, ghost_exp, p, res_val);

      // Original code:
      // res = res.square();
      res := field_square(res);

      // Ghost code
      ghost_exp := ghost_exp * 2;
      MathHelpers.Pow2DoubleLemma(j);
    }
    assert old_res.inner.ValueSpec()
      == pow_mod(a_val, old_ghost_exp, p);

    // LEMMAS
    PowModAddLemma(a_val, ghost_exp, old_ghost_exp, p);

    // original code:
    // res *= old_res;
    res := field_mul(res, old_res);

    // GHOST CODE
    ghost_exp := ghost_exp + old_ghost_exp;

    // original code:
    // let old_res = res;
    old_res := res;

    // GHOST CODE
    old_ghost_exp := ghost_exp;

    // original code:
    // for _ in 0 .. 64 {
    //   res = res.square();
    // }
    assert {:split_here} true;
    assert ghost_exp == 18446744073709551615 * MathHelpers.pow2(0) by {
      assert MathHelpers.pow2(0) == 1;
      MathHelpers.Pow2To32Lemma();
    }
    for {:isolate_assertions} j := 0 to 64
      modifies {}
      invariant ValidField(res)
      invariant ghost_exp
        == 18446744073709551615 * MathHelpers.pow2(j)
      invariant res.inner.ValueSpec()
        == pow_mod(a_val, ghost_exp, p)
    {
      // LEMMAS
      ghost var res_val := res.inner.ValueSpec();
      PowModSquareStepLemma(a_val, ghost_exp, p, res_val);

      // Original code:
      // res = res.square();
      res := field_square(res);

      // GHOST CODE
      ghost_exp := ghost_exp * 2;
      MathHelpers.Pow2DoubleLemma(j);
    }
    assert old_res.inner.ValueSpec()
      == pow_mod(a_val, old_ghost_exp, p);

    // LEMMAS
    PowModAddLemma(a_val, ghost_exp, old_ghost_exp, p);

    // original code:
    // res *= old_res;
    res := field_mul(res, old_res);
    // GHOST CODE
    ghost_exp := ghost_exp + old_ghost_exp;
    assert {:isolate} ghost_exp
      == 340282366920938463463374607431768211455 by {
      MathHelpers.Pow2To64Lemma();
    }

    assert {:split_here} true;

    // original code:
    // let mut bits = 0;
    var bits: int := 0;
    // original code:
    // for bit in MODULUS_PLUS_ONE_DIV_FOUR.to_le_bits().iter().take(253).rev().skip(128) {
    //   bits <<= 1;
    //   let bit = u8::from(*bit);
    //   bits |= bit;
    //
    //   res = res.square();
    //
    //   if (bits & (1 << 3)) != 0 {
    //     res *= table[usize::from(bits)];
    //     bits = 0;
    //   }
    // }
    var sqrt_exp_limbs: array<Limb> := new Limb[U256_LIMBS][
      LimbFromInt(0xfe6142da37c477d5),
      LimbFromInt(0xfdcd5207465a7cc5),
      LimbFromInt(0xffffffffffffffff),
      LimbFromInt(0x1fffffffffffffff)
    ];

    // GHOST CODE
    SqrtExponentValueLemma();
    ghost var sqrt_exp_val := LimbsValueSpec(sqrt_exp_limbs[..]);
    assert {:isolate} sqrt_exp_val == SqrtExponent() by {
      assert sqrt_exp_limbs[..] == [
        LimbFromInt(0xfe6142da37c477d5),
        LimbFromInt(0xfdcd5207465a7cc5),
        LimbFromInt(0xffffffffffffffff),
        LimbFromInt(0x1fffffffffffffff)
      ];
    }
    // LEMMAS: Prove TopBits(se, 131) == ghost_exp
    assert {:isolate} ghost_exp + bits
      == TopBits(sqrt_exp_val, 255 - 124) by {
      SqrtTopBitsInitLemma(ghost_exp, sqrt_exp_val);
    }

    assert {:split_here} true;
    ghost var sqrt_exp_seq := sqrt_exp_limbs[..];
    for i := 125 downto 0
      modifies {}
      invariant ValidField(res)
      invariant 0 <= ghost_exp
      invariant res.inner.ValueSpec()
        == pow_mod(a_val, ghost_exp, p)
      invariant 0 <= bits < 8
      invariant ghost_exp + bits
        == TopBits(sqrt_exp_val, 256 - i)
      invariant sqrt_exp_limbs[..] == sqrt_exp_seq
      invariant LimbsValueSpec(sqrt_exp_seq) == sqrt_exp_val
      invariant table[..] == table_snapshot
    {
      // Bit-extraction + squaring step (isolated in helper method).
      // Original code:
      //   bits <<= 1;
      //   let bit = u8::from(*bit);
      //   bits |= bit;
      //
      //   res = res.square();
      res, bits, ghost_exp := sqrt_window_square(
        sqrt_exp_limbs, sqrt_exp_seq, sqrt_exp_val,
        a_val, p,
        i, res, bits, ghost_exp);
      assert {:split_here} true;

      //   if (bits & (1 << 3)) != 0 {
      //     res *= table[usize::from(bits)];
      //     bits = 0;
      //  }
      if bits >= 8 {
        // ORIGINAL CODE
        assert table[bits] == table_snapshot[bits];
        SqrtLoopMulBridgeLemma(
          table_snapshot, a_val, p,
          ghost_exp, bits, res.inner.ValueSpec());
        // Original code:
        //     res *= table[usize::from(bits)];
        res := field_mul(res, table[bits]);

        // GHOST CODE
        ghost_exp := ghost_exp + bits;

        // Original code:
        //     bits = 0;
        bits := 0;
      }
    }
    assert {:split_here} true;
    // LEMMAS: ghost_exp + bits == se
    assert ghost_exp + bits == sqrt_exp_val by {
      SqrtTopBitsFinalizeLemma(sqrt_exp_val, ghost_exp, bits);
    }
    assert {:split_here} true;

    // Post-loop: table multiply, conditional negate, square, limb compare,
    // and final postcondition proofs. Isolated in a helper method so the
    // main method's VC doesn't have to carry the full final-check context.
    // Original code:
    // // Handle the final window
    // res *= table[usize::from(bits)];
    //
    // // Normalize to the even choice of square root
    // // `let ()` is used to assert how `conditional_negate` operates in-place
    // let () = res.conditional_negate(res.is_odd());
    //
    // CtOption::new(res, res.square().ct_eq(self))
    is_sqrt, result := sqrt_post_loop(
      a, a_val, p, sqrt_exp_val,
      table, table_snapshot,
      res, bits, ghost_exp);
  }


  // ===================================================================
  // POST-LOOP (extracted as method so its VC is isolated)
  // ===================================================================

  // Post-loop: table multiply by residual bits, conditional negate to
  // produce even output, square-and-check against input, and discharge
  // the three method-level postconditions.
  method
    {:timeLimit 180}
    {:fuel pow_mod, 0}
    {:fuel TopBits, 0}
    {:fuel LimbsValueSpec, 0}
    sqrt_post_loop(
      a: HelioseleneField,
      ghost a_val: int, ghost p: int,
      ghost sqrt_exp_val: int,
      table: array<HelioseleneField>,
      ghost table_snapshot: seq<HelioseleneField>,
      res_in: HelioseleneField,
      bits_in: int,
      ghost ghost_exp_in: int)
    returns (is_sqrt: bool, result: HelioseleneField)
    modifies {}
    requires ValidField(a)
    requires p == ModulusValueSpec()
    requires a_val == a.inner.ValueSpec()
    requires 0 <= a_val < p
    requires sqrt_exp_val == SqrtExponent()
    requires table.Length == 16
    requires table[..] == table_snapshot
    requires |table_snapshot| == 16
    requires forall k | 0 <= k < 16 ::
      table_snapshot[k].inner.Valid() &&
      table_snapshot[k].inner.ValueSpec() < p &&
      table_snapshot[k].inner.ValueSpec() == pow_mod(a_val, k, p)
    requires ValidField(res_in)
    requires 0 <= ghost_exp_in
    requires 0 <= bits_in < 8
    requires res_in.inner.ValueSpec() == pow_mod(a_val, ghost_exp_in, p)
    requires ghost_exp_in + bits_in == sqrt_exp_val
    ensures ValidField(result)
    ensures is_sqrt ==>
      (result.inner.ValueSpec() * result.inner.ValueSpec())
        % p == a_val
    ensures is_sqrt ==> result.inner.ValueSpec() % 2 == 0
    ensures !is_sqrt ==>
      forall x: int :: 0 <= x < p ==>
        (x * x) % p != a_val
  {
    // GHOST CODE
    // table-multiply by residual bits
    assert table[bits_in] == table_snapshot[bits_in];
    SqrtLoopMulBridgeLemma(
      table_snapshot, a_val, p,
      ghost_exp_in, bits_in, res_in.inner.ValueSpec());

    // Original code:
    // // Handle the final window
    // res *= table[usize::from(bits)];
    var res := field_mul(res_in, table[bits_in]);

    // GHOST CODE
    ghost var r := res.inner.ValueSpec();
    assert r == pow_mod(a_val, sqrt_exp_val, p) by {
      assert ghost_exp_in + bits_in == sqrt_exp_val;
    }
    PowModBoundLemma(a_val, sqrt_exp_val, p);
    assert {:split_here} true;

    // Original code:
    // // Normalize to the even choice of square root
    // // `let ()` is used to assert how `conditional_negate` operates in-place
    // let () = res.conditional_negate(res.is_odd());
    var res_is_odd := field_is_odd(res);
    if res_is_odd {
      res := field_neg(res);
    }
    // GOHST CODE
    assert {:split_here} true;

    // Original code:
    // CtOption::new(res, res.square().ct_eq(self))
    //
    // This implements the square
    var sq := field_square(res);
    assert {:split_here} true;

    // Original code:
    // CtOption::new(res, res.square().ct_eq(self))
    //
    // This implements the ct_eq
    var sq_limbs := sq.inner.as_limbs();
    var a_limbs := a.inner.as_limbs();
    var sq_eq_a := true;
    var k := 0;
    while k < U256_LIMBS
      modifies {}
      decreases U256_LIMBS - k
      invariant 0 <= k <= U256_LIMBS
      invariant sq_eq_a <==> (sq_limbs[..k] == a_limbs[..k])
    {
      if sq_limbs[k] != a_limbs[k] {
        sq_eq_a := false;
      }
      k := k + 1;
    }

    // GHOST CODE
    assert sq_eq_a <==> (sq_limbs[..] == a_limbs[..]) by {
      assert sq_limbs[..] == sq_limbs[..k];
      assert a_limbs[..] == a_limbs[..k];
    }
    assert {:split_here} true;

    // Original code:
    // CtOption::new(res, res.square().ct_eq(self))
    //
    // This implements the CtOption::new
    is_sqrt := sq_eq_a;
    result := res;

    // GHOST CODE
    assert a_val == LimbsValueSpec(a_limbs[..]) by {
      assert a_limbs == a.inner.limbs;
    }
    assert sq.inner.ValueSpec() == LimbsValueSpec(sq_limbs[..]) by {
      assert sq_limbs == sq.inner.limbs;
    }
    SqEqValueSpecLemma(
      sq_limbs[..], a_limbs[..],
      sq.inner.ValueSpec(), a_val, sq_eq_a);
    SqrtCheckBridgeLemma(
      r, res.inner.ValueSpec(), sq.inner.ValueSpec(),
      a_val, p, res_is_odd, sq_eq_a, sqrt_exp_val);
  }

  // ===================================================================
  // WINDOWED LOOP BIT-EXTRACT + SQUARE STEP (extracted as method)
  // ===================================================================

  // Single bit-extraction + squaring step of the windowed loop.
  // Extracted as a method so its VC is isolated; the main method's
  // loop just sees the ensures, not the body's bit-extraction work.
  // The table-multiplication step stays inline in the caller so this
  // method has no table-related preconditions.
  method
    {:timeLimit 60}
    {:fuel pow_mod, 0}
    {:fuel TopBits, 0}
    {:fuel LimbsValueSpec, 0}
    sqrt_window_square(
      sqrt_exp_limbs: array<Limb>,
      ghost sqrt_exp_seq: seq<Limb>,
      ghost sqrt_exp_val: int,
      ghost a_val: int, ghost p: int,
      i: int,
      res_in: HelioseleneField,
      bits_in: int,
      ghost ghost_exp_in: int)
    returns (
      res_out: HelioseleneField,
      bits_out: int,
      ghost ghost_exp_out: int)
    modifies {}
    requires p == ModulusValueSpec()
    requires 0 <= a_val < p
    requires 0 <= sqrt_exp_val
    requires 0 <= ghost_exp_in
    requires 0 <= bits_in < 8
    requires 0 <= i <= 124
    requires sqrt_exp_limbs.Length == U256_LIMBS
    requires sqrt_exp_limbs[..] == sqrt_exp_seq
    requires |sqrt_exp_seq| == U256_LIMBS
    requires LimbsValueSpec(sqrt_exp_seq) == sqrt_exp_val
    requires ValidField(res_in)
    requires res_in.inner.ValueSpec() == pow_mod(a_val, ghost_exp_in, p)
    requires ghost_exp_in + bits_in == TopBits(sqrt_exp_val, 255 - i)
    ensures ValidField(res_out)
    ensures 0 <= ghost_exp_out
    ensures res_out.inner.ValueSpec() == pow_mod(a_val, ghost_exp_out, p)
    ensures 0 <= bits_out < 16
    ensures ghost_exp_out + bits_out == TopBits(sqrt_exp_val, 256 - i)
  {
    // Original code:
    //   bits <<= 1;
    //   let bit = u8::from(*bit);
    //   bits |= bit;
    var old_bits := bits_in;
    var limb_idx := i / 64;
    var bit_offset := i % 64;
    MathHelpers.Pow2PositiveLemma(bit_offset);
    var bit: int := (sqrt_exp_limbs[limb_idx].word
      as int / MathHelpers.pow2(bit_offset)) % 2;
    bits_out := old_bits * 2 + bit;

    // GHOST CODE
    assert sqrt_exp_limbs[limb_idx] == sqrt_exp_seq[limb_idx];

    SqrtWindowStepLemma(
      sqrt_exp_seq, sqrt_exp_val,
      i, ghost_exp_in, old_bits, bit);

    PowModSquareStepLemma(
      a_val, ghost_exp_in, p, res_in.inner.ValueSpec());

    // Original code:
    //   res = res.square();
    res_out := field_square(res_in);
    ghost_exp_out := ghost_exp_in * 2;
  }

  // ===================================================================
  // BRIDGE LEMMAS
  // ===================================================================


  // Proves that multiplying by table[bits] maintains pow_mod tracking.
  lemma SqrtLoopMulLemma(
    ghost_exp: int, bits: int,
    res_val: int, table_val: int,
    a_val: int, p: int)
    requires p == ModulusValueSpec()
    requires 0 <= a_val < p
    requires 0 <= ghost_exp
    requires 0 <= bits < 16
    requires res_val == pow_mod(a_val, ghost_exp, p)
    requires table_val == pow_mod(a_val, bits, p)
    requires 0 <= res_val < p
    requires 0 <= table_val < p
    ensures (res_val * table_val) % p
      == pow_mod(a_val, ghost_exp + bits, p)
  {
    PowModAddLemma(a_val, ghost_exp, bits, p);
  }

  // Combined table-lookup + multiplication bridge over the value-type
  // snapshot seq.  Uses opaque TableValid so callers carry the table
  // facts as a single cheap bool instead of an expanded forall.
  lemma SqrtLoopMulBridgeLemma(
    table: seq<HelioseleneField>,
    a_val: int, p: int,
    ghost_exp: int, bits: int, res_val: int)
    requires p == ModulusValueSpec()
    requires 0 <= a_val < p
    requires |table| == 16
    requires forall i :: 0 <= i < 16 ==>
      table[i].inner.Valid() &&
      table[i].inner.ValueSpec() < p &&
      table[i].inner.ValueSpec() == pow_mod(a_val, i, p)
    requires 0 <= ghost_exp
    requires 0 <= bits < 16
    requires res_val == pow_mod(a_val, ghost_exp, p)
    requires 0 <= res_val < p
    ensures table[bits].inner.Valid()
    ensures table[bits].inner.ValueSpec() < p
    ensures table[bits].inner.ValueSpec() == pow_mod(a_val, bits, p)
    ensures (res_val * table[bits].inner.ValueSpec()) % p
      == pow_mod(a_val, ghost_exp + bits, p)
  {
    PowModAddLemma(a_val, ghost_exp, bits, p);
  }

  // Final-postcondition bridge: transform limb-level equality (sq_limbs ==
  // a_limbs) through ValueSpec into the three method postconditions via
  // SqrtCheckBridgeLemma. Called once from field_sqrt's tail.
  lemma {:isolate_assertions} SqrtFinalPostBridgeLemma(
    r: int, res_val: int, sq_val: int,
    sq_limbs: seq<Limb>, a_limbs: seq<Limb>,
    a_val: int, p: int,
    res_is_odd: bool, sq_eq_a: bool,
    sqrt_exp_val: int)
    requires |sq_limbs| == 4 && |a_limbs| == 4
    requires p == ModulusValueSpec()
    requires 0 <= a_val < p
    requires 0 <= r < p
    requires sqrt_exp_val == SqrtExponent()
    requires r == pow_mod(a_val, sqrt_exp_val, p)
    requires a_val == LimbsValueSpec(a_limbs)
    requires sq_val == LimbsValueSpec(sq_limbs)
    requires res_is_odd <==> r % 2 == 1
    requires res_is_odd ==> res_val == (p - r) % p
    requires !res_is_odd ==> res_val == r
    requires sq_val == (res_val * res_val) % p
    requires sq_eq_a <==> (sq_limbs == a_limbs)
    ensures res_val % 2 == 0
    ensures sq_eq_a ==> (res_val * res_val) % p == a_val
    ensures !sq_eq_a ==>
      forall x :: 0 <= x < p ==> (x * x) % p != a_val
  {
    SqEqValueSpecLemma(sq_limbs, a_limbs, sq_val, a_val, sq_eq_a);
    SqrtCheckBridgeLemma(
      r, res_val, sq_val, a_val, p,
      res_is_odd, sq_eq_a, sqrt_exp_val);
  }

  // Single squaring step: (pow_mod(base, exp, p))^2 == pow_mod(base, exp*2, p).
  lemma PowModSquareStepLemma(
    base: int, exp: int, p: int, res_val: int)
    requires p == ModulusValueSpec()
    requires 0 <= base < p
    requires 0 <= exp
    requires res_val == pow_mod(base, exp, p)
    ensures (res_val * res_val) % p == pow_mod(base, exp * 2, p)
  {
    PowModAddLemma(base, exp, exp, p);
  }

  // Helper: compute window bit and update TopBits relation for the sqrt loop.
  // Called from field_sqrt's windowed loop body to discharge the
  // ghost_exp/bits/TopBits relationship in a single isolated proof context.
  // Takes a seq (not array) to avoid heap-frame reasoning at the call site.
  lemma {:isolate_assertions} SqrtWindowStepLemma(
    sqrt_exp_seq: seq<Limb>,
    sqrt_exp_val: int,
    i: int, ghost_exp: int, bits: int,
    bit: int)
    requires |sqrt_exp_seq| == U256_LIMBS
    requires LimbsValueSpec(sqrt_exp_seq) == sqrt_exp_val
    requires 0 <= bits < 8
    requires 0 <= i <= 124
    requires ghost_exp + bits == TopBits(sqrt_exp_val, 255 - i)
    requires bit == (sqrt_exp_seq[i / 64].word as int / MathHelpers.pow2(i % 64)) % 2
    ensures 0 <= bits * 2 + bit < 16
    ensures ghost_exp * 2 + (bits * 2 + bit)
      == TopBits(sqrt_exp_val, 256 - i)
  {
    // bit is 0 or 1
    assert 0 <= bit < 2 by {
      MathHelpers.Pow2PositiveLemma(i % 64);
    }
    assert 0 <= i < 256;
    assert (forall j :: 0 <= j < 4 ==>
      0 <= LimbToInt(sqrt_exp_seq[j]) < WORD_MODULUS);
    // Link bit extraction to TopBits step
    BitExtractLemma(sqrt_exp_seq, i);
    assert bit == (sqrt_exp_val / MathHelpers.pow2(i)) % 2;
    // TopBits step: k = 255 - i
    ghost var k := 255 - i;
    TopBitsStepLemma(sqrt_exp_val, k);
    // bits window stays in range
    assert bits * 2 + bit < 16;
    // Update TopBits relation
    calc {
      ghost_exp * 2 + (bits * 2 + bit);
      == { }
      (ghost_exp + bits) * 2 + bit;
      == { }
      TopBits(sqrt_exp_val, 255 - i) * 2 + bit;
      == { }
      TopBits(sqrt_exp_val, 256 - i);
    }
  }

  // Table entry lookup: specialize build_pow_table postcondition for a single index.
  lemma TableEntryPowModLemma(
    table: array<HelioseleneField>,
    a_val: int, p: int, k: int)
    requires table.Length == 16
    requires p == ModulusValueSpec()
    requires 0 <= a_val < p
    requires 0 <= k < 16
    requires forall i :: 0 <= i < 16 ==>
      table[i].inner.Valid() &&
      table[i].inner.ValueSpec() < p &&
      table[i].inner.ValueSpec() == pow_mod(a_val, i, p)
    ensures table[k].inner.ValueSpec() == pow_mod(a_val, k, p)
    ensures table[k].inner.ValueSpec() < p
  {
    assert table[k].inner.ValueSpec() == pow_mod(a_val, k, p);
    assert table[k].inner.ValueSpec() < p;
  }

  // Post-loop: normalization + postcondition proof.
  lemma SqrtCheckLemma(
    r: int, res_val: int, sq_val: int,
    a_val: int, p: int,
    res_is_odd: bool, sq_eq_a: bool)
    requires p == ModulusValueSpec()
    requires 0 <= a_val < p
    requires 0 <= r < p
    requires r == pow_mod(a_val, SqrtExponent(), p)
    requires res_is_odd <==> r % 2 == 1
    requires res_is_odd ==> res_val == (p - r) % p
    requires !res_is_odd ==> res_val == r
    requires sq_val == (res_val * res_val) % p
    requires sq_eq_a <==> (sq_val == a_val)
    ensures res_val % 2 == 0
    ensures sq_eq_a ==> (res_val * res_val) % p == a_val
    ensures !sq_eq_a ==>
      forall x :: 0 <= x < p ==> (x * x) % p != a_val
  {
    SqrtCheckEvenLemma(res_val, r, p, res_is_odd);
    SqrtCheckSquareLemma(sq_val, r, p, res_is_odd);
    if !sq_eq_a {
      EulerCriterionLemma(a_val, p, r);
    }
  }

  // ===================================================================
  // SUPPORTING LEMMAS
  // ===================================================================

  // Proves TopBits(se, 131) == ladder_exp for the windowed loop init.
  lemma {:isolate_assertions} SqrtTopBitsInitLemma(
    ladder_exp: int, sqrt_exp_val: int)
    requires ladder_exp
      == 340282366920938463463374607431768211455
    requires sqrt_exp_val == SqrtExponent()
    ensures ladder_exp + 0
      == TopBits(sqrt_exp_val, 131)
  {
    ghost var lower_val := LimbsValueSpec([
      LimbFromInt(0xfe6142da37c477d5),
      LimbFromInt(0x1dcd5207465a7cc5),
      ZeroLimb(),
      ZeroLimb()
    ]);
    assert {:split_here} true;
    MathHelpers.Pow2PositiveLemma(125);
    assert {:split_here} true;
    SqrtExponentDecompositionLemma(
      ladder_exp,
      ladder_exp * MathHelpers.pow2(125),
      lower_val);
    assert {:split_here} true;
    assert sqrt_exp_val
      == ladder_exp * MathHelpers.pow2(125) + lower_val;
    assert 0 <= lower_val;
    assert {:split_here} true;
    assert lower_val < MathHelpers.pow2(125) by {
      MathHelpers.Pow2To125Lemma();
    }
    assert {:split_here} true;
    DivMod.LemmaFundamentalDivModConverse(
      sqrt_exp_val, MathHelpers.pow2(125),
      ladder_exp, lower_val);
    assert {:split_here} true;
  }

  // TopBits(se, 256) == se: finalize ghost_exp + bits.
  lemma {:isolate_assertions} SqrtTopBitsFinalizeLemma(
    sqrt_exp_val: int, ghost_exp: int, bits: int)
    requires 0 <= sqrt_exp_val
    requires ghost_exp + bits == TopBits(sqrt_exp_val, 256)
    ensures ghost_exp + bits == sqrt_exp_val
  {
    TopBits256Lemma(sqrt_exp_val);
  }

  // Seq inequality for length-4 limbs yields a concrete index witness.
  lemma Seq4DiffIndexLemma(s1: seq<Limb>, s2: seq<Limb>)
    requires |s1| == 4 && |s2| == 4
    requires s1 != s2
    ensures exists j :: 0 <= j < 4 && s1[j] != s2[j]
  {
    if s1[0] != s2[0] {
      assert (exists j :: j == 0 && 0 <= j < 4 && s1[j] != s2[j]) by {
        assert 0 <= 0 < 4;
        assert s1[0] != s2[0];
      }
    } else if s1[1] != s2[1] {
      assert (exists j :: j == 1 && 0 <= j < 4 && s1[j] != s2[j]) by {
        assert 0 <= 1 < 4;
        assert s1[1] != s2[1];
      }
    } else if s1[2] != s2[2] {
      assert (exists j :: j == 2 && 0 <= j < 4 && s1[j] != s2[j]) by {
        assert 0 <= 2 < 4;
        assert s1[2] != s2[2];
      }
    } else {
      assert s1[3] != s2[3];
      assert (exists j :: j == 3 && 0 <= j < 4 && s1[j] != s2[j]) by {
        assert 0 <= 3 < 4;
        assert s1[3] != s2[3];
      }
    }
  }

  // Limb sequence equality implies ValueSpec equality (and conversely via uniqueness lemma).
  lemma {:isolate_assertions} SqEqValueSpecLemma(
    sq_limbs: seq<Limb>, a_limbs: seq<Limb>,
    sq_val: int, a_val: int, sq_eq_a: bool)
    requires |sq_limbs| == 4 && |a_limbs| == 4
    requires sq_val == LimbsValueSpec(sq_limbs)
    requires a_val == LimbsValueSpec(a_limbs)
    requires sq_eq_a <==> (sq_limbs == a_limbs)
    ensures sq_eq_a <==> (sq_val == a_val)
  {
    if sq_eq_a {
      assert sq_limbs == a_limbs;
      assert sq_val == a_val;
    } else {
      assert sq_limbs != a_limbs;
      Seq4DiffIndexLemma(sq_limbs, a_limbs);
      LimbsDifferValueDifferLemma(sq_limbs, a_limbs);
    }
  }

  // Bridge lemma: discharge SqrtCheckLemma preconditions from local facts.
  lemma {:isolate_assertions} SqrtCheckBridgeLemma(
    r: int, res_val: int, sq_val: int,
    a_val: int, p: int,
    res_is_odd: bool, sq_eq_a: bool,
    sqrt_exp_val: int)
    requires p == ModulusValueSpec()
    requires 0 <= a_val < p
    requires 0 <= r < p
    requires sqrt_exp_val == SqrtExponent()
    requires r == pow_mod(a_val, sqrt_exp_val, p)
    requires res_is_odd <==> r % 2 == 1
    requires res_is_odd ==> res_val == (p - r) % p
    requires !res_is_odd ==> res_val == r
    requires sq_val == (res_val * res_val) % p
    requires sq_eq_a <==> (sq_val == a_val)
    ensures res_val % 2 == 0
    ensures sq_eq_a ==> (res_val * res_val) % p == a_val
    ensures !sq_eq_a ==>
      forall x :: 0 <= x < p ==> (x * x) % p != a_val
  {
    SqrtCheckLemma(
      r, res_val, sq_val,
      a_val, p, res_is_odd, sq_eq_a);
  }

  // Proves the sqrt result is even after conditional negation.
  lemma SqrtCheckEvenLemma(
    res_val: int, r: int, p: int,
    res_is_odd: bool)
    requires p == ModulusValueSpec()
    requires 0 <= r < p
    requires res_is_odd ==> r % 2 == 1
    requires !res_is_odd ==> r % 2 == 0
    requires res_is_odd ==> res_val == (p - r) % p
    requires !res_is_odd ==> res_val == r
    ensures res_val % 2 == 0
  {
    ModulusCongruence3Mod4Lemma();
    if res_is_odd {
      assert r > 0;
      DivMod.LemmaSmallMod(p - r, p);
    }
  }

  // Rewrite pow_mod exponent equality.
  lemma PowModRewriteLemma(
    base: int, exp1: int, exp2: int, p: int)
    requires p == ModulusValueSpec()
    requires 0 <= base < p
    requires 0 <= exp1
    requires 0 <= exp2
    requires exp1 == exp2
    ensures pow_mod(base, exp1, p) == pow_mod(base, exp2, p)
  {
  }

  // Proves sq == (r * r) % p after conditional negation.
  lemma SqrtCheckSquareLemma(
    sq_val: int, r: int, p: int,
    res_is_odd: bool)
    requires p == ModulusValueSpec()
    requires p > 0
    requires 0 <= r < p
    requires res_is_odd ==> r % 2 == 1
    requires res_is_odd ==>
      sq_val == (((p - r) % p) * ((p - r) % p)) % p
    requires !res_is_odd ==>
      sq_val == (r * r) % p
    ensures sq_val == (r * r) % p
  {
    if res_is_odd {
      assert r > 0;
      DivMod.LemmaSmallMod(p - r, p);
      NegSquareModLemma(r, p);
    }
  }

  // SqrtExponent() equals (p+1)/4 and the constant limbs represent it.
  lemma SqrtExponentValueLemma()
    ensures SqrtExponent() == (ModulusValueSpec() + 1) / 4
    ensures SqrtExponent() < ModulusValueSpec()
    ensures LimbsValueSpec([
      LimbFromInt(0xfe6142da37c477d5),
      LimbFromInt(0xfdcd5207465a7cc5),
      LimbFromInt(0xffffffffffffffff),
      LimbFromInt(0x1fffffffffffffff)
    ]) == SqrtExponent()
  {
    assert SqrtExponent() * 4 == ModulusValueSpec() + 1;
  }

  // Proves the addition chain exponent decomposition equals SqrtExponent().
  lemma SqrtExponentDecompositionLemma(
    ladder_exp: int, shifted_exp: int, lower_val: int
  )
    requires ladder_exp == 340282366920938463463374607431768211455
    requires shifted_exp == ladder_exp * MathHelpers.pow2(125)
    requires lower_val == LimbsValueSpec([
      LimbFromInt(0xfe6142da37c477d5),
      LimbFromInt(0x1dcd5207465a7cc5),
      ZeroLimb(),
      ZeroLimb()
    ])
    ensures shifted_exp + lower_val == SqrtExponent()
  {
    SqrtExponentValueLemma();
    MathHelpers.Pow2To125Lemma();
  }

  // Verified: the field modulus is ≡ 3 (mod 4).
  lemma ModulusCongruence3Mod4Lemma()
    ensures ModulusValueSpec() % 4 == 3
  {
    assert ModulusValueSpec() % 4 == 3;
  }

  // Euler criterion for p ≡ 3 (mod 4).
  lemma EulerCriterionLemma(
    a_val: int, p: int, r: int)
    requires p == ModulusValueSpec()
    requires 0 <= a_val < p
    requires 0 <= r < p
    requires r == pow_mod(a_val, SqrtExponent(), p)
    requires (r * r) % p != a_val
    ensures forall x: int :: 0 <= x < p ==>
      (x * x) % p != a_val
  {
    forall x: int | 0 <= x < p
      ensures (x * x) % p != a_val
    {
      if (x * x) % p == a_val {
        EulerCriterionContradictionLemma(
          x, a_val, p, r);
      }
    }
  }

  // Helper: if x^2 ≡ a (mod p) then a^((p+1)/4)^2 ≡ a.
  lemma {:isolate_assertions} EulerCriterionContradictionLemma(
      x: int, a_val: int, p: int, r: int
    )
    requires p == ModulusValueSpec()
    requires 0 <= x < p
    requires 0 <= a_val < p
    requires (x * x) % p == a_val
    requires 0 <= r < p
    requires r == pow_mod(a_val, SqrtExponent(), p)
    ensures (r * r) % p == a_val
  {
    SqrtExponentValueLemma();
    var e := SqrtExponent();
    assert e == (p + 1) / 4;
    ModulusIsPrimeLemma();
    if x == 0 {
      assert a_val == 0;
      PowModBoundLemma(0, e, p);
    } else {
      FermatLittleCorollary(x, p);
      assert Power.Pow(x, p - 1) % p == 1;

      PowModBoundLemma(a_val, e, p);
      PowModMulExpLemma(a_val, e, 2, p);
      assert pow_mod(r, 2, p)
        == pow_mod(a_val, e * 2, p);
      assert e * 2 == (p + 1) / 2;

      PowModEqPowLemma(a_val, (p + 1) / 2, p);
      Power.LemmaPowModNoop(
        x * x, (p + 1) / 2, p);
      Power.LemmaPowMultiplies(
        x, 2, (p + 1) / 2);
      assert 2 * ((p + 1) / 2) == p + 1;
      Power.LemmaPowAdds(x, 2, p - 1);
      assert 2 + (p - 1) == p + 1;
      Power.LemmaSquareIsPow2(x);
      assert Power.Pow(x, 2) == x * x;
      DivMod.LemmaMulModNoopRight(
        x * x, Power.Pow(x, p - 1), p);

      PowModEqPowLemma(r, 2, p);
      Power.LemmaSquareIsPow2(r);
      assert Power.Pow(r, 2) == r * r;
    }
  }
}
