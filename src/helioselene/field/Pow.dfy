include "Arith.dfy"
include "../../helpers/u8.dfy"

module FieldPow {
  import opened FieldBase
  import opened FieldArith
  import opened CryptoBigint_0_5_5_Limb
  import opened CryptoBigint_0_5_5_U256
  import opened Limbs
  import opened PowMod
  import opened BitOps
  import opened u8
  import DivMod = Std.Arithmetic.DivMod
  import Mul = Std.Arithmetic.Mul

  // Ported from https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs#L384-L427
  // pow: 4-bit windowed exponentiation. 1-1 syntactic port of Rust code.
  // NOTE: Table lookup uses branching equivalent of Rust's constant-time conditional_select loop.
  // The CT aspect is a timing concern, not functional correctness.
  method {:isolate_assertions}
    {:rlimit 200000}
    {:fuel pow_mod, 0} {:fuel TopBits, 0}
    {:fuel LimbsValueSpec, 0}
    pow(self: HelioseleneField, exp: HelioseleneField)
    returns (result: HelioseleneField)
    requires ValidField(self)
    requires ValidField(exp)
    ensures ValidField(result)
    ensures result.inner.ValueSpec()
      == pow_mod(self.inner.ValueSpec(),
        exp.inner.ValueSpec(), ModulusValueSpec())
  {
    // GHOST CODE
    ghost var a_val := self.inner.ValueSpec();
    ghost var exp_val := exp.inner.ValueSpec();
    ghost var p := ModulusValueSpec();
    ghost var ghost_exp: int := 0;

    // Original code::
    // let mut table = [Self::ONE; 16];
    // table[1] = *self;
    // table[2] = self.square();
    // table[3] = table[2] * self;
    // table[4] = table[2].square();
    // table[5] = table[4] * self;
    // table[6] = table[3].square();
    // table[7] = table[6] * self;
    // table[8] = table[4].square();
    // table[9] = table[8] * self;
    // table[10] = table[5].square();
    // table[11] = table[10] * self;
    // table[12] = table[6].square();
    // table[13] = table[12] * self;
    // table[14] = table[7].square();
    // table[15] = table[14] * self;
    var table := build_pow_table(self);

    // Original code::
    // let mut res = Self::ONE;
    var res := table[0];

    // Original code::
    // let mut bits = 0;
    var bits: u8 := 0;

    // GHOST CODE: snapshot table as value-type seq
    ghost var table_snapshot := table[..];

    // LEMMAS
    PowModZeroLemma(a_val, p);
    // exp_val < 2^256, needed by TopBitsZeroLemma
    Pow256EqWordModulus4Lemma();
    TwoModulusLt2Pow256Lemma();
    assert exp_val < ModulusValueSpec();
    assert ModulusValueSpec() < WORD_MODULUS4 / 2;
    assert WORD_MODULUS4 / 2 < WORD_MODULUS4;
    assert exp_val < WORD_MODULUS4;
    assert exp_val < MathHelpers.pow2(256);
    TopBitsZeroLemma(exp_val);

    // Original code::
    // for (i, mut bit) in exp.to_le_bits().iter_mut().rev().enumerate() {
    // Extract exponent limbs for bit access
    var exp_limbs := exp.inner.as_limbs();
    for i := 0 to 256
      modifies {}
      invariant ValidField(res)
      invariant 0 <= ghost_exp
      invariant res.inner.ValueSpec()
        == pow_mod(a_val, ghost_exp, p)
      invariant 0 <= bits
      // Case-split bits bound (avoids symbolic pow2)
      invariant i % 4 == 0 ==> bits == 0
      invariant i % 4 == 1 ==> bits < 2
      invariant i % 4 == 2 ==> bits < 4
      invariant i % 4 == 3 ==> bits < 8
      // Case-split combined invariant (avoids symbolic pow2)
      invariant i % 4 == 0
        ==> ghost_exp + bits as int == TopBits(exp_val, i)
      invariant i % 4 == 1
        ==> ghost_exp * 2 + bits as int == TopBits(exp_val, i)
      invariant i % 4 == 2
        ==> ghost_exp * 4 + bits as int == TopBits(exp_val, i)
      invariant i % 4 == 3
        ==> ghost_exp * 8 + bits as int == TopBits(exp_val, i)
      invariant table[..] == table_snapshot
      invariant exp_limbs.Length == 4
      invariant LimbsValueSpec(exp_limbs[..]) == exp_val
    {
      // NOTE: We modified the code to manually extract the bit instead of using to_le_bits, this
      //       is noted on the README and could be improved
      var bit_idx := 255 - i;
      var limb_idx := bit_idx / 64;
      var bit_offset := bit_idx % 64;
      MathHelpers.Pow2PositiveLemma(bit_offset);
      var bit: int := (exp_limbs[limb_idx].word
        as int / MathHelpers.pow2(bit_offset)) % 2;

      // Original code::
      //   bits <<= 1;
      //   let mut bit = crate::u8_from_bool(bit.deref_mut());
      //   bits |= bit;
      bits := u8Shl(bits, 1);
      bits := u8Or(bits, bit as u8);

      // LEMMAS: TopBits step + bit extraction
      ghost var ghost_bit := bit;
      BitExtractLemma(exp_limbs[..], bit_idx);
      assert ghost_bit == (exp_val / MathHelpers.pow2(255 - i)) % 2;
      TopBitsStepLemma(exp_val, i);

      //   bit.zeroize();
      bit := 0;

      // Original code::
      //   if ((i + 1) % 4) == 0 {
      if (i + 1) % 4 == 0 {

        // Original code::
        //     if i != 3 {
        //       for _ in 0 .. 4 {
        //         res = res.square();
        //       }
        //     }
        if i != 3 {
          // GHOST CODE
          ghost var window_val := bits;
          assert TopBits(exp_val, i + 1) == ghost_exp * 16 + window_val as int;
          assert 0 <= window_val < 16;

          // Original code:
          //       for _ in 0 .. 4 {
          //         res = res.square();
          //       }
          for iter := 0 to 4
            modifies {}
            invariant ValidField(res)
            invariant res.inner.ValueSpec() < p
            invariant 0 <= ghost_exp
            invariant res.inner.ValueSpec()
              == pow_mod(a_val, ghost_exp, p)
            invariant ghost_exp * MathHelpers.pow2(4 - iter) + bits as int == TopBits(exp_val, i + 1)
          {
            // GHOST CODE
            PowModAddLemma(a_val, ghost_exp, ghost_exp, p);
            ghost_exp := ghost_exp * 2;

            // Original code:
            //         res = res.square();
            res := field_square(res);
          }
        } else {
          // GHOST CODE
          // First window: ghost_exp == 0, no squaring needed
          assert ghost_exp == 0;
          ghost var window_val := bits;
          assert window_val as int == TopBits(exp_val, i + 1);
        }

        // Original code::
        //     let mut factor = table[0];
        //     for (j, candidate) in table[1 ..].iter().enumerate() {
        //       let j = j + 1;
        //       factor = Self::conditional_select(
        //         &factor, candidate,
        //         usize::from(bits).ct_eq(&j));
        //     }
        var factor := table[0];
        for j := 0 as u8 to (table.Length - 1) as u8
          modifies {}
          invariant 0 <= j <= 15
          invariant 0 <= bits < 16
          invariant factor.inner.Valid()
          invariant factor.inner.ValueSpec()
            < ModulusValueSpec()
          invariant bits < j + 1 ==>
            factor.inner.ValueSpec()
              == pow_mod(a_val, bits as int, p)
          invariant bits >= j + 1 ==>
            factor.inner.ValueSpec()
              == pow_mod(a_val, 0, p)
          invariant table[..] == table_snapshot
        {
          // Original code:
          // let j = j + 1;
          var innerJ := j + 1;

          // NOTE: Rust uses an enumerate(), we must explicitly index
          var candidate := table[innerJ];

          // Original code::
          //   factor = Self::conditional_select(
          //     &factor, candidate,
          //     usize::from(bits).ct_eq(&j));
          if bits == innerJ {
            factor := table[innerJ];
          }
        }

        // LEMMAS
        PowModAddLemma(a_val, ghost_exp, bits as int, p);

        // Original code::
        //     res *= factor;
        res := field_mul(res, factor);

        // GHOST CODE
        ghost_exp := ghost_exp + bits as int;

        // Original code::
        //     bits = 0;
        bits := 0;

      //   } // end if ((i + 1) % 4) == 0
      }

      // Help z3 with non-window case algebra
      if (i + 1) % 4 != 0 {
        assert TopBits(exp_val, i + 1)
          == TopBits(exp_val, i) * 2 + ghost_bit;
        if i % 4 == 0 {
          assert ghost_exp * 2 + bits as int
            == TopBits(exp_val, i + 1);
        } else if i % 4 == 1 {
          assert ghost_exp * 4 + bits as int
            == TopBits(exp_val, i + 1);
        } else if i % 4 == 2 {
          assert ghost_exp * 8 + bits as int
            == TopBits(exp_val, i + 1);
        }
      }

    // } // end for
    }

    // LEMMAS: ghost_exp + 0 == TopBits(exp_val, 256) == exp_val
    TopBits256Lemma(exp_val);

    // Original code:
    // res
    result := res;
  }

  // Build the 16-entry power table: table[k] == a^k mod p for k in 0..15
  method {:isolate_assertions} {:rlimit 140000} build_pow_table(self: HelioseleneField) returns (table: array<HelioseleneField>)
    requires ValidField(self)
    ensures table.Length == 16
    ensures forall k | 0 <= k < 16 ::
      table[k].inner.Valid() &&
      table[k].inner.ValueSpec() < ModulusValueSpec() &&
      table[k].inner.ValueSpec() == pow_mod(self.inner.ValueSpec(), k, ModulusValueSpec())
    ensures fresh(table)
  {
    // GHOST CODE
    ghost var self_val := self.inner.ValueSpec();
    ghost var p := ModulusValueSpec();
    PowModOneLemma(self_val, p);

    // Original code::
    //  let mut table = [Self::ONE; 16];
    var one_field := HelioseleneField_ONE();
    table := new HelioseleneField[16](_ => one_field);

    // Original code::
    // table[1] = *self;
    table[1] := self;

    // GHOST CODE
    assert TablePredicate(table[..2]) by {
      assert ValidField(table[0]);
      assert ValidField(table[1]);
      assert pow_mod(self_val, 0, p) == 1;
      assert table[0].inner.ValueSpec() == pow_mod(self_val, 0, p);
      assert pow_mod(self_val, 1, p) == self_val by {
        PowModOneLemma(self_val, p);
      }
      assert table[1].inner.ValueSpec() == pow_mod(self_val, 1, p);
    }

    // Original code::
    // table[2] = self.square();
    table[2] := field_square(self);
    // GHOST CODE
    assert TablePredicate(table[..3]) by {
      TableEvenUpdateLemma(table[..3]);
    }

    // Original code::
    // table[3] = table[2] * self;
    table[3] := field_mul(table[2], self);
    // GHOST CODE
    assert TablePredicate(table[..4]) by {
      TableOddUpdateLemma(table[..3], table[3]);
    }

    // Original code::
    // table[4] = table[2].square();
    table[4] := field_square(table[2]);
      // GHOST CODE
    assert TablePredicate(table[..5]) by {
      TableEvenUpdateLemma(table[..5]);
    }

    // Original code::
    // table[5] = table[4] * self;
    table[5] := field_mul(table[4], self);
    // GHOST CODE
    assert TablePredicate(table[..6]) by {
      TableOddUpdateLemma(table[..5], table[5]);
    }

    // Original code::
    // table[6] = table[3].square();
    table[6] := field_square(table[3]);
    // GHOST CODE
    ghost var tab7 := table[..7];
    assert TablePredicate(tab7) by {
      TableEvenUpdateLemma(tab7);
    }

    // Original code::
    // table[7] = table[6] * self;
    table[7] := field_mul(table[6], self);
    // GHOST CODE
    assert TablePredicate(table[..8]) by {
      TableOddUpdateLemma(table[..7], table[7]);
    }

    // Original code::
    // table[8] = table[4].square();
    table[8] := field_square(table[4]);
    // GHOST CODE
    assert TablePredicate(table[..9]) by {
      TableEvenUpdateLemma(table[..9]);
    }

    // Original code::
    // table[9] = table[8] * self;
    table[9] := field_mul(table[8], self);
    // GHOST CODE
    assert TablePredicate(table[..10]) by {
      TableOddUpdateLemma(table[..9], table[9]);
    }

    // Original code::
    // table[10] = table[5].square();
    table[10] := field_square(table[5]);
    // GHOST CODE
    assert TablePredicate(table[..11]) by {
      TableEvenUpdateLemma(table[..11]);
    }

    // Original code::
    // table[11] = table[10] * self;
    table[11] := field_mul(table[10], self);
    // GHOST CODE
    assert TablePredicate(table[..12]) by {
      TableOddUpdateLemma(table[..11], table[11]);
    }

    // Original code::
    // table[12] = table[6].square();
    table[12] := field_square(table[6]) by {
      TablePredicateAtIndex(table[..12], 6);
    }
    // GHOST CODE
    assert TablePredicate(table[..13]) by {
      TableEvenUpdateLemma(table[..13]);
    }

    // Original code::
    // table[13] = table[12] * self;
    table[13] := field_mul(table[12], self) by {
      TablePredicateAtIndex(table[..13], 12);
    }
    // GHOST CODE
    assert TablePredicate(table[..14]) by {
      TableOddUpdateLemma(table[..13], table[13]) by {
        assert 1 < |table[..13]| <= 16;
        assert TablePredicate(table[..13]);
        assert ValidField(table[13]);
        var prev:= table[..13][|table[..13]| - 1].inner.ValueSpec();
        var base := table[..13][1].inner.ValueSpec();
        assert table[13].inner.ValueSpec() == (prev * base) % ModulusValueSpec();
      }
      assert table[..14] == table[..13] + [table[13]];
    }

    // Original code::
    // table[14] = table[7].square();
    table[14] := field_square(table[7]) by {
      TablePredicateAtIndex(table[..14], 7);
    }
    // GHOST CODE
    assert TablePredicate(table[..15]) by {
      TableEvenUpdateLemma(table[..15]) by {
        var newField := table[..15][|table[..15]| - 1];
        var sqrtIndex := (|table[..15]| - 1) / 2;
        var sqrt := table[..15][sqrtIndex].inner.ValueSpec();
        assert newField.inner.ValueSpec() == (sqrt * sqrt) % ModulusValueSpec();
        assert |table[..15]| == 15;
        assert TablePredicate(table[..15][..|table[..15]| - 1]);
        assert ValidField(table[..15][|table[..15]| - 1]);
      }
    }

    // Original code::
    // table[15] = table[14] * self;
    table[15] := field_mul(table[14], self);
    // GHOST CODE
    assert TABLE_PREDICATE_16: TablePredicate(table[..16]) by {
      TableOddUpdateLemma(table[..15], table[15]);
    }

    assert forall k | 0 <= k < 16 ::
      table[k].inner.Valid() &&
      table[k].inner.ValueSpec() < ModulusValueSpec() &&
      table[k].inner.ValueSpec() == pow_mod(self.inner.ValueSpec(), k, ModulusValueSpec()) by {
      TablePostconditionLemma(table, self) by {
        assert table.Length == 16;
        assert TablePredicate(table[..]) by {
          assert |table[..]| == 16;
          reveal TABLE_PREDICATE_16;
          assert table[..] == table[..16];
        }
        assert self.inner.ValueSpec() == table[1].inner.ValueSpec() by {
          assert pow_mod(self.inner.ValueSpec(), 1, ModulusValueSpec()) == self.inner.ValueSpec() by {
            assert pow_mod(self.inner.ValueSpec(), 1, ModulusValueSpec()) == self.inner.ValueSpec() % ModulusValueSpec() by {
              PowModOneLemma(self.inner.ValueSpec(), ModulusValueSpec());
            }
            assert self.inner.ValueSpec() == self.inner.ValueSpec() % ModulusValueSpec() by {
              DivMod.LemmaSmallMod(self.inner.ValueSpec(), ModulusValueSpec());
            }
          }
          assert table[1].inner.ValueSpec() == pow_mod(self.inner.ValueSpec(), 1, ModulusValueSpec()) by {
            TablePredicateAtIndex(table[..], 1);
          }
        }
      }
    }
  }

  // ===================================================================
  // SUPPORTING LEMMAS
  // ===================================================================

  ghost predicate TablePredicate(table: seq<HelioseleneField>)
    requires 1 < |table|
    reads set i | 0 <= i < |table| :: table[i].inner
    reads set i | 0 <= i < |table| :: table[i].inner.limbs
  {
    if TablePredicateValid(table)
      then TablePredicateCorrect(table)
      else false
  }

  ghost predicate {:fuel 2} {:inline} TablePredicateValid(table: seq<HelioseleneField>)
    reads set i | 0 <= i < |table| :: table[i].inner
    reads set i | 0 <= i < |table| :: table[i].inner.limbs
  {
    forall k {:trigger table[k]} {:trigger ValidField(table[k])} | 0 <= k < |table| :: ValidField(table[k])
  }

  ghost predicate {:fuel 1} {:fuel ValidField,2} {:inline} TablePredicateCorrect(table: seq<HelioseleneField>)
    requires 1 < |table|
    requires forall k | 0 <= k < |table| :: ValidField(table[k])
    reads set i | 0 <= i < |table| :: table[i].inner
    reads set i | 0 <= i < |table| :: table[i].inner.limbs
  {
    assert ValidField(table[1]) by {
      assert forall k | 0 <= k < |table| :: ValidField(table[k]);
      assert 0 <= 1 < |table|;
      assert ValidField(table[1]);
    }
    forall k | 0 <= k < |table| ::
      assert ValidField(table[k]) by {
        assert 0 <= k < |table|;
        assert ValidField(table[k]);
      }
      table[k].inner.ValueSpec() == pow_mod(table[1].inner.ValueSpec(), k, ModulusValueSpec())
  }

  lemma {:rlimit 10000} {:isolate_assertions} TableEvenUpdateLemma(table: seq<HelioseleneField>)
    requires |table| == 3 || |table| == 5 || |table| == 7 || |table| == 9 || |table| == 11 || |table| == 13 || |table| == 15
    requires TablePredicate(table[..|table| - 1])
    requires ValidField(table[|table| - 1])
    requires
      var newField := table[|table| - 1];
      var sqrtIndex := (|table| - 1) / 2;
      assert ValidField(table[sqrtIndex]) by {
        TablePredicateAtIndex(table[..|table| - 1], sqrtIndex);
      }
      var sqrt := table[sqrtIndex].inner.ValueSpec();
      newField.inner.ValueSpec() == (sqrt * sqrt) % ModulusValueSpec()
    ensures TablePredicate(table)
  {
    var head := table[..|table| - 1];
    var newField := table[|table| - 1];
    assert TablePredicateValid(table) by {
      assert TablePredicateValid(head);
      assert ValidField(newField);
    }
    assert TablePredicateCorrect(table) by {
      assert TablePredicateCorrect(head);
      assert newField.inner.ValueSpec() == pow_mod(table[1].inner.ValueSpec(), |table| - 1, ModulusValueSpec()) by {
        var sqrtIndex := (|table| - 1) / 2;
        var sqrt := table[sqrtIndex].inner.ValueSpec();
        var base := table[1].inner.ValueSpec();
        var newFieldValue := newField.inner.ValueSpec();
        var p := ModulusValueSpec();
        assert newFieldValue == (sqrt * sqrt) % p;
        assert sqrt == pow_mod(base, sqrtIndex, p);
        assert pow_mod(base, sqrtIndex + sqrtIndex, p) == (pow_mod(base, sqrtIndex, p) * pow_mod(base, sqrtIndex, p)) % p by {
          PowModAddLemma(base, |table| - 1, 1, p);
        }
        assert pow_mod(base, |table| - 1, p) == pow_mod(base, sqrtIndex + sqrtIndex, p) by {
          assert |table| - 1 == sqrtIndex + sqrtIndex;
        }
        assert pow_mod(base, |table| - 1, p) == (sqrt * sqrt) % p;
        assert newFieldValue == pow_mod(base, |table| - 1, p);
      }
    }
  }

  lemma TableOddUpdateLemma(table: seq<HelioseleneField>, newField: HelioseleneField)
    requires 1 < |table| <= 16
    requires TablePredicate(table)
    requires ValidField(newField)
    requires
      assert ValidField(table[|table| - 1]) by { TablePredicateAtIndex(table, |table| - 1); }
      var prev:= table[|table| - 1].inner.ValueSpec();
      assert ValidField(table[1]) by { TablePredicateAtIndex(table, 1); }
      var base := table[1].inner.ValueSpec();
      newField.inner.ValueSpec() == (prev * base) % ModulusValueSpec()
    ensures TablePredicate(table + [newField])
  {
    var newTable := table + [newField];
    assert TablePredicateValid(newTable) by {
      assert TablePredicateValid(table);
      assert ValidField(newField);
    }
    assert TablePredicateCorrect(newTable) by {
      assert TablePredicateCorrect(table);
      assert newField.inner.ValueSpec() == pow_mod(table[1].inner.ValueSpec(), |table|, ModulusValueSpec()) by {
        var prev := table[|table| - 1].inner.ValueSpec();
        var base := table[1].inner.ValueSpec();
        var newFieldValue := newField.inner.ValueSpec();
        var p := ModulusValueSpec();
        assert newFieldValue == (prev * base) % p;
        assert prev == pow_mod(base, |table| - 1, p);
        assert pow_mod(base, (|table| - 1) + 1, p) == (pow_mod(base, |table| - 1, p) * pow_mod(base, 1, p)) % p by {
          PowModAddLemma(base, |table| - 1, 1, p);
        }
        assert base == pow_mod(base, 1, p);
        assert pow_mod(base, (|table| - 1) + 1, p) == (prev * base) % p;
        assert newFieldValue == pow_mod(base, |table|, p);
      }
    }
  }

  lemma {:fuel ValidField,2} TablePredicateAtIndex(table: seq<HelioseleneField>, index: nat)
    requires 1 < |table| <= 16
    requires index < |table|
    requires TablePredicate(table)
    ensures ValidField(table[index])
    ensures
      assert ValidField(table[1]) by {
        assert TablePredicate(table);
        assert TablePredicateValid(table);
        assert ValidField(table[1]);
      }
      table[index].inner.ValueSpec() == pow_mod(table[1].inner.ValueSpec(), index, ModulusValueSpec())
  {
    assert TablePredicateValid(table);
    assert TablePredicateCorrect(table);
    assert 0 <= index < |table|;
    assert table[index].inner.ValueSpec() == pow_mod(table[1].inner.ValueSpec(), index, ModulusValueSpec());
  }

  lemma TablePostconditionLemma(table: array<HelioseleneField>, self: HelioseleneField)
    requires table.Length == 16
    requires TablePredicate(table[..])
    requires ValidField(self)
    requires self.inner.ValueSpec() == table[1].inner.ValueSpec()
    ensures forall k | 0 <= k < 16 ::
      table[k].inner.Valid() &&
      table[k].inner.ValueSpec() < ModulusValueSpec() &&
      table[k].inner.ValueSpec() == pow_mod(self.inner.ValueSpec(), k, ModulusValueSpec())
  {
    assert TablePredicateValid(table[..]);
    assert TablePredicateCorrect(table[..]);
  }

  // pow2(a + b) == pow2(a) * pow2(b)
  lemma Pow2SplitLemma(a: nat, b: nat)
    ensures MathHelpers.pow2(a + b) == MathHelpers.pow2(a) * MathHelpers.pow2(b)
    decreases b
  {
    if b == 0 {
      assert MathHelpers.pow2(0) == 1;
    } else {
      Pow2SplitLemma(a, b - 1);
      var pa := MathHelpers.pow2(a);
      var pb1 := MathHelpers.pow2(b - 1);
      assert MathHelpers.pow2(a + b - 1) == pa * pb1;
      MathHelpers.Pow2DoubleLemma(a + b - 1);
      assert MathHelpers.pow2(a + b) == 2 * (pa * pb1);
      MathHelpers.Pow2DoubleLemma(b - 1);
      assert MathHelpers.pow2(b) == 2 * pb1;
      // Need: pa * (2 * pb1) == 2 * (pa * pb1)
      // i.e. pa * (2 * pb1) == 2 * pa * pb1
      Mul.LemmaMulIsAssociative(pa, 2, pb1);
      assert pa * (2 * pb1) == (pa * 2) * pb1;
      Mul.LemmaMulIsCommutative(pa, 2);
      assert (pa * 2) * pb1 == (2 * pa) * pb1;
      Mul.LemmaMulIsAssociative(2, pa, pb1);
      assert (2 * pa) * pb1 == 2 * (pa * pb1);
    }
  }

  // Bit extraction from (x + pow2(n) * y): upper part vanishes mod 2 when n >= 1.
  // (x + pow2(n) * y) / pow2(offset) % 2 == x / pow2(offset) % 2
  // when 0 <= x < pow2(n) and 0 <= offset < n.
  lemma {:timeLimit 240} BitFromSumLemma(
    x: nat, y: nat, n: nat, offset: nat)
    requires n >= 1
    requires 0 <= x < MathHelpers.pow2(n)
    requires 0 <= offset < n
    requires MathHelpers.pow2(offset) > 0
    ensures ((x + MathHelpers.pow2(n) * y) / MathHelpers.pow2(offset)) % 2
         == (x / MathHelpers.pow2(offset)) % 2
  {
    MathHelpers.Pow2PositiveLemma(offset);
    MathHelpers.Pow2PositiveLemma(n);
    MathHelpers.Pow2PositiveLemma(n - offset);
    Pow2SplitLemma(offset, n - offset);
    var p := MathHelpers.pow2(offset);
    var q := MathHelpers.pow2(n - offset);

    // pow2(n) == p * q, and (p*q)*y == p*(q*y) by associativity
    Mul.LemmaMulIsAssociative(p, q, y);

    // Decompose x = p * xd + xr
    DivMod.LemmaFundamentalDivMod(x, p);
    var xd := x / p;
    var xr := x % p;

    // p*xd + p*(q*y) == p*(xd + q*y) by distributivity
    Mul.LemmaMulIsDistributive(p, xd, q * y);

    // (x + p*(q*y)) / p == xd + q*y
    assert x + p * (q * y) == p * (xd + q * y) + xr;
    DivMod.LemmaFundamentalDivModConverse(
      x + p * (q * y), p, xd + q * y, xr);

    // q*y is even: q = 2*k (since n-offset >= 1)
    MathHelpers.Pow2DoubleLemma(n - offset - 1);
    var k := MathHelpers.pow2(n - offset - 1);
    Mul.LemmaMulIsAssociative(2, k, y);
    assert q * y == 2 * (k * y);

    // (xd + 2*(k*y)) % 2 == xd % 2
    ModAddMultipleLemma(xd, k * y, 2);
  }

  // Bit extraction from limbs matches bit extraction from value.
  // For U256 val = sum_{k=0}^{3} L_k * W^k (W = 2^64),
  // the bit at position pos in val equals the bit at position (pos % 64) in L_{pos/64}.
  lemma {:timeLimit 120} BitExtractLemma(limbs: seq<Limb>, pos: nat)
    requires |limbs| == 4
    requires 0 <= pos < 256
    requires forall j :: 0 <= j < 4 ==> 0 <= LimbToInt(limbs[j]) < WORD_MODULUS
    ensures (LimbsValueSpec(limbs) / MathHelpers.pow2(pos)) % 2
         == (LimbToInt(limbs[pos / 64]) / MathHelpers.pow2(pos % 64)) % 2
  {
    var L0 := LimbToInt(limbs[0]);
    var L1 := LimbToInt(limbs[1]);
    var L2 := LimbToInt(limbs[2]);
    var L3 := LimbToInt(limbs[3]);
    var W := WORD_MODULUS;
    MathHelpers.Pow2To64Lemma();
    assert W == MathHelpers.pow2(64);
    var val := LimbsValueSpec(limbs);
    assert val == L0 + L1 * W + L2 * W * W + L3 * W * W * W;

    var k := pos / 64;
    var offset := pos % 64;
    MathHelpers.Pow2PositiveLemma(offset);
    MathHelpers.Pow2PositiveLemma(pos);

    // pow2(pos) == pow2(64 * k + offset) == pow2(64 * k) * pow2(offset)
    assert pos == 64 * k + offset;
    Pow2SplitLemma(64 * k, offset);
    MathHelpers.Pow2PositiveLemma(64 * k);

    var pow2_64k := MathHelpers.pow2(64 * k);
    var pow2_offset := MathHelpers.pow2(offset);

    // Use LemmaDivDenominator: val / pow2(pos) == (val / pow2(64*k)) / pow2(offset)
    DivMod.LemmaDivDenominator(val, pow2_64k, pow2_offset);
    assert val / MathHelpers.pow2(pos) == (val / pow2_64k) / pow2_offset;

    // Now show: (val / pow2(64*k)) % 2^64 == L_k, and the bit extraction
    // from (val / pow2(64*k)) at offset equals extraction from L_k at offset.
    // Strategy: val = lower + pow2(64*k) * (L_k + upper * W)
    // where lower < pow2(64*k), so val / pow2(64*k) == L_k + upper * W
    // Then BitFromSumLemma gives the result.

    if k == 0 {
      // val / pow2(0) == val, L_k = L0
      assert MathHelpers.pow2(0) == 1;
      assert val / 1 == val;
      // val = L0 + W * (L1 + L2 * W + L3 * W * W)
      var upper := L1 + L2 * W + L3 * W * W;
      assert val == L0 + W * upper;
      assert 0 <= L0 < W;
      assert W == MathHelpers.pow2(64);
      BitFromSumLemma(L0, upper, 64, offset);
    } else if k == 1 {
      // val / pow2(64) == val / W
      assert MathHelpers.pow2(64) == W;
      assert MathHelpers.pow2(64 * 1) == W;
      // val = L0 + W * (L1 + L2 * W + L3 * W * W)
      // val / W == L1 + L2 * W + L3 * W * W  (since 0 <= L0 < W)
      var rest := L1 + L2 * W + L3 * W * W;
      assert val == L0 + W * rest;
      DivMod.LemmaFundamentalDivModConverse(val, W, rest, L0);
      assert val / W == rest;
      // rest = L1 + W * (L2 + L3 * W)
      var upper := L2 + L3 * W;
      assert rest == L1 + W * upper;
      assert 0 <= L1 < W;
      assert W == MathHelpers.pow2(64);
      BitFromSumLemma(L1, upper, 64, offset);
    } else if k == 2 {
      Pow2SplitLemma(64, 64);
      assert MathHelpers.pow2(128) == W * W;
      assert MathHelpers.pow2(64 * 2) == W * W;
      // val = (L0 + L1 * W) + W * W * (L2 + L3 * W)
      var lower := L0 + L1 * W;
      var rest := L2 + L3 * W;
      assert val == lower + W * W * rest;
      assert 0 <= lower;
      assert lower < W * W by {
        assert L0 < W;
        assert L1 < W;
        assert lower == L0 + L1 * W;
        assert L0 + L1 * W < W + (W - 1) * W;
        assert W + (W - 1) * W == W * W;
      }
      DivMod.LemmaFundamentalDivModConverse(val, W * W, rest, lower);
      assert val / (W * W) == rest;
      // rest = L2 + W * L3
      var upper := L3;
      assert rest == L2 + W * upper;
      assert 0 <= L2 < W;
      assert W == MathHelpers.pow2(64);
      BitFromSumLemma(L2, upper, 64, offset);
    } else {
      assert k == 3;
      Pow2SplitLemma(64, 64);
      Pow2SplitLemma(128, 64);
      assert MathHelpers.pow2(192) == W * W * W;
      assert MathHelpers.pow2(64 * 3) == W * W * W;
      // val = (L0 + L1 * W + L2 * W * W) + W * W * W * L3
      var lower := L0 + L1 * W + L2 * W * W;
      assert val == lower + W * W * W * L3;
      assert 0 <= lower;
      assert lower < W * W * W by {
        assert L0 < W;
        assert L1 < W;
        assert L2 < W;
        assert L0 + L1 * W < W + (W - 1) * W == W * W;
        assert L0 + L1 * W + L2 * W * W < W * W + (W - 1) * W * W;
        assert W * W + (W - 1) * W * W == W * W * W;
      }
      DivMod.LemmaFundamentalDivModConverse(val, W * W * W, L3, lower);
      assert val / (W * W * W) == L3;
      // L3 is a single limb; offset < 64, need bit extraction from L3
      // (L3 / pow2(offset)) % 2 == (L3 / pow2(offset)) % 2 — trivially equal
      // But we need: (val / pow2(pos)) % 2 == (L3 / pow2(offset)) % 2
      // We have: val / pow2(pos) == (val / pow2(192)) / pow2(offset) == L3 / pow2(offset)
    }
  }

}
