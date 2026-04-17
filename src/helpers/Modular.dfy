module Modular {
  import DivMod = Std.Arithmetic.DivMod
  import opened Std.BoundedInts

  const TWO_POW_64 := 18446744073709551616

  // ===================================================================
  // TCB AXIOMS — BV/int trust boundary
  // ===================================================================

  // TCB AXIOM: bv64 addition distributes to int.
  lemma {:rlimit 12} {:axiom} BV64ToIntHomomorphicAxiom(a: bv64, b: bv64)
    ensures (a as int + b as int) % TWO_POW_64 == (a + b) as int

  lemma {:rlimit 508781} {:axiom} BV64ToIntConversionMonotonicPlusOneAxiom(a: bv64, b: bv64)
    requires a <= b
    requires !(a == b)
    ensures a <= b - 1

  ////////////
  // LEMMAS //
  ////////////

  lemma {:rlimit 20} ModDecomposeLemma(x: int, p: int) returns (q: int, r: int)
    requires p > 0
    ensures x == p * q + r
    ensures q == x / p
    ensures r == x % p
  {
    q := x / p;
    r := x % p;
    DivMod.LemmaFundamentalDivMod(x, p);
  }

  lemma {:rlimit 29} LessThanModulusMeansIsReducedLemma(a: int, n: int)
    requires 0 <= a < n
    ensures a % n == a
  {
  }

  lemma {:rlimit 87} Red1Lemma(a: int, b: int, n: int)
    requires a == b || a == b - n
    requires 0 <= a < n
    ensures a == b % n
  {
  }

  lemma {:rlimit 37} {:auto_apply} BV64RoundTripLemma(a: int)
    requires 0 <= a < TWO_POW_64
    ensures a == (a as bv64) as int
  {
    assert 0 <= a < TWO_POW_64;
    assert a % TWO_POW_64 == a;
  }

  lemma {:axiom} {:rlimit 508781} SubtractAndAdd(a: bv64, b: bv64, diff: bv64)
    requires diff == (b - a)
    ensures diff + a == b
  {
    assert diff + a == (b - a) + a;
    assert (b - a) + a == b + (-a) + a;
    assert b + (-a) + a == b + (-a + a);
    assert b + (-a + a) == b + 0;
    assert b + 0 == b;
  }

  lemma {:rlimit 8733} {:isolate_assertions} BV64ToIntConversionMonotonicLemma_Helper1(a: bv64, b: bv64)
    requires a <= b
    ensures a as int <= b as int
    decreases b
  {
    if a == b {
      assert a as int == b as int;
    }
    else {
      var aInt := a as int;
      var bMinusOneInt := (b - 1) as int;

      assert aInt <= bMinusOneInt as int by {
        BV64ToIntConversionMonotonicLemma_Helper1(a, b - 1) by {
          assert a <= b - 1 < b by {
            BV64ToIntConversionMonotonicPlusOneAxiom(a, b);
          }
        }
      }
      assert ((b - 1) + 1) as int == (bMinusOneInt + 1 as int) % TWO_POW_64 by {
        BV64ToIntHomomorphicAxiom(b - 1, 1);
      }
      assert (bMinusOneInt + 1) % TWO_POW_64 <= b as int;
      if bMinusOneInt == TWO_POW_64 - 1 {
        assert TWO_POW_64 == TWO_TO_THE_64;
        assert b - 1  == (TWO_TO_THE_64 - 1) as bv64;
        assert b == 0;
        assert b <= a;
        assert a == b;
        assert false;
      }
      else {
        assert 0 <= bMinusOneInt + 1 < TWO_POW_64;
        assert (bMinusOneInt + 1) % TWO_POW_64 == bMinusOneInt + 1 by {
          LessThanModulusMeansIsReducedLemma(bMinusOneInt + 1, TWO_POW_64);
        }
        assert bMinusOneInt + 1 <= b as int;
        assert aInt <= b as int;
      }
    }
  }

  lemma {:rlimit 8} BV64ToIntConversionMonotonicLemma_Helper2(a: bv64, b: bv64)
  ensures !(a <= b) ==> a != b
  {
  }

  lemma {:rlimit 58} BV64ToIntConversionMonotonicLemma_Helper3(a: bv64, b: bv64)
  ensures a != b ==> a as int != b as int
  {
    assert a as int as bv64 == a;
    assert b as int as bv64 == b;
  }

  lemma {:rlimit 9} BV64ToIntConversionMonotonicLemma_Helper4(a: bv64, b: bv64)
  ensures !(a <= b) ==> a as int != b as int
  {
    BV64ToIntConversionMonotonicLemma_Helper2(a, b);
    BV64ToIntConversionMonotonicLemma_Helper3(a, b);
  }

  lemma {:rlimit 455} BV64ToIntConversionMonotonicLemma(a: bv64, b: bv64)
    ensures (a <= b) <==> (a as int <= b as int)
  {
    var lower := if a <= b then a else b;
    var upper := if a <= b then b else a;
    assert lower <= upper;
    BV64ToIntConversionMonotonicLemma_Helper1(lower, upper);
    assert lower as int <= upper as int;
    assert if a <= b then a as int <= b as int else b as int <= a as int;
    assert a <= b ==> (a as int <= b as int);
    assert !(a <= b) ==> b as int <= a as int;
    BV64ToIntConversionMonotonicLemma_Helper4(a, b);
  }

  lemma {:rlimit 81} BV64FromIntConversionMonotonicLemma_Helper0(a: int, b:int, a_64: bv64, b_64: bv64)
    requires 0 <= a < TWO_POW_64
    requires 0 <= b < TWO_POW_64
    requires a_64 == a as bv64
    requires b_64 == b as bv64
    ensures (a as bv64 <= b as bv64) <==> a_64 <= b_64
  {

  }

  lemma {:rlimit 928} BV64FromIntConversionMonotonicLemma(a: int, b:int)
    requires 0 <= a < TWO_POW_64
    requires 0 <= b < TWO_POW_64
    ensures (a <= b) <==> (a as bv64 <= b as bv64)
  {
    var a_64 := a as bv64;
    var b_64 := b as bv64;

    BV64RoundTripLemma(a);
    assert a_64 as int == a;
    BV64RoundTripLemma(b);
    assert b_64 as int == b;
    BV64ToIntConversionMonotonicLemma(a_64, b_64);
    assert
      (a_64 <= b_64)
      <==>
      (a_64 as int <= b_64 as int);
    assert
      (a_64 <= b_64)
      <==>
      (a <= b);
    assert
      (a <= b)
      <==>
      (a_64 <= b_64);
    BV64FromIntConversionMonotonicLemma_Helper0(a, b, a_64, b_64);
    assert
      (a <= b)
      <==>
      (a as bv64 <= b as bv64);
  }

  // ===================================================================
  // MODULAR CONGRUENCE LEMMAS
  // ===================================================================
  // Extracted from Field.dfy for modularity (REORG-006).

  // If x = y (mod p), then x*c = y*c (mod p).
  lemma {:rlimit 162} ModMulCongruenceLemma(
    x: int, y: int, c: int, p: int)
    requires p > 0
    requires x % p == y % p
    ensures (x * c) % p == (y * c) % p
  {
    ghost var qx, r := ModDecomposeLemma(x, p);
    ghost var qy, r_y := ModDecomposeLemma(y, p);
    assert r_y == r;
    // x = qx * p + r, y = qy * p + r
    assert x == p * qx + r;
    assert y == p * qy + r;
    // x * c = qx * c * p + r * c
    assert x * c == qx * c * p + r * c;
    assert y * c == qy * c * p + r * c;
    DivMod.LemmaModMultiplesVanish(qx * c, r * c, p);
    DivMod.LemmaModMultiplesVanish(qy * c, r * c, p);
  }

  // If x = x' and y = y' (mod p), then x-y = x'-y' (mod p).
  lemma {:rlimit 26822} ModSubCongruenceLemma(
    x: int, x': int, y: int, y': int, p: int)
    requires p > 0
    requires x % p == x' % p
    requires y % p == y' % p
    ensures (x - y) % p == (x' - y') % p
  {
    ghost var qx, r := ModDecomposeLemma(x, p);
    ghost var qx', r_x := ModDecomposeLemma(x', p);
    ghost var qy, s := ModDecomposeLemma(y, p);
    ghost var qy', s_y := ModDecomposeLemma(y', p);
    assert r_x == r;
    assert s_y == s;
    assert x == p * qx + r;
    assert x' == p * qx' + r;
    assert y == p * qy + s;
    assert y' == p * qy' + s;
    assert x - y == (qx - qy) * p + (r - s);
    assert x' - y' == (qx' - qy') * p + (r - s);
    DivMod.LemmaModMultiplesVanish(qx - qy, r - s, p);
    DivMod.LemmaModMultiplesVanish(qx' - qy', r - s, p);
  }

  // If 2*a = 2*b (mod p) and p is odd, then a = b (mod p).
  // Uses: 2 * ((p+1)/2) = p+1 = 1 (mod p), so (p+1)/2
  // is the modular inverse of 2.
  lemma {:rlimit 2885} Cancel2ModLemma(a: int, b: int, p: int)
    requires p > 1
    requires p % 2 == 1
    requires (2 * a) % p == (2 * b) % p
    ensures a % p == b % p
  {
    ghost var inv2 := (p + 1) / 2;
    assert 2 * inv2 == p + 1;

    // Multiply the congruence 2a = 2b by inv2
    ModMulCongruenceLemma(2 * a, 2 * b, inv2, p);
    // Now: (2*a*inv2) % p == (2*b*inv2) % p

    // 2*a*inv2 = a*(p+1) = a*p + a = a (mod p)
    assert (2 * a) * inv2 == a * (p + 1);
    assert a * (p + 1) == a * p + a;
    DivMod.LemmaModMultiplesVanish(a, a, p);

    // Same for b
    assert (2 * b) * inv2 == b * (p + 1);
    assert b * (p + 1) == b * p + b;
    DivMod.LemmaModMultiplesVanish(b, b, p);
  }
}
