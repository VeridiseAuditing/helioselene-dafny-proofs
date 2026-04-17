include "Math.dfy"

// General-purpose number theory: BitLength, gcd, and supporting lemmas.
// Extracted from Field.dfy for modularity (REORG-003).

module NumberTheory {
  import MathHelpers
  import DivMod = Std.Arithmetic.DivMod
  import Mul = Std.Arithmetic.Mul

  // BitLength: number of bits needed to represent x.
  // BitLength(0) = 0, BitLength(x) = floor(log2(x)) + 1 for x > 0.
  ghost function {:rlimit 26} BitLength(x: nat): nat
    decreases x
  {
    if x == 0 then 0
    else 1 + BitLength(x / 2)
  }

  // gcd: greatest common divisor (Euclidean algorithm).
  ghost function {:rlimit 32} gcd(a: nat, b: nat): nat
    decreases a + b
  {
    if b == 0 then a
    else if a == 0 then b
    else if a < b then gcd(a, b % a)
    else gcd(b, a % b)
  }

  // BitLength(x / 2) == BitLength(x) - 1 for x > 0.
  lemma {:rlimit 23} BitLengthHalfLemma(x: nat)
    requires x > 0
    ensures BitLength(x / 2) == BitLength(x) - 1
  {
    // Immediate from the definition: BitLength(x) = 1 + BitLength(x / 2)
  }

  // x > 0 implies BitLength(x) >= 1.
  lemma {:rlimit 21} BitLengthPositiveLemma(x: nat)
    requires x > 0
    ensures BitLength(x) >= 1
  {
    // Immediate from the definition
  }

  // x < 2^n implies BitLength(x) <= n.
  lemma {:rlimit 99} BitLengthUpperBoundLemma(x: nat, n: nat)
    requires x < MathHelpers.pow2(n)
    decreases n
    ensures BitLength(x) <= n
  {
    if x == 0 {
    } else if n == 0 {
      MathHelpers.Pow2PositiveLemma(0);
      assert MathHelpers.pow2(0) == 1;
      assert x < 1;
      assert false;  // contradiction: x > 0 but x < 1
    } else {
      // x < pow2(n) implies x / 2 < pow2(n-1)
      MathHelpers.Pow2PositiveLemma(n);
      assert MathHelpers.pow2(n) == 2 * MathHelpers.pow2(n - 1);
      assert x / 2 < MathHelpers.pow2(n - 1);
      BitLengthUpperBoundLemma(x / 2, n - 1);
    }
  }

  // Monotonicity: x <= y implies BitLength(x) <= BitLength(y).
  lemma {:rlimit 84} BitLengthMonotoneLemma(x: nat, y: nat)
    requires x <= y
    decreases y
    ensures BitLength(x) <= BitLength(y)
  {
    if x == 0 {
    } else {
      assert x / 2 <= y / 2;
      BitLengthMonotoneLemma(x / 2, y / 2);
    }
  }

  // Core convergence lemma for even case:
  // a' = a/2, b' = b. BitLength(a') + BitLength(b') < BitLength(a) + BitLength(b).
  lemma {:rlimit 20} BitLengthEvenStepLemma(a: nat, b: nat)
    requires a > 0
    ensures BitLength(a / 2) + BitLength(b)
         == BitLength(a) - 1 + BitLength(b)
  {
    BitLengthHalfLemma(a);
  }

  // Core convergence lemma for odd-lt case:
  // a odd, b odd, 0 < a < b.
  // a' = (b-a)/2, b' = a.
  // BitLength(a') + BitLength(b') <= BitLength(a) + BitLength(b) - 1.
  lemma {:rlimit 769} BitLengthOddLtStepLemma(a: nat, b: nat)
    requires a > 0 && b > 0
    requires a % 2 == 1 && b % 2 == 1
    requires a < b
    ensures BitLength((b - a) / 2) + BitLength(a)
         <= BitLength(a) + BitLength(b) - 1
  {
    // b - a < b since a > 0
    // (b-a)/2 < b/2
    // BitLength((b-a)/2) <= BitLength(b/2) = BitLength(b) - 1
    var diff := b - a;
    assert diff > 0;
    assert diff % 2 == 0;  // both odd, so difference is even
    var half_diff := diff / 2;
    // half_diff = (b - a) / 2 < b / 2
    assert half_diff < b;
    // b / 2 < b since b > 0
    var half_b := b / 2;
    assert half_diff <= half_b;
    BitLengthMonotoneLemma(half_diff, half_b);
    BitLengthHalfLemma(b);
    // BitLength(half_diff) <= BitLength(half_b) == BitLength(b) - 1
  }

  // Core convergence lemma for odd-ge case:
  // a odd, b odd, a >= b > 0.
  // a' = (a-b)/2, b' = b.
  // BitLength(a') + BitLength(b') <= BitLength(a) + BitLength(b) - 1.
  lemma {:rlimit 206} BitLengthOddGeStepLemma(a: nat, b: nat)
    requires a >= b > 0
    requires a % 2 == 1 && b % 2 == 1
    ensures BitLength((a - b) / 2) + BitLength(b)
         <= BitLength(a) + BitLength(b) - 1
  {
    if a == b {
      // a - b == 0, so (a-b)/2 == 0, BitLength(0) = 0
      // BitLength(0) + BitLength(b) = BitLength(b) <= BitLength(a) + BitLength(b) - 1
      // since BitLength(a) >= 1 (a > 0)
      BitLengthPositiveLemma(a);
    } else {
      // a > b, so a - b > 0
      var diff := a - b;
      assert diff > 0;
      assert diff % 2 == 0;
      var half_diff := diff / 2;
      // half_diff = (a-b)/2 <= (a-1)/2 = a/2 (since a is odd, a-1 is even)
      assert half_diff <= (a - 1) / 2;
      assert (a - 1) / 2 == a / 2;  // a is odd
      BitLengthMonotoneLemma(half_diff, a / 2);
      BitLengthHalfLemma(a);
    }
  }

  // When a == 0, the step doesn't change anything
  // (a' = 0/2 = 0, b' = b).
  lemma {:rlimit 17} BitLengthZeroStepLemma(b: nat)
    ensures BitLength(0) == 0
  {
  }

  // GCD is symmetric
  lemma {:rlimit 34} GcdSymmetricLemma(a: nat, b: nat)
    ensures gcd(a, b) == gcd(b, a)
    decreases a + b
  {
    if a == 0 || b == 0 {
    } else if a == b {
      assert a % b == 0;
      assert b % a == 0;
    } else if a < b {
      // gcd(a, b) = gcd(a, b % a)
      // gcd(b, a) = gcd(a, b % a) since b >= a, so gcd(b,a) = gcd(a, b%a)
    } else {
      // a > b
      // gcd(a, b) = gcd(b, a % b)
      // gcd(b, a) = gcd(b, a % b) since a >= b
    }
  }

  // ===================================================================
  // GCD DIVISIBILITY INFRASTRUCTURE
  // ===================================================================

  ghost predicate divides(d: nat, n: nat) {
    exists k: nat :: n == d * k
  }

  // Extract a concrete witness k for d | n.
  lemma {:rlimit 26} DividesWitness(d: nat, n: nat) returns (k: nat)
    requires divides(d, n)
    ensures n == d * k
  {
    var w :| n == d * w;
    k := w;
  }

  lemma {:rlimit 23} DividesSelfLemma(n: nat)
    ensures divides(n, n)
  {
    assert n == n * 1;
  }

  lemma {:rlimit 22} DividesZeroLemma(d: nat)
    ensures divides(d, 0)
  {
    assert 0 == d * 0;
  }

  lemma {:rlimit 23} OneDividesAllLemma(n: nat)
    ensures divides(1, n)
  {
    assert n == 1 * n;
  }

  lemma {:rlimit 38} DividesTransitiveLemma(a: nat, b: nat, c: nat)
    requires divides(a, b) && divides(b, c)
    ensures divides(a, c)
  {
    var kb := DividesWitness(a, b);
    var kc := DividesWitness(b, c);
    Mul.LemmaMulIsAssociative(a, kb, kc);
    assert c == a * (kb * kc);
  }

  lemma {:rlimit 33} DividesModZeroLemma(d: nat, n: nat)
    requires d > 0
    requires divides(d, n)
    ensures n % d == 0
  {
    var k :| n == d * k;
    DivMod.LemmaFundamentalDivModConverse(
      n, d, k, 0
    );
  }

  lemma {:rlimit 34} ModZeroDividesLemma(d: nat, n: nat)
    requires d > 0
    requires n % d == 0
    ensures divides(d, n)
  {
    DivMod.LemmaFundamentalDivMod(n, d);
    assert n == d * (n / d) + 0;
    assert n == d * (n / d);
  }

  lemma {:rlimit 54} DividesSubLemma(d: nat, a: nat, b: nat)
    requires divides(d, a) && divides(d, b)
    requires a >= b
    ensures divides(d, a - b)
  {
    var ka := DividesWitness(d, a);
    var kb := DividesWitness(d, b);
    if d == 0 {
      assert a == 0 && b == 0;
      DividesZeroLemma(0);
    } else {
      // d * ka >= d * kb since a >= b
      // => ka >= kb by cancellation
      Mul.LemmaMulInequalityConverse(kb, ka, d);
      Mul.LemmaMulIsDistributiveSub(d, ka, kb);
      assert a - b == d * (ka - kb);
    }
  }

  lemma {:rlimit 34} DividesAddLemma(d: nat, a: nat, b: nat)
    requires divides(d, a) && divides(d, b)
    ensures divides(d, a + b)
  {
    var ka := DividesWitness(d, a);
    var kb := DividesWitness(d, b);
    Mul.LemmaMulIsDistributiveAdd(d, ka, kb);
    assert a + b == d * (ka + kb);
  }

  lemma {:rlimit 42} DividesMulLemma(d: nat, n: nat, k: nat)
    requires divides(d, n)
    ensures divides(d, n * k)
  {
    var kd := DividesWitness(d, n);
    Mul.LemmaMulIsAssociative(d, kd, k);
    assert n * k == d * (kd * k);
  }

  lemma {:rlimit 69} DividesRemainderLemma(d: nat, a: nat, b: nat)
    requires d > 0 && b > 0
    requires divides(d, a) && divides(d, b)
    ensures divides(d, a % b)
  {
    DivMod.LemmaFundamentalDivMod(a, b);
    var q := a / b;
    assert a == b * q + a % b;
    DividesMulLemma(d, b, q);
    assert divides(d, b * q);
    DividesSubLemma(d, a, b * q);
    assert a - b * q == a % b;
  }

  lemma {:rlimit 32} DividesBoundLemma(d: nat, n: nat)
    requires d > 0 && n > 0
    requires divides(d, n)
    ensures d <= n
  {
    var k := DividesWitness(d, n);
    if k == 0 {
      assert n == 0;
    } else {
      Mul.LemmaMulIncreases(d, k);
    }
  }

  lemma {:rlimit 29} DividesDoubleLemma(d: nat, k: nat)
    requires divides(d, k)
    ensures divides(d, 2 * k)
  {
    DividesMulLemma(d, k, 2);
    Mul.LemmaMulIsCommutative(k, 2);
  }

  // If d is odd and d | 2k, then d | k.
  lemma {:rlimit 250} OddDividesTwiceLemma(d: nat, k: nat)
    requires d > 0 && d % 2 == 1
    requires divides(d, 2 * k)
    ensures divides(d, k)
  {
    if k == 0 {
      DividesZeroLemma(d);
    } else if d == 1 {
      OneDividesAllLemma(k);
    } else {
      // d | 2k means 2k = d * q for some q.
      var q := DividesWitness(d, 2 * k);
      // Since d is odd, q must be even.
      // Proof: d * q = 2k is even. d is odd, so q must be even.
      // If q were odd, d * q would be odd (odd * odd = odd), contradiction.
      if q % 2 == 1 {
        // d odd, q odd => d*q odd. But d*q = 2k is even. Contradiction.
        assert (d * q) % 2 == 1 by {
          Mul.LemmaMulIsCommutative(d, q);
          // odd * odd = odd
          // d = 2a+1, q = 2b+1 => d*q = 4ab + 2a + 2b + 1 = 2(2ab+a+b) + 1
          var a := d / 2;
          var b := q / 2;
          assert d == 2 * a + 1;
          assert q == 2 * b + 1;
          calc {
            d * q;
            (2 * a + 1) * (2 * b + 1);
            4 * a * b + 2 * a + 2 * b + 1;
            2 * (2 * a * b + a + b) + 1;
          }
        }
        assert 2 * k == d * q;
        assert (2 * k) % 2 == 0;
        assert false;
      }
      assert q % 2 == 0;
      var q2 := q / 2;
      assert q == 2 * q2;
      calc {
        2 * k;
        d * q;
        d * (2 * q2);
        { Mul.LemmaMulIsAssociative(d, 2, q2); }
        (d * 2) * q2;
        { Mul.LemmaMulIsCommutative(d, 2); }
        (2 * d) * q2;
        { Mul.LemmaMulIsAssociative(2, d, q2); }
        2 * (d * q2);
      }
      assert k == d * q2;
    }
  }

  // gcd(a, b) divides both a and b.
  lemma {:rlimit 903} GcdDividesBothLemma(a: nat, b: nat)
    ensures divides(gcd(a, b), a)
    ensures divides(gcd(a, b), b)
    decreases a + b
  {
    if b == 0 {
      DividesSelfLemma(a);
      DividesZeroLemma(a);
    } else if a == 0 {
      DividesZeroLemma(b);
      DividesSelfLemma(b);
    } else if a < b {
      GcdDividesBothLemma(a, b % a);
      // gcd(a, b) == gcd(a, b % a)
      // By IH: gcd(a, b%a) | a and gcd(a, b%a) | (b%a)
      var g := gcd(a, b);
      assert divides(g, a);
      assert divides(g, b % a);
      // Need: g | b. Since b = (b/a)*a + b%a, and g | a, g | b%a.
      DivMod.LemmaFundamentalDivMod(b, a);
      DividesMulLemma(g, a, b / a);
      DividesAddLemma(g, a * (b / a), b % a);
      Mul.LemmaMulIsCommutative(a, b / a);
      assert b == (b / a) * a + b % a;
      assert a * (b / a) + b % a == b;
    } else {
      GcdDividesBothLemma(b, a % b);
      var g := gcd(a, b);
      assert divides(g, b);
      assert divides(g, a % b);
      DivMod.LemmaFundamentalDivMod(a, b);
      DividesMulLemma(g, b, a / b);
      DividesAddLemma(g, b * (a / b), a % b);
      Mul.LemmaMulIsCommutative(b, a / b);
      assert a == (a / b) * b + a % b;
      assert b * (a / b) + a % b == a;
    }
  }

  // Any common divisor of a and b divides gcd(a, b).
  lemma {:rlimit 97} GcdIsGreatestLemma(a: nat, b: nat, d: nat)
    requires d > 0
    requires divides(d, a) && divides(d, b)
    ensures divides(d, gcd(a, b))
    decreases a + b
  {
    if b == 0 {
      // gcd(a, 0) = a, and d | a
    } else if a == 0 {
      // gcd(0, b) = b, and d | b
    } else if a < b {
      DividesRemainderLemma(d, b, a);
      GcdIsGreatestLemma(a, b % a, d);
    } else {
      DividesRemainderLemma(d, a, b);
      GcdIsGreatestLemma(b, a % b, d);
    }
  }

  // d | a and d | b and d > 0 ==> d <= gcd(a, b) when a > 0 or b > 0.
  lemma {:rlimit 25} GcdAntisymDividesLemma(g1: nat, g2: nat)
    requires g1 > 0 && g2 > 0
    requires divides(g1, g2) && divides(g2, g1)
    ensures g1 == g2
  {
    DividesBoundLemma(g1, g2);
    DividesBoundLemma(g2, g1);
  }

  // gcd(a, b) = gcd(a, b - a) when 0 < a <= b.
  lemma {:rlimit 504} GcdSubtractLemma(a: nat, b: nat)
    requires 0 < a <= b
    ensures gcd(a, b) == gcd(a, b - a)
    decreases a + b
  {
    var g := gcd(a, b);
    var g' := gcd(a, b - a);
    // g | a, g | b => g | (b - a)
    GcdDividesBothLemma(a, b);
    DividesSubLemma(g, b, a);
    GcdIsGreatestLemma(a, b - a, g);
    // g' | a, g' | (b-a) => g' | b (since b = a + (b-a))
    GcdDividesBothLemma(a, b - a);
    DividesAddLemma(g', a, b - a);
    assert a + (b - a) == b;
    GcdIsGreatestLemma(a, b, g');
    // g | g' and g' | g => g == g'
    if g == 0 {
      // g | a means a == 0, contradiction
      DividesBoundLemma(1, a);
      OneDividesAllLemma(a);
      GcdIsGreatestLemma(a, b, 1);
      DividesBoundLemma(g, 1);
    } else if g' == 0 {
      GcdIsGreatestLemma(a, b - a, 1);
      OneDividesAllLemma(a);
      OneDividesAllLemma(b - a);
      DividesBoundLemma(g', 1);
    } else {
      GcdAntisymDividesLemma(g, g');
    }
  }

  // ===================================================================
  // BINARY GCD IDENTITIES
  // ===================================================================

  // GCD preservation for even case: gcd(a, b) = gcd(a/2, b) when a even, b odd.
  // Proof: any common divisor of (a, b) must be odd (since b is odd),
  // so it also divides a/2. Conversely, any common divisor of (a/2, b)
  // divides a = 2*(a/2). So common divisors are the same set.
  lemma {:rlimit 431} GcdEvenOddLemma(a: nat, b: nat)
    requires a > 0 && a % 2 == 0
    requires b % 2 == 1
    ensures gcd(a, b) == gcd(a / 2, b)
  {
    var k := a / 2;
    assert a == 2 * k;
    var g := gcd(a, b);
    var g' := gcd(k, b);
    // Show g | k and g | b, so g | g'
    GcdDividesBothLemma(a, b);
    assert divides(g, a) && divides(g, b);
    // g | b and b is odd => g is odd
    GcdIsOddIfDivisorIsOddLemma(g, b);
    // g is odd and g | 2k => g | k
    OddDividesTwiceLemma(g, k);
    GcdIsGreatestLemma(k, b, g);
    // Show g' | a and g' | b, so g' | g
    GcdDividesBothLemma(k, b);
    DividesDoubleLemma(g', k);
    assert 2 * k == a;
    GcdIsGreatestLemma(a, b, g');
    // g | g' and g' | g => g == g'
    if g == 0 {
      OneDividesAllLemma(a);
      OneDividesAllLemma(b);
      GcdIsGreatestLemma(a, b, 1);
      DividesBoundLemma(g, 1);
    } else if g' == 0 {
      OneDividesAllLemma(k);
      OneDividesAllLemma(b);
      GcdIsGreatestLemma(k, b, 1);
      DividesBoundLemma(g', 1);
    } else {
      GcdAntisymDividesLemma(g, g');
    }
  }

  // Helper: if d > 0 divides an odd number, d is odd.
  lemma {:rlimit 45} GcdIsOddIfDivisorIsOddLemma(d: nat, n: nat)
    requires n % 2 == 1
    requires divides(d, n)
    ensures d == 0 || d % 2 == 1
  {
    if d == 0 {
    } else if d % 2 == 0 {
      // d is even, d | n means n = d*k, so n is even. Contradiction.
      var k := DividesWitness(d, n);
      var d2 := d / 2;
      assert d == 2 * d2;
      Mul.LemmaMulIsAssociative(2, d2, k);
      assert n == 2 * (d2 * k);
      assert n % 2 == 0;
    }
  }

  // gcd(a, b) = gcd((b-a)/2, a) when both odd, a < b.
  // Proof: gcd(a, b) = gcd(a, b-a) [subtraction]
  //                   = gcd((b-a)/2, a) [even-odd, since b-a even and a odd]
  //                   (with symmetry)
  lemma {:rlimit 2360} GcdOddLtLemma(a: nat, b: nat)
    requires a > 0 && b > 0
    requires a % 2 == 1 && b % 2 == 1
    requires a < b
    ensures gcd(a, b) == gcd((b - a) / 2, a)
  {
    GcdSubtractLemma(a, b);
    assert gcd(a, b) == gcd(a, b - a);
    var diff := b - a;
    assert diff > 0;
    assert diff % 2 == 0;
    GcdSymmetricLemma(a, diff);
    assert gcd(a, diff) == gcd(diff, a);
    GcdEvenOddLemma(diff, a);
    assert gcd(diff, a) == gcd(diff / 2, a);
    GcdSymmetricLemma(diff / 2, a);
  }

  // gcd(a, b) = gcd((a-b)/2, b) when both odd, a >= b.
  lemma {:rlimit 1814} GcdOddGeLemma(a: nat, b: nat)
    requires a >= b > 0
    requires a % 2 == 1 && b % 2 == 1
    ensures gcd(a, b) == gcd((a - b) / 2, b)
  {
    if a == b {
      // gcd(a, a) = a, and gcd(0, b) = b = a
      DividesSelfLemma(a);
      GcdDividesBothLemma(a, a);
      GcdIsGreatestLemma(a, a, a);
      DividesBoundLemma(a, gcd(a, a));
      DividesBoundLemma(gcd(a, a), a);
    } else {
      GcdSymmetricLemma(a, b);
      assert gcd(a, b) == gcd(b, a);
      GcdSubtractLemma(b, a);
      assert gcd(b, a) == gcd(b, a - b);
      var diff := a - b;
      assert diff > 0;
      assert diff % 2 == 0;
      GcdEvenOddLemma(diff, b);
      GcdSymmetricLemma(b, diff);
      assert gcd(b, diff) == gcd(diff, b);
      assert gcd(diff, b) == gcd(diff / 2, b);
    }
  }

  // gcd(0, b) == b.
  lemma {:rlimit 20} GcdZeroLemma(b: nat)
    ensures gcd(0, b) == b
  {
  }

  // Primality predicate: p has no divisors other than 1 and p.
  ghost predicate IsPrime(p: nat) {
    p >= 2 && forall d: nat :: 1 < d < p ==> p % d != 0
  }

  // gcd(a, p) == 1 for prime p when 0 < a < p.
  // Proof: gcd(a, p) divides p. Since p is prime, gcd(a,p) ∈ {1, p}.
  // Since gcd(a,p) | a and a < p, we have gcd(a,p) <= a < p,
  // so gcd(a,p) != p, thus gcd(a,p) == 1.
  lemma {:rlimit 80} PrimeGcdLemma(a: nat, p: nat)
    requires IsPrime(p)
    requires 0 < a < p
    ensures gcd(a, p) == 1
  {
    var g := gcd(a, p);
    GcdDividesBothLemma(a, p);
    assert divides(g, a) && divides(g, p);
    // g > 0: since g | a and a > 0, g > 0
    if g == 0 {
      // g | a means exists k :: a == 0 * k == 0. But a > 0. Contradiction.
      var k :| a == 0 * k;
      assert a == 0;
    }
    assert g > 0;
    // g | a and a > 0 => g <= a < p, so g != p.
    DividesBoundLemma(g, a);
    assert g <= a < p;
    // g | p and g > 0 and g < p. By primality, g == 1.
    GcdDivisorOfPrimeLemma(g, p);
  }

  // If d | p and p is prime, then d == 1 or d == p.
  lemma {:rlimit 45} GcdDivisorOfPrimeLemma(d: nat, p: nat)
    requires IsPrime(p)
    requires d > 0
    requires divides(d, p)
    ensures d == 1 || d == p
  {
    var k :| p == d * k;
    if d == 1 || d == p {
    } else {
      // 1 < d < p (since d > 0 and d != 1 and d != p)
      // But d | p means p % d == 0, contradicting primality.
      assert d > 1;
      if d > p {
        DividesBoundLemma(d, p);
        assert d <= p;
        assert false;
      }
      assert 1 < d < p;
      DividesModZeroLemma(d, p);
      assert p % d == 0;
      // IsPrime(p) says forall d :: 1 < d < p ==> p % d != 0
      assert false;
    }
  }

  // ===================================================================
  // BEZOUT'S IDENTITY AND EUCLID'S LEMMA
  // ===================================================================

  // Extended GCD: returns (s, t) such that a*s + b*t == gcd(a, b).
  ghost function {:rlimit 57} bezout_coeffs(a: nat, b: nat): (int, int)
    decreases a + b
  {
    if b == 0 then (if a == 0 then (0, 0) else (1, 0))
    else if a == 0 then (0, 1)
    else if a < b then
      var (s', t') := bezout_coeffs(a, b % a);
      (s' - (b / a) as int * t', t')
    else
      var (s', t') := bezout_coeffs(b, a % b);
      (t', s' - (a / b) as int * t')
  }

  lemma {:rlimit 1587} {:isolate_assertions} BezoutIdentityLemma(a: nat, b: nat)
    decreases a + b
    ensures var (s, t) := bezout_coeffs(a, b);
            a as int * s + b as int * t == gcd(a, b) as int
  {
    if b == 0 {
    } else if a == 0 {
    } else if a < b {
      BezoutIdentityLemma(a, b % a);
      var (s', t') := bezout_coeffs(a, b % a);
      DivMod.LemmaFundamentalDivMod(b, a);
      var q := (b / a) as int;
      var r := (b % a) as int;
      assert b as int == q * a as int + r by {
        DivMod.LemmaFundamentalDivMod(b, a);
      }
      assert a as int * s' + r * t' == gcd(a, b) as int;
      assert a as int * (s' - q * t') + b as int * t'
          == a as int * s' - a as int * q * t' + b as int * t' by {
        assert a as int * (s' - q * t') == a as int * s' - a as int * q * t';
      }
      assert a as int * s' - a as int * q * t' + b as int * t'
          == a as int * s' + (b as int - a as int * q) * t';
      assert b as int - a as int * q == r;
    } else {
      BezoutIdentityLemma(b, a % b);
      var (s', t') := bezout_coeffs(b, a % b);
      DivMod.LemmaFundamentalDivMod(a, b);
      var q := (a / b) as int;
      var r := (a % b) as int;
      assert a as int == q * b as int + r by {
        DivMod.LemmaFundamentalDivMod(a, b);
      }
      assert b as int * s' + r * t' == gcd(a, b) as int;
      assert a as int * t' + b as int * (s' - q * t')
          == b as int * s' + (a as int - b as int * q) * t' by {
        assert b as int * (s' - q * t') == b as int * s' - b as int * q * t';
        assert a as int * t' + b as int * s' - b as int * q * t'
            == b as int * s' + (a as int - b as int * q) * t';
      }
      assert a as int - b as int * q == r;
    }
  }

  // Helper: extract b from a Bezout-based product.
  // If a*s + b*t == 1 and a*c == b*q, then c == b*(q*s + c*t).
  lemma {:rlimit 52} BezoutProductLemma(
    a_i: int, b_i: int, c_i: int, s: int, t: int, q_i: int
  )
    requires a_i * s + b_i * t == 1
    requires a_i * c_i == b_i * q_i
    ensures c_i == b_i * (q_i * s + c_i * t)
  {
    calc {
      c_i;
      c_i * 1;
      c_i * (a_i * s + b_i * t);
      { Mul.LemmaMulIsDistributiveAddOtherWay(c_i, a_i * s, b_i * t); }
      c_i * (a_i * s) + c_i * (b_i * t);
      { Mul.LemmaMulIsAssociative(c_i, a_i, s);
        Mul.LemmaMulIsAssociative(c_i, b_i, t); }
      (c_i * a_i) * s + (c_i * b_i) * t;
      { Mul.LemmaMulIsCommutative(c_i, a_i);
        Mul.LemmaMulIsCommutative(c_i, b_i); }
      (a_i * c_i) * s + (b_i * c_i) * t;
      (b_i * q_i) * s + (b_i * c_i) * t;
      { Mul.LemmaMulIsAssociative(b_i, q_i, s);
        Mul.LemmaMulIsAssociative(b_i, c_i, t); }
      b_i * (q_i * s) + b_i * (c_i * t);
      { Mul.LemmaMulIsDistributiveAdd(b_i, q_i * s, c_i * t); }
      b_i * (q_i * s + c_i * t);
    }
  }

  // Coprime cancellation: gcd(a, b) == 1 and b | a*c implies b | c.
  lemma {:rlimit 3999} CoprimeDividesProductLemma(a: nat, b: nat, c: nat)
    requires b > 0
    requires gcd(a, b) == 1
    requires divides(b, a * c)
    ensures divides(b, c)
  {
    BezoutIdentityLemma(a, b);
    var (s, t) := bezout_coeffs(a, b);
    assert a as int * s + b as int * t == 1;
    var q :| a * c == b * q;
    BezoutProductLemma(
      a as int, b as int, c as int, s, t, q as int
    );
    var k_int := q as int * s + c as int * t;
    assert c as int == b as int * k_int;
    if k_int < 0 {
      Mul.LemmaMulStrictlyPositive(b, (-k_int) as nat);
      assert b as int * k_int < 0;
    }
    assert k_int >= 0;
    assert c == b * k_int as nat;
  }

  // Euclid's lemma for primes: p | a*b and p ∤ a implies p | b.
  lemma {:rlimit 55} EuclidsLemmaForPrime(p: nat, a: nat, b: nat)
    requires IsPrime(p)
    requires divides(p, a * b)
    requires !divides(p, a)
    ensures divides(p, b)
  {
    // a % p != 0 (since p ∤ a and p > 0)
    if a % p == 0 {
      ModZeroDividesLemma(p, a);
    }
    assert a % p != 0;
    // Reduce: a % p is in (0, p), so gcd(a%p, p) = 1
    var a_mod := a % p;
    assert 0 < a_mod < p;
    PrimeGcdLemma(a_mod, p);
    // gcd(a, p) = gcd(a%p, p) = 1
    GcdModEquivLemma(a, p);
    assert gcd(a, p) == 1;
    // By coprime cancellation: p | a*b and gcd(a, p) = 1 => p | b
    GcdSymmetricLemma(a, p);
    assert gcd(p, a) == 1;
    CoprimeDividesProductLemma(a, p, b);
  }

  // gcd(a, b) == gcd(a % b, b) for b > 0.
  lemma {:rlimit 34} GcdModEquivLemma(a: nat, b: nat)
    requires b > 0
    ensures gcd(a, b) == gcd(a % b, b)
    decreases a
  {
    if a == 0 {
      DivMod.LemmaSmallMod(0, b);
    } else if a < b {
      DivMod.LemmaSmallMod(a, b);
    } else {
      // a >= b > 0
      // gcd(a, b) = gcd(b, a % b) [by definition]
      // gcd(a % b, b): since a % b < b, gcd(a%b, b) = gcd(a%b, b % (a%b))
      //   if a%b == 0: gcd(0, b) = b
      // We use: gcd(a, b) = gcd(b, a%b) = gcd(a%b, b) [by symmetry]
      // And gcd(a%b, b) = gcd(a%b, b).
      // But we need gcd(a, b) = gcd(a%b, b).
      // gcd(a, b) = gcd(b, a%b) [definition, since a >= b]
      // gcd(b, a%b) = gcd(a%b, b) [symmetry]
      GcdSymmetricLemma(b, a % b);
      // gcd(a, b) = gcd(a%b, b). Done.
    }
  }

  // gcd(a*b, p) == 1 when gcd(a, p) == 1 and gcd(b, p) == 1.
  lemma {:rlimit 131} {:isolate_assertions}
    GcdProductCoprimeLemma(a: nat, b: nat, p: nat)
    requires p > 1
    requires gcd(a, p) == 1
    requires gcd(b, p) == 1
    ensures gcd(a * b, p) == 1
  {
    BezoutIdentityLemma(a, p);
    var (s1, t1) := bezout_coeffs(a, p);
    BezoutIdentityLemma(b, p);
    var (s2, t2) := bezout_coeffs(b, p);
    BezoutProductExpandLemma(
      a as int, p as int, s1, t1,
      b as int, p as int, s2, t2
    );
    // Now we know (a*b) * (s1*s2) + p * (...) == 1.
    // Therefore gcd(a*b, p) | 1.
    GcdBezoutOneLemma(a * b, p, s1 * s2,
      a as int * s1 * t2 + b as int * s2 * t1
      + p as int * t1 * t2);
  }

  // If a*s + b*t == 1, then gcd(a, b) == 1.
  lemma {:rlimit 75} GcdBezoutOneLemma(a: nat, b: nat, s: int, t: int)
    requires a as int * s + b as int * t == 1
    ensures gcd(a, b) == 1
  {
    var g := gcd(a, b);
    // g >= 1: trivially, since gcd >= 1 when a + b > 0.
    // a*s + b*t = 1 => a > 0 or b > 0.
    // g | a and g | b, so g | (a*s + b*t) = 1, meaning g | 1.
    GcdDividesBothLemma(a, b);
    // g | a means exists ka :: a == g * ka
    // g | b means exists kb :: b == g * kb
    // a*s + b*t = g*ka*s + g*kb*t = g*(ka*s + kb*t) = 1
    // So g | 1, meaning g <= 1, meaning g == 1 (since g >= 0).
    GcdDividesLinearCombLemma(a, b, s, t);
  }

  // If d | a and d | b, then d | (a*s + b*t) for any int s, t
  // (when the result is non-negative).
  lemma {:rlimit 113} GcdDividesLinearCombLemma(a: nat, b: nat, s: int, t: int)
    requires a as int * s + b as int * t >= 0
    ensures var g := gcd(a, b);
            var lc := (a as int * s + b as int * t) as nat;
            divides(g, lc)
  {
    var g := gcd(a, b);
    GcdDividesBothLemma(a, b);
    var ka :| a == g * ka;
    var kb :| b == g * kb;
    var lc := (a as int * s + b as int * t) as nat;
    // lc = g*ka*s + g*kb*t = g*(ka*s + kb*t)
    assert a as int * s == (g * ka) as int * s;
    assert b as int * t == (g * kb) as int * t;
    var k_int := ka as int * s + kb as int * t;
    assert lc as int == g as int * k_int by {
      Mul.LemmaMulIsAssociative(g, ka, s);
      Mul.LemmaMulIsAssociative(g, kb, t);
      assert (g * ka) as int * s == g as int * (ka as int * s);
      assert (g * kb) as int * t == g as int * (kb as int * t);
      Mul.LemmaMulIsDistributiveAdd(
        g as int, ka as int * s, kb as int * t);
    }
    if k_int < 0 {
      if g == 0 {
        assert lc as int == 0;
      } else {
        assert g as int * k_int < 0;
        assert lc as int >= 0;
        assert false;
      }
    }
    assert k_int >= 0 || g == 0;
    if g == 0 {
      assert lc == 0;
      DividesZeroLemma(0);
    } else {
      assert lc == g * k_int as nat;
    }
  }

  // Expand (a*s1 + m*t1)*(b*s2 + m*t2) into (a*b)*(s1*s2) + m*(...).
  lemma {:rlimit 233} BezoutProductExpandLemma(
    a: int, m: int, s1: int, t1: int,
    b: int, n: int, s2: int, t2: int
  )
    requires a * s1 + m * t1 == 1
    requires b * s2 + n * t2 == 1
    requires m == n
    ensures (a * b) * (s1 * s2) + m * (a * s1 * t2 + b * s2 * t1
            + m * t1 * t2) == 1
  {
    calc {
      (a * s1 + m * t1) * (b * s2 + m * t2);
      { Mul.LemmaMulIsDistributiveAdd(
          a * s1 + m * t1, b * s2, m * t2); }
      (a * s1 + m * t1) * (b * s2)
        + (a * s1 + m * t1) * (m * t2);
      { Mul.LemmaMulIsDistributiveAddOtherWay(
          b * s2, a * s1, m * t1);
        Mul.LemmaMulIsDistributiveAddOtherWay(
          m * t2, a * s1, m * t1); }
      (a * s1) * (b * s2) + (m * t1) * (b * s2)
        + (a * s1) * (m * t2) + (m * t1) * (m * t2);
    }
    // Regroup: (a*b)*(s1*s2) + m*(a*s1*t2 + b*s2*t1 + m*t1*t2)
    Mul.LemmaMulIsAssociative(a, s1, b * s2);
    Mul.LemmaMulIsCommutative(s1, b * s2);
    Mul.LemmaMulIsAssociative(b, s2, s1);
    Mul.LemmaMulIsCommutative(s2, s1);
    assert (a * s1) * (b * s2) == (a * b) * (s1 * s2) by {
      Mul.LemmaMulIsAssociative(a, s1, b * s2);
      Mul.LemmaMulIsAssociative(a, b, s2);
      Mul.LemmaMulIsCommutative(s1, b * s2);
      assert s1 * (b * s2) == (b * s2) * s1;
      Mul.LemmaMulIsAssociative(b, s2, s1);
      Mul.LemmaMulIsCommutative(s2, s1);
      assert s1 * (b * s2) == b * (s1 * s2);
      Mul.LemmaMulIsAssociative(a, b, s1 * s2);
    }
  }

  // (-r)^2 = r^2 (mod p): negation preserves the square.
  // Proof: (p-r)^2 = p*(p-2r) + r^2, and p divides p*(p-2r).
  lemma {:rlimit 3662} NegSquareModLemma(r: int, p: int)
    requires p > 0
    requires 0 <= r < p
    ensures ((p - r) * (p - r)) % p == (r * r) % p
  {
    assert (p - r) * (p - r) == p * (p - 2 * r) + r * r;
    DivMod.LemmaModMultiplesVanish(p - 2 * r, r * r, p);
  }
}
