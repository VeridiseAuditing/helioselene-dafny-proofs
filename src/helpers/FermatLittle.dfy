include "NumberTheory.dfy"
include "PowMod.dfy"

// Fermat's Little Theorem and supporting infrastructure.
// Proof chain: choose → absorption → p|C(p,k) → Freshman's Dream → FLT.

module FermatLittle {
  import opened NumberTheory
  import opened PowMod
  import Power = Std.Arithmetic.Power
  import DivMod = Std.Arithmetic.DivMod
  import Mul = Std.Arithmetic.Mul

  // Binomial coefficient via Pascal's triangle.
  ghost function {:rlimit 32} choose(n: nat, k: nat): nat
    decreases n
  {
    if k == 0 || k == n then 1
    else if k > n then 0
    else choose(n - 1, k - 1) + choose(n - 1, k)
  }

  // Absorption identity: k * C(n, k) = n * C(n-1, k-1).
  // Proved by induction following Pascal's rule.
  lemma {:rlimit 9824} AbsorptionLemma(n: nat, k: nat)
    requires n > 0 && 0 < k <= n
    decreases n + k
    ensures k * choose(n, k) == n * choose(n - 1, k - 1)
  {
    if k == n {
      // C(n, n) = 1, C(n-1, n-1) = 1. n * 1 == n * 1. ✓
    } else if k == 1 {
      // C(n, 1) = C(n-1, 0) + C(n-1, 1). C(n-1, 0) = 1.
      // 1 * C(n, 1) = n * C(n-1, 0) = n * 1 = n.
      // C(n, 1) = n. Prove by induction on n.
      ChooseOneLemma(n);
    } else {
      // General case: 1 < k < n, so n >= 3.
      // C(n, k) = C(n-1, k-1) + C(n-1, k)
      // k * C(n, k) = k * C(n-1, k-1) + k * C(n-1, k)
      // By IH on C(n-1, k): k * C(n-1, k) = (n-1) * C(n-2, k-1)
      assert k <= n - 1;
      AbsorptionLemma(n - 1, k);
      assert k * choose(n - 1, k) == (n - 1) * choose(n - 2, k - 1);
      // So k * C(n, k) = k * C(n-1, k-1) + (n-1) * C(n-2, k-1)
      // We want: k * C(n, k) = n * C(n-1, k-1)
      // = n * (C(n-2, k-2) + C(n-2, k-1))
      // = n * C(n-2, k-2) + n * C(n-2, k-1)
      // So need: k * C(n-1, k-1) + (n-1) * C(n-2, k-1)
      //        = n * C(n-2, k-2) + n * C(n-2, k-1)
      // i.e., k * C(n-1, k-1) = n * C(n-2, k-2) + C(n-2, k-1)
      // i.e., k * (C(n-2, k-2) + C(n-2, k-1)) = n * C(n-2, k-2) + C(n-2, k-1)
      // By IH on C(n-1, k-1): (k-1) * C(n-1, k-1) = (n-1) * C(n-2, k-2)
      AbsorptionLemma(n - 1, k - 1);
      assert (k - 1) * choose(n - 1, k - 1)
          == (n - 1) * choose(n - 2, k - 2);
      // k * C(n-1, k-1) = (k-1) * C(n-1, k-1) + C(n-1, k-1)
      //                  = (n-1) * C(n-2, k-2) + C(n-2, k-2) + C(n-2, k-1)
      //                  = n * C(n-2, k-2) - C(n-2, k-2) + C(n-2, k-2) + C(n-2, k-1)
      // Direct computation:
      // k * C(n, k) = k * C(n-1, k-1) + (n-1) * C(n-2, k-1)    ...(*)
      // (k-1) * C(n-1, k-1) = (n-1) * C(n-2, k-2)
      // k * C(n-1, k-1) = (n-1) * C(n-2, k-2) + C(n-1, k-1)
      //                  = (n-1) * C(n-2, k-2) + C(n-2, k-2) + C(n-2, k-1)
      // Substituting into (*):
      // k * C(n, k) = (n-1)*C(n-2,k-2) + C(n-2,k-2) + C(n-2,k-1) + (n-1)*C(n-2,k-1)
      //             = n*C(n-2,k-2) + n*C(n-2,k-1)
      //             = n * (C(n-2,k-2) + C(n-2,k-1))
      //             = n * C(n-1, k-1)
      var cn := choose(n, k);
      var cn1k1 := choose(n - 1, k - 1);
      var cn1k := choose(n - 1, k);
      var cn2k2 := choose(n - 2, k - 2);
      var cn2k1 := choose(n - 2, k - 1);
      assert cn == cn1k1 + cn1k;
      assert cn1k1 == cn2k2 + cn2k1;
      assert k * cn1k == (n - 1) * cn2k1;
      assert (k - 1) * cn1k1 == (n - 1) * cn2k2;
      // k * cn1k1 = (k-1) * cn1k1 + cn1k1
      assert k * cn1k1 == (k - 1) * cn1k1 + cn1k1;
      // = (n-1)*cn2k2 + cn2k2 + cn2k1 = n*cn2k2 + cn2k1
      // But we need it all together:
      calc {
        k * cn;
        k * (cn1k1 + cn1k);
        k * cn1k1 + k * cn1k;
        ((k - 1) * cn1k1 + cn1k1) + (n - 1) * cn2k1;
        (n - 1) * cn2k2 + cn1k1 + (n - 1) * cn2k1;
        (n - 1) * cn2k2 + (cn2k2 + cn2k1) + (n - 1) * cn2k1;
        ((n - 1) * cn2k2 + cn2k2) + (cn2k1 + (n - 1) * cn2k1);
        n * cn2k2 + n * cn2k1;
        n * (cn2k2 + cn2k1);
        n * cn1k1;
      }
    }
  }

  // C(n, 1) = n.
  lemma {:rlimit 58} ChooseOneLemma(n: nat)
    requires n > 0
    ensures choose(n, 1) == n
    decreases n
  {
    if n == 1 {
    } else {
      ChooseOneLemma(n - 1);
      assert choose(n, 1) == choose(n - 1, 0) + choose(n - 1, 1);
    }
  }

  // For prime p and 0 < k < p: p | C(p, k).
  lemma {:rlimit 193} PrimeDividesChooseLemma(p: nat, k: nat)
    requires IsPrime(p)
    requires 0 < k < p
    ensures divides(p, choose(p, k))
  {
    AbsorptionLemma(p, k);
    assert k * choose(p, k) == p * choose(p - 1, k - 1);
    // p | p * C(p-1, k-1) trivially
    assert p * choose(p - 1, k - 1) == k * choose(p, k);
    // So p | k * C(p, k). Since gcd(k, p) = 1 (by PrimeGcdLemma),
    // by Euclid's lemma, p | C(p, k).
    var cpk := choose(p, k);
    assert divides(p, k * cpk) by {
      assert k * cpk == p * choose(p - 1, k - 1);
    }
    // gcd(k, p) = 1
    PrimeGcdLemma(k, p);
    GcdSymmetricLemma(k, p);
    assert gcd(p, k) == 1;
    // By coprime cancellation: p | k*cpk and gcd(p, k) = 1 => p | cpk
    CoprimeDividesProductLemma(k, p, cpk);
  }

  // ===================================================================
  // BINOMIAL SUM AND THEOREM
  // ===================================================================

  // Partial binomial sum: Σ_{i=0}^{j} C(n, i) * x^i.
  ghost function {:rlimit 42} binom_sum(x: int, n: nat, j: nat): int
    requires j <= n
    decreases j
  {
    if j == 0 then choose(n, 0) // == 1
    else binom_sum(x, n, j - 1) + choose(n, j) * Power.Pow(x, j)
  }

  // Key combination lemma: x * binom_sum(x, n-1, j) + binom_sum(x, n-1, j)
  // == binom_sum(x, n, j) + choose(n-1, j) * Pow(x, j+1).
  // Proved by induction on j, using Pascal's rule at each step.
  lemma {:rlimit 50000} {:isolate_assertions} BinomSumProductLemma(x: int, n: nat, j: nat)
    requires n >= 1 && j <= n - 1
    decreases j
    ensures x * binom_sum(x, n - 1, j) + binom_sum(x, n - 1, j)
         == binom_sum(x, n, j)
          + choose(n - 1, j) * Power.Pow(x, j + 1)
  {
    if j == 0 {
      // LHS: x * C(n-1,0) + C(n-1,0) = x + 1
      // RHS: C(n,0) + C(n-1,0) * x^1 = 1 + x
      Power.LemmaPow1(x);
    } else {
      BinomSumProductLemma(x, n, j - 1);
      // IH: x * bs(j-1) + bs(j-1) == bns(j-1) + C(n-1,j-1)*x^j
      var bs_prev := binom_sum(x, n - 1, j - 1);
      var cnj := choose(n - 1, j);
      var xj := Power.Pow(x, j);
      var xj1 := Power.Pow(x, j + 1);
      // binom_sum(x, n-1, j) = bs_prev + cnj * xj
      assert {:isolate} binom_sum(x, n - 1, j) == bs_prev + cnj * xj;
      // x * (bs_prev + cnj*xj) + (bs_prev + cnj*xj)
      // = (x * bs_prev + bs_prev) + (x + 1) * cnj * xj
      // = (x * bs_prev + bs_prev) + cnj * x * xj + cnj * xj
      // = (bns(j-1) + C(n-1,j-1)*x^j) + cnj*x^(j+1) + cnj*x^j  [by IH]
      // = bns(j-1) + (C(n-1,j-1) + cnj)*x^j + cnj*x^(j+1)
      // = bns(j-1) + C(n,j)*x^j + cnj*x^(j+1)  [Pascal]
      // = bns(j) + cnj*x^(j+1)
      assert xj1 == x * xj;
      // Pascal's rule: C(n-1,j-1) + C(n-1,j) = C(n,j)
      assert {:isolate} choose(n - 1, j - 1) + choose(n - 1, j) == choose(n, j);
      calc {
        x * binom_sum(x, n - 1, j) + binom_sum(x, n - 1, j);
        x * (bs_prev + cnj * xj) + (bs_prev + cnj * xj);
        (x * bs_prev + bs_prev) + cnj * xj * x + cnj * xj;
        { assert {:isolate} x * bs_prev + bs_prev
              == binom_sum(x, n, j - 1)
               + choose(n - 1, j - 1) * xj; }
        binom_sum(x, n, j - 1) + choose(n - 1, j - 1) * xj
          + cnj * (x * xj) + cnj * xj;
        binom_sum(x, n, j - 1) + choose(n - 1, j - 1) * xj
          + cnj * xj + cnj * (x * xj);
        binom_sum(x, n, j - 1) + choose(n - 1, j - 1) * xj
          + cnj * xj + cnj * xj1;
        binom_sum(x, n, j - 1) + (choose(n - 1, j - 1) * xj + cnj * xj) + cnj * xj1;
        {
          assert {:isolate} (choose(n - 1, j - 1) + cnj) * xj
            == (choose(n - 1, j - 1) * xj + cnj * xj);
        }
        binom_sum(x, n, j - 1)
          + (choose(n - 1, j - 1) + cnj) * xj + cnj * xj1;
        binom_sum(x, n, j - 1) + choose(n, j) * xj + cnj * xj1;
        binom_sum(x, n, j) + cnj * xj1;
      }
    }
  }

  // Binomial theorem: (x + 1)^n = Σ_{k=0}^{n} C(n, k) * x^k.
  lemma {:rlimit 3053} BinomialTheoremLemma(x: int, n: nat)
    decreases n
    ensures Power.Pow(x + 1, n) == binom_sum(x, n, n)
  {
    if n == 0 {
    } else {
      BinomialTheoremLemma(x, n - 1);
      // (x+1)^n = (x+1) * binom_sum(x, n-1, n-1)
      // Pow(x+1, n) = (x+1) * Pow(x+1, n-1) by definition
      // Apply BinomSumProductLemma with j = n-1:
      // x * bs(n-1,n-1) + bs(n-1,n-1)
      //   == binom_sum(x, n, n-1) + C(n-1,n-1) * x^n
      //   == binom_sum(x, n, n-1) + x^n
      //   == binom_sum(x, n, n-1) + C(n,n) * x^n
      //   == binom_sum(x, n, n)
      BinomSumProductLemma(x, n, n - 1);
      assert choose(n - 1, n - 1) == 1;
      assert choose(n, n) == 1;
      Mul.LemmaMulBasics(Power.Pow(x, n));
    }
  }

  // ===================================================================
  // FERMAT'S LITTLE THEOREM
  // ===================================================================

  // All middle binomial terms are divisible by p:
  // Σ_{k=1}^{j} C(p, k) * x^k ≡ 0 (mod p) for prime p.
  ghost function {:rlimit 44} middle_sum(x: int, p: nat, j: nat): int
    requires 0 < j < p
    decreases j
  {
    if j == 1 then choose(p, 1) * Power.Pow(x, 1)
    else middle_sum(x, p, j - 1) + choose(p, j) * Power.Pow(x, j)
  }

  lemma {:rlimit 311159} MiddleSumDivisibleLemma(x: int, p: nat, j: nat)
    requires IsPrime(p) && 0 < j < p
    decreases j
    ensures middle_sum(x, p, j) % p == 0
  {
    if j == 1 {
      ChooseOneLemma(p);
      Power.LemmaPow1(x);
      assert middle_sum(x, p, 1) == p * x;
      DivMod.LemmaModMultiplesBasic(x, p);
    } else {
      MiddleSumDivisibleLemma(x, p, j - 1);
      PrimeDividesChooseLemma(p, j);
      var cpj := choose(p, j);
      var xj := Power.Pow(x, j);
      // cpj * xj is divisible by p
      DividesModZeroLemma(p, cpj);
      assert cpj % p == 0;
      DivMod.LemmaMulModNoopLeft(cpj, xj, p);
      assert (cpj * xj) % p == 0;
      // middle_sum(x, p, j-1) % p == 0 by IH
      DivMod.LemmaAddModNoop(middle_sum(x, p, j - 1), cpj * xj, p);
    }
  }

  // Relate binom_sum to middle_sum + boundary terms.
  lemma {:rlimit 79} BinomSumDecomposeLemma(x: int, p: nat)
    requires IsPrime(p)
    ensures binom_sum(x, p, p) == 1 + middle_sum(x, p, p - 1)
                                   + Power.Pow(x, p)
  {
    // binom_sum(x, p, p)
    //   = binom_sum(x, p, p-1) + C(p,p) * x^p
    //   = binom_sum(x, p, p-1) + x^p
    // Need: binom_sum(x, p, p-1)
    //   = binom_sum(x, p, 0) + Σ_{k=1}^{p-1} C(p,k)*x^k
    //   = 1 + middle_sum(x, p, p-1)
    BinomSumEqMiddleLemma(x, p, p - 1);
  }

  // binom_sum(x, p, j) = 1 + middle_sum(x, p, j) for 0 < j < p.
  lemma {:rlimit 109} BinomSumEqMiddleLemma(x: int, p: nat, j: nat)
    requires IsPrime(p) && 0 < j < p
    decreases j
    ensures binom_sum(x, p, j) == 1 + middle_sum(x, p, j)
  {
    if j == 1 {
      assert binom_sum(x, p, 1)
          == binom_sum(x, p, 0) + choose(p, 1) * Power.Pow(x, 1);
      assert binom_sum(x, p, 0) == 1;
    } else {
      BinomSumEqMiddleLemma(x, p, j - 1);
    }
  }

  // Freshman's Dream: (a+1)^p ≡ a^p + 1 (mod p) for prime p.
  lemma {:rlimit 4000} {:isolate_assertions}
    FreshmansDreamLemma(a: nat, p: nat)
    requires IsPrime(p)
    ensures Power.Pow(a + 1, p) % p == (Power.Pow(a, p) + 1) % p
  {
    BinomialTheoremLemma(a, p);
    BinomSumDecomposeLemma(a, p);
    MiddleSumDivisibleLemma(a, p, p - 1);
    var ms := middle_sum(a, p, p - 1);
    var ap := Power.Pow(a, p);
    assert Power.Pow(a + 1, p) == 1 + ms + ap;
    assert ms % p == 0;
    // (1 + ms + ap) % p = (1 + ap) % p since ms % p == 0
    assert (1 + ms) % p == 1 % p by {
      assert (1 + ms) % p == (1 % p + ms % p) % p by {
        DivMod.LemmaAddModNoop(1, ms, p);
      }
      assert (1 % p + ms % p) % p == (1 + 0) % p by {
        assert ms % p == 0;
        assert 1 % p == 1 by {
          DivMod.LemmaSmallMod(1, p);
        }
      }
    }
    assert (1 + ms + ap) % p == (1 + ap) % p by {
      DivMod.LemmaAddModNoop(1 + ms, ap, p);
      DivMod.LemmaAddModNoop(1, ap, p);
    }
  }

  // Fermat's Little Theorem: a^p ≡ a (mod p) for prime p and all a >= 0.
  lemma {:rlimit 527} FermatLittleLemma(a: nat, p: nat)
    requires IsPrime(p)
    decreases a
    ensures Power.Pow(a, p) % p == a % p
  {
    if a == 0 {
      Power.LemmaPow0(0);
      assert Power.Pow(0, p) == 0;
    } else {
      FermatLittleLemma(a - 1, p);
      assert Power.Pow(a - 1, p) % p == (a - 1) % p;
      FreshmansDreamLemma(a - 1, p);
      // (a-1+1)^p ≡ (a-1)^p + 1 ≡ (a-1) + 1 = a (mod p)
      assert Power.Pow(a, p) % p == (Power.Pow(a - 1, p) + 1) % p;
      DivMod.LemmaAddModNoop(Power.Pow(a - 1, p), 1, p);
      DivMod.LemmaAddModNoop(a - 1, 1, p);
    }
  }

  // Corollary: a^(p-1) ≡ 1 (mod p) for 0 < a < p and prime p.
  lemma {:rlimit 75} FermatLittleCorollary(a: nat, p: nat)
    requires IsPrime(p)
    requires 0 < a < p
    ensures Power.Pow(a, p - 1) % p == 1
  {
    FermatLittleLemma(a, p);
    DivMod.LemmaSmallMod(a, p);
    assert Power.Pow(a, p) % p == a;
    Power.LemmaPowPositive(a, p - 1);
    var ap1: nat := Power.Pow(a, p - 1);
    assert (a * ap1) % p == a;
    assert (a * 1) % p == a by { DivMod.LemmaSmallMod(a, p); }
    ModularCancelLemma(a, ap1, 1, p);
    DivMod.LemmaSmallMod(1, p);
  }

  // Modular cancellation: a*x ≡ a*y (mod p), gcd(a,p)=1 => x ≡ y (mod p).
  lemma {:rlimit 162} {:isolate_assertions}
    ModularCancelLemma(a: nat, x: nat, y: nat, p: nat)
    requires IsPrime(p)
    requires 0 < a < p
    requires (a * x) % p == (a * y) % p
    ensures x % p == y % p
  {
    if x >= y {
      PrimeGcdLemma(a, p);
      GcdSymmetricLemma(a, p);
      Mul.LemmaMulIsDistributiveSub(a, x, y);
      // a*x = a*y + a*(x-y), so (a*(x-y)) % p == 0
      ModSubtractLemma(a * y, a * (x - y), p);
      ModZeroDividesLemma(p, a * (x - y));
      CoprimeDividesProductLemma(a, p, x - y);
      DividesModZeroLemma(p, x - y);
      // (x-y) % p == 0 means x = y + (x-y) and x % p == y % p
      ModZeroAddLemma(y, x - y, p);
    } else {
      PrimeGcdLemma(a, p);
      GcdSymmetricLemma(a, p);
      Mul.LemmaMulIsDistributiveSub(a, y, x);
      ModSubtractLemma(a * x, a * (y - x), p);
      ModZeroDividesLemma(p, a * (y - x));
      CoprimeDividesProductLemma(a, p, y - x);
      DividesModZeroLemma(p, y - x);
      ModZeroAddLemma(x, y - x, p);
    }
  }

  // If b % p == 0, then (a + b) % p == a % p.
  lemma {:rlimit 440} ModZeroAddLemma(a: nat, b: nat, p: nat)
    requires p > 0
    requires b % p == 0
    ensures (a + b) % p == a % p
  {
    DivMod.LemmaAddModNoop(a, b, p);
  }

  // If (a + b) % p == a % p, then b % p == 0.
  lemma {:rlimit 97353} ModSubtractLemma(a: nat, b: nat, p: nat)
    requires p > 0
    requires (a + b) % p == a % p
    ensures b % p == 0
  {
    DivMod.LemmaAddModNoop(a, b, p);
    // (a + b) % p == (a % p + b % p) % p == a % p
    // Also (a + b) % p == a % p
    // So (a % p + b % p) % p == a % p
    // Let r = a % p. Then (r + b % p) % p == r.
    // This means b % p == 0.
    var r := a % p;
    var s := b % p;
    assert (r + s) % p == r;
    DivMod.LemmaSmallMod(r, p);
    if s != 0 {
      // r + s >= r, and (r + s) % p == r
      // If r + s < p, then r + s == r, so s == 0. Contradiction.
      // If r + s >= p, then (r + s) % p == r + s - p.
      // r + s - p == r => s == p. But s < p. Contradiction.
      if r + s < p {
        DivMod.LemmaSmallMod(r + s, p);
      } else {
        DivMod.LemmaModSubtraction(r, s, p);
        assert s % p == s;
        DivMod.LemmaSmallMod(s, p);
      }
    }
  }
}
