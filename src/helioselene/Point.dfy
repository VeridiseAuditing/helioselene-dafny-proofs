// Dafny port of Helios point operations from:
// https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/point.rs
//
// Helios is a short-Weierstrass curve over the Curve25519 prime field (Field25519):
//   y^2 = x^3 - 3x + B
// where:
//   Coordinate field:  Field25519 = Z/(2^255 - 19)
//   Scalar field:      HelioseleneField (the Crandall field verified in Field.dfy)
//   B = 0x26bdec0884fe05f20cb42071569fab6432be360d07da8c5b460b82b980fd8c60
//   G = (1, G_Y) where G_Y = 0x611dffc62fe02c759e5ac10f40e009b8e3b147387068aaf810dbdf2d817c67ba
//
// Points are represented in projective (homogeneous) coordinates [X:Y:Z] where
//   affine x = X/Z, affine y = Y/Z.
// The identity element is [0:1:0].
//
// Verification status:
//   - Basic constructors/helpers (`point_identity`, `point_generator`,
//     `point_from_xy`, `point_neg`, `point_eq`, `point_is_identity`,
//     `point_select`, `point_sub`) are mechanically verified
//   - Arithmetic-heavy methods (`point_add`, `point_double`,
//     `point_scalar_mul`) remain {:verify false} structural ports
//   - Full algebraic group-law proofs still require a fuller Field25519
//     arithmetic model
//
// Note: Field25519 arithmetic is modeled abstractly here. A future session would
//   need to add Field25519.dfy analogous to Field.dfy for the Helioselene field.
//
// Scope note: SelenePoint (the dual curve using HelioseleneField as coordinates)
// uses identical point operation logic (same curve! macro). Excluded because the
// algorithmic logic is identical to HeliosPoint; only field instantiation and
// constants differ. See XLATE-108 / SPEC-005.

include "../crypto_bigint_0_5_5/Limb.dfy"
include "../crypto_bigint_0_5_5/U256.dfy"
include "../helpers/Modular.dfy"
include "Field.dfy"

module HelioselenePoint {
  import opened CryptoBigint_0_5_5_Limb
  import opened CryptoBigint_0_5_5_U256
  import opened HelioseleneFieldMod
  import opened FieldBase

  // ===================================================================
  // FIELD25519: ABSTRACT MODEL
  // ===================================================================
  //
  // Field25519 is Fp where p25519 = 2^255 - 19 (Curve25519 prime).
  // We model it abstractly: each instance carries a ghost `value` in [0, p25519).
  // All arithmetic operations are {:verify false} stubs. A full formalization
  // would require a Field25519.dfy analogous to Field.dfy.
  //
  // Known limitation: All Field25519 methods are {:verify false}. Point operation
  // proofs (OnCurve preservation) require a verified Field25519.dfy. See XLATE-109.

  const F25519_MOD: int := 57896044618658097711785492504343953926634992332820282019728792003956564819949  // 2^255 - 19

  class Field25519 {
    // NOTE: `var` instead of `ghost var` because all methods are {:verify false}
    // stubs that assign to value. A full Field25519.dfy would carry U256 state
    // and use `ghost var` for the mathematical model. See SPEC-007.
    var value: int  // mathematical value, in [0, F25519_MOD)

    ghost predicate Valid()
      reads this
    {
      0 <= value < F25519_MOD
    }

    // All field operations are {:verify false} stubs.
    // Postconditions state the mathematical spec; implementations are trusted.

    static method {:verify false} zero() returns (out: Field25519)
      ensures fresh(out)
      ensures out.Valid()
      ensures out.value == 0
    {
      out := new Field25519;
      out.value := 0;
    }

    static method {:verify false} one() returns (out: Field25519)
      ensures fresh(out)
      ensures out.Valid()
      ensures out.value == 1
    {
      out := new Field25519;
      out.value := 1;
    }

    // Construct from a concrete integer value (used for constants like B, G_Y)
    static method {:verify false} from_int(v: int) returns (out: Field25519)
      requires 0 <= v < F25519_MOD
      ensures fresh(out)
      ensures out.Valid()
      ensures out.value == v
    {
      out := new Field25519;
      out.value := v;
    }

    method {:verify false} add(b: Field25519) returns (out: Field25519)
      requires this.Valid()
      requires b.Valid()
      ensures fresh(out)
      ensures out.Valid()
      ensures out.value == (this.value + b.value) % F25519_MOD
    {
      out := new Field25519;
      out.value := (this.value + b.value) % F25519_MOD;
    }

    method {:verify false} sub(b: Field25519) returns (out: Field25519)
      requires this.Valid()
      requires b.Valid()
      ensures fresh(out)
      ensures out.Valid()
      ensures out.value == (this.value - b.value + F25519_MOD) % F25519_MOD
    {
      out := new Field25519;
      out.value := (this.value - b.value + F25519_MOD) % F25519_MOD;
    }

    method {:verify false} mul(b: Field25519) returns (out: Field25519)
      requires this.Valid()
      requires b.Valid()
      ensures fresh(out)
      ensures out.Valid()
      ensures out.value == (this.value * b.value) % F25519_MOD
    {
      out := new Field25519;
      out.value := (this.value * b.value) % F25519_MOD;
    }

    method {:verify false} square() returns (out: Field25519)
      requires this.Valid()
      ensures fresh(out)
      ensures out.Valid()
      ensures out.value == (this.value * this.value) % F25519_MOD
    {
      out := new Field25519;
      out.value := (this.value * this.value) % F25519_MOD;
    }

    method {:verify false} double() returns (out: Field25519)
      requires this.Valid()
      ensures fresh(out)
      ensures out.Valid()
      ensures out.value == (2 * this.value) % F25519_MOD
    {
      out := new Field25519;
      out.value := (2 * this.value) % F25519_MOD;
    }

    method {:verify false} neg() returns (out: Field25519)
      requires this.Valid()
      ensures fresh(out)
      ensures out.Valid()
      ensures out.value == (F25519_MOD - this.value) % F25519_MOD
    {
      out := new Field25519;
      out.value := (F25519_MOD - this.value) % F25519_MOD;
    }

    method {:verify false} f25519_eq(b: Field25519) returns (result: bool)
      requires this.Valid()
      requires b.Valid()
      ensures result <==> this.value == b.value
    {
      result := this.value == b.value;
    }

    method {:verify false} is_zero() returns (result: bool)
      requires this.Valid()
      ensures result <==> this.value == 0
    {
      result := this.value == 0;
    }

    method {:verify false} is_odd() returns (result: bool)
      requires this.Valid()
      ensures result <==> this.value % 2 == 1
    {
      result := this.value % 2 == 1;
    }

    // conditional_negate: negate if condition is true
    method {:verify false} conditional_negate(condition: bool) returns (out: Field25519)
      requires this.Valid()
      ensures fresh(out)
      ensures out.Valid()
      ensures condition ==> out.value == (F25519_MOD - this.value) % F25519_MOD
      ensures !condition ==> out.value == this.value
    {
      out := new Field25519;
      if condition {
        out.value := (F25519_MOD - this.value) % F25519_MOD;
      } else {
        out.value := this.value;
      }
    }

    // select: constant-time select between a and b
    static method {:verify false} select(a: Field25519, b: Field25519, choice: bool) returns (out: Field25519)
      requires a.Valid()
      requires b.Valid()
      ensures fresh(out)
      ensures out.Valid()
      ensures !choice ==> out.value == a.value
      ensures choice ==> out.value == b.value
    {
      out := new Field25519;
      if choice { out.value := b.value; } else { out.value := a.value; }
    }
  }

  // ===================================================================
  // CURVE CONSTANTS
  // ===================================================================

  // Helios B coefficient: 0x26bdec0884fe05f20cb42071569fab6432be360d07da8c5b460b82b980fd8c60
  // Decimal derived from big-endian hex via int('26bd...60', 16).
  // Verified: GY^2 ≡ B - 2 (mod p) for G = (1, GY, 1).
  const HELIOS_B_VALUE: int :=
    17523451383230374900436292617863907649717438939964238673872692863501483215968

  // Helios generator y-coordinate: 0x611dffc62fe02c759e5ac10f40e009b8e3b147387068aaf810dbdf2d817c67ba
  // Decimal derived from big-endian hex via int('611d...ba', 16).
  // Verified: GY is even (matches Rust test assert !G.y.is_odd()).
  const HELIOS_G_Y_VALUE: int :=
    43927350165885181914572701368652294970994947138804342515295004363921039321018

  // Helios curve equation: y^2 = x^3 - 3x + B
  // In projective coordinates with Z denominator:
  //   Y^2 * Z = X^3 - 3 * X * Z^2 + B * Z^3  (mod F25519_MOD)
  ghost function CurveEquationRHS(X: int, Z: int): int
  {
    (X * X * X - 3 * X * Z * Z + HELIOS_B_VALUE * Z * Z * Z) % F25519_MOD
  }

  ghost function CurveEquationLHS(Y: int, Z: int): int
  {
    (Y * Y * Z) % F25519_MOD
  }

  // Generator OnCurve: GY^2 ≡ 1 - 3 + B (mod p), i.e., GY^2 ≡ B - 2 (mod p).
  // This is a concrete arithmetic statement on 256-bit integers.
  lemma GeneratorOnCurveLemma()
    ensures CurveEquationLHS(HELIOS_G_Y_VALUE, 1) == CurveEquationRHS(1, 1)
  {}

  lemma NegateYPreservesCurveLHSLemma(y: int, z: int)
    requires 0 <= y < F25519_MOD
    ensures CurveEquationLHS((F25519_MOD - y) % F25519_MOD, z) == CurveEquationLHS(y, z)
  {
    if y == 0 {
    } else {
      assert (F25519_MOD - y) % F25519_MOD == F25519_MOD - y;
      var lhs := (F25519_MOD - y) * (F25519_MOD - y) * z;
      var rhs := y * y * z;
      assert lhs - rhs == F25519_MOD * z * (F25519_MOD - 2 * y);
      assert lhs == rhs + F25519_MOD * z * (F25519_MOD - 2 * y);
      assert lhs % F25519_MOD == rhs % F25519_MOD;
    }
  }

  lemma PointNegOnCurveLemma(X: int, Y: int, Z: int)
    requires 0 <= Y < F25519_MOD
    requires CurveEquationLHS(Y, Z) == CurveEquationRHS(X, Z)
    ensures CurveEquationLHS((F25519_MOD - Y) % F25519_MOD, Z) == CurveEquationRHS(X, Z)
  {
    NegateYPreservesCurveLHSLemma(Y, Z);
  }

  lemma ModAddCompatLemma(a: int, b: int, p: int)
    requires p > 0
    ensures ((a % p) + (b % p)) % p == (a + b) % p
  {
    assert a == (a / p) * p + a % p;
    assert b == (b / p) * p + b % p;
    assert a + b == (a / p + b / p) * p + (a % p + b % p);
  }

  lemma ModMulCompatLemma(a: int, b: int, p: int)
    requires p > 0
    ensures ((a % p) * (b % p)) % p == (a * b) % p
  {
    assert a == (a / p) * p + a % p;
    assert b == (b / p) * p + b % p;
    assert a * b
      == (a / p) * (b / p) * p * p
       + (a / p) * p * (b % p)
       + (b / p) * p * (a % p)
       + (a % p) * (b % p);
    assert a * b
      == p * ((a / p) * (b / p) * p + (a / p) * (b % p) + (b / p) * (a % p))
         + (a % p) * (b % p);
  }

  // ===================================================================
  // FORMULA CORRECTNESS LEMMAS
  // ===================================================================

  // --- dbl-2007-bl-2: point doubling ---
  //
  // The doubling formula's OnCurve preservation follows from the polynomial identity:
  //   Y3²·Z3 - (X3³ - 3·X3·Z3² + B·Z3³) = curve_eq · 512·Y1⁹·Z1⁶
  // where curve_eq = Y1²·Z1 - X1³ + 3·X1·Z1² - B·Z1³.
  // Since OnCurve(P) ⟹ curve_eq ≡ 0 (mod p), the output satisfies OnCurve.

  // TCB AXIOM: Polynomial factorization identity for dbl-2007-bl-2.
  // Verified externally via SymPy:
  //   w = 3*(X1**2 - Z1**2); s = 2*Y1*Z1; R = Y1*s; Bd = 2*X1*R
  //   h = w**2 - 2*Bd; X3 = h*s; Y3 = w*(Bd-h) - 2*R**2; Z3 = s**3
  //   ce = Y1**2*Z1 - X1**3 + 3*X1*Z1**2 - B*Z1**3
  //   diff = expand(Y3**2*Z3 - (X3**3 - 3*X3*Z3**2 + B*Z3**3))
  //   q, r = Poly(diff, Y1).div(Poly(ce, Y1))
  //   assert r == 0 and q == Poly(512*Y1**9*Z1**6, Y1)
  lemma {:verify false} PointDoubleFactorizationLemma(
    X1: int, Y1: int, Z1: int)
    ensures
      var w := 3 * (X1 * X1 - Z1 * Z1);
      var s := 2 * Y1 * Z1;
      var R := Y1 * s;
      var Bd := 2 * X1 * R;
      var h := w * w - 2 * Bd;
      var X3 := h * s;
      var Y3 := w * (Bd - h) - 2 * R * R;
      var Z3 := s * s * s;
      var ce := Y1 * Y1 * Z1 - X1 * X1 * X1
        + 3 * X1 * Z1 * Z1 - HELIOS_B_VALUE * Z1 * Z1 * Z1;
      var cf := 512 * Y1 * Y1 * Y1 * Y1 * Y1
        * Y1 * Y1 * Y1 * Y1 * Z1 * Z1 * Z1 * Z1 * Z1 * Z1;
      Y3 * Y3 * Z3
        - (X3 * X3 * X3 - 3 * X3 * Z3 * Z3
           + HELIOS_B_VALUE * Z3 * Z3 * Z3) == ce * cf

  // Mechanically verified: dbl-2007-bl-2 preserves OnCurve (unmodded formula).
  lemma PointDoubleOnCurveLemma(X1: int, Y1: int, Z1: int)
    requires (Y1 * Y1 * Z1) % F25519_MOD ==
      (X1 * X1 * X1 - 3 * X1 * Z1 * Z1
       + HELIOS_B_VALUE * Z1 * Z1 * Z1) % F25519_MOD
    ensures
      var w := 3 * (X1 * X1 - Z1 * Z1);
      var s := 2 * Y1 * Z1;
      var R := Y1 * s;
      var Bd := 2 * X1 * R;
      var h := w * w - 2 * Bd;
      var X3 := h * s;
      var Y3 := w * (Bd - h) - 2 * R * R;
      var Z3 := s * s * s;
      (Y3 * Y3 * Z3) % F25519_MOD ==
        (X3 * X3 * X3 - 3 * X3 * Z3 * Z3
         + HELIOS_B_VALUE * Z3 * Z3 * Z3) % F25519_MOD
  {
    PointDoubleFactorizationLemma(X1, Y1, Z1);
    var w := 3 * (X1 * X1 - Z1 * Z1);
    var s := 2 * Y1 * Z1;
    var R := Y1 * s;
    var Bd := 2 * X1 * R;
    var h := w * w - 2 * Bd;
    var X3 := h * s;
    var Y3 := w * (Bd - h) - 2 * R * R;
    var Z3 := s * s * s;
    var ce := Y1 * Y1 * Z1 - X1 * X1 * X1
      + 3 * X1 * Z1 * Z1 - HELIOS_B_VALUE * Z1 * Z1 * Z1;
    var cf := 512 * Y1 * Y1 * Y1 * Y1 * Y1
      * Y1 * Y1 * Y1 * Y1 * Z1 * Z1 * Z1 * Z1 * Z1 * Z1;
    var diff := Y3 * Y3 * Z3
      - (X3 * X3 * X3 - 3 * X3 * Z3 * Z3
         + HELIOS_B_VALUE * Z3 * Z3 * Z3);
    assert diff == ce * cf;
    assert ce % F25519_MOD == 0;
    assert ce == (ce / F25519_MOD) * F25519_MOD;
    var q := ce / F25519_MOD;
    assert diff == q * F25519_MOD * cf;
    assert diff % F25519_MOD == 0 by {
      assert q * F25519_MOD * cf == (q * cf) * F25519_MOD;
      assert ((q * cf) * F25519_MOD) % F25519_MOD == 0;
    }
  }

  // --- add-2015-rcb-3: point addition ---
  //
  // The addition formula's OnCurve preservation follows from the identity:
  //   diff = ce_P · q_P + ce_Q · q_Q
  // where ce_P, ce_Q are the curve equations for inputs P and Q.
  // When both inputs are OnCurve, ce_P ≡ ce_Q ≡ 0 (mod p), so diff ≡ 0.
  //
  // The cofactors q_P, q_Q are rational functions (polynomials / Z2³)
  // with hundreds of terms each, verified via SymPy. Too large to state
  // inline; verified by the CAS code below.

  // TCB AXIOM: Point addition formula preserves OnCurve.
  // Verified externally via SymPy (add-2015-rcb-3 for y²=x³-3x+B):
  //   [formula translation matching Point.dfy lines 395-438]
  //   diff = expand(Y3f**2*Z3f - (X3f**3 - 3*X3f*Z3f**2 + B*Z3f**3))
  //   # Divide by ce_Q then ce_P:
  //   q_Q, r_Q = Poly(diff, Y2).div(Poly(ce_Q, Y2))
  //   q_P, r_P = Poly(r_Q, Y1).div(Poly(ce_P, Y1))
  //   assert r_P == 0  # diff ∈ ideal(ce_P, ce_Q)
  //   check = expand(diff - ce_P*q_P - ce_Q*q_Q); assert check == 0
  lemma {:verify false} PointAddFactorizationLemma(
    X1: int, Y1: int, Z1: int,
    X2: int, Y2: int, Z2: int)
    requires (Y1 * Y1 * Z1) % F25519_MOD ==
      (X1 * X1 * X1 - 3 * X1 * Z1 * Z1
       + HELIOS_B_VALUE * Z1 * Z1 * Z1) % F25519_MOD
    requires (Y2 * Y2 * Z2) % F25519_MOD ==
      (X2 * X2 * X2 - 3 * X2 * Z2 * Z2
       + HELIOS_B_VALUE * Z2 * Z2 * Z2) % F25519_MOD
    ensures
      var t0 := X1 * X2;
      var t1 := Y1 * Y2;
      var t2 := Z1 * Z2;
      var t3 := (X1 + Y1) * (X2 + Y2) - (t0 + t1);
      var t4 := (Y1 + Z1) * (Y2 + Z2) - (t1 + t2);
      var Y3a := (X1 + Z1) * (X2 + Z2) - (t0 + t2);
      var X3a := Y3a - HELIOS_B_VALUE * t2;
      var X3b := 3 * X3a;
      var Z3c := t1 - X3b;
      var X3c := t1 + X3b;
      var Y3b := HELIOS_B_VALUE * Y3a - 3 * t2 - t0;
      var Y3c := 3 * Y3b;
      var t0b := 3 * t0 - 3 * t2;
      var X3f := t3 * X3c - t4 * Y3c;
      var Y3f := X3c * Z3c + t0b * Y3c;
      var Z3f := t4 * Z3c + t3 * t0b;
      (Y3f * Y3f * Z3f) % F25519_MOD ==
        (X3f * X3f * X3f - 3 * X3f * Z3f * Z3f
         + HELIOS_B_VALUE * Z3f * Z3f * Z3f) % F25519_MOD

  // ===================================================================
  // HELIOS POINT
  // ===================================================================

  // Projective point: [X:Y:Z] where affine = (X/Z, Y/Z)
  // Identity = [0:1:0]
  datatype HeliosPoint = HeliosPoint(x: Field25519, y: Field25519, z: Field25519)

  ghost predicate ValidPoint(P: HeliosPoint)
    reads P.x, P.y, P.z
  {
    P.x.Valid() && P.y.Valid() && P.z.Valid()
  }

  // OnCurve: projective Weierstrass equation holds
  ghost predicate OnCurve(P: HeliosPoint)
    reads P.x, P.y, P.z
    requires ValidPoint(P)
  {
    CurveEquationLHS(P.y.value, P.z.value) == CurveEquationRHS(P.x.value, P.z.value)
  }

  // IsIdentity: Z = 0 (projective identity)
  ghost predicate IsIdentity(P: HeliosPoint)
    reads P.z
  {
    P.z.value == 0
  }

  // ===================================================================
  // POINT CONSTRUCTORS
  // ===================================================================

  // Identity point: [0:1:0]
  // original code: $Point { x: $Field::ZERO, y: $Field::ONE, z: $Field::ZERO }
  method point_identity() returns (P: HeliosPoint)
    ensures fresh(P.x) && fresh(P.y) && fresh(P.z)
    ensures ValidPoint(P)
    ensures IsIdentity(P)
    ensures OnCurve(P)
  {
    var x := Field25519.zero();
    var y := Field25519.one();
    var z := Field25519.zero();
    P := HeliosPoint(x, y, z);
    assert ValidPoint(P);
    assert IsIdentity(P);
    assert CurveEquationLHS(P.y.value, P.z.value) == 0;
    assert CurveEquationRHS(P.x.value, P.z.value) == 0;
    assert OnCurve(P);
  }

  // Generator point: [1:G_Y:1]
  // original code: G = $Point { x: G_X, y: G_Y, z: $Field::ONE }
  method point_generator() returns (P: HeliosPoint)
    ensures fresh(P.x) && fresh(P.y) && fresh(P.z)
    ensures ValidPoint(P)
    ensures OnCurve(P)
    ensures P.x.value == 1
    ensures P.y.value == HELIOS_G_Y_VALUE
    ensures P.z.value == 1
  {
    var x := Field25519.one();
    var y := Field25519.from_int(HELIOS_G_Y_VALUE);
    var z := Field25519.one();
    P := HeliosPoint(x, y, z);
    assert ValidPoint(P);
    GeneratorOnCurveLemma();
    assert CurveEquationLHS(P.y.value, P.z.value) == CurveEquationRHS(P.x.value, P.z.value);
    assert OnCurve(P);
  }

  // from_xy: create a point from affine coordinates, checking OnCurve
  // original code: from_xy(x, y) -> CtOption<Self>
  // Returns (valid, P): if valid, P is on the curve with affine coords (x, y).
  method {:isolate_assertions} {:timeLimit 240} point_from_xy(x: Field25519, y: Field25519)
    returns (valid: bool, P: HeliosPoint)
    requires x.Valid()
    requires y.Valid()
    ensures valid ==> ValidPoint(P) && OnCurve(P)
    ensures valid ==> P.x.value == x.value && P.y.value == y.value && P.z.value == 1
    ensures !valid ==>
      (y.value * y.value) % F25519_MOD !=
        (x.value * x.value * x.value - 3 * x.value + HELIOS_B_VALUE + F25519_MOD * 4) % F25519_MOD
  {
    // original code: CtOption::new(Self { x, y, z: $Field::ONE }, y.square().ct_eq(&curve_equation(x)))
    var y_sq := y.square();
    // curve_equation(x) = x^3 - x.double() - x + B = x^3 - 3x + B
    var x_sq := x.square();
    var x_cu := x_sq.mul(x);
    var three_x := x.double();
    var three_x_2 := three_x.add(x);  // 3x
    var rhs_no_b := x_cu.sub(three_x_2);  // x^3 - 3x
    var b := Field25519.from_int(HELIOS_B_VALUE);
    var rhs := rhs_no_b.add(b);  // x^3 - 3x + B
    valid := y_sq.f25519_eq(rhs);
    var z := Field25519.one();
    P := HeliosPoint(x, y, z);
    assert ValidPoint(P);
    assert y_sq.value == (y.value * y.value) % F25519_MOD;
    assert x_sq.value == (x.value * x.value) % F25519_MOD;
    ModMulCompatLemma(x.value * x.value, x.value, F25519_MOD);
    assert x_cu.value == (x.value * x.value * x.value) % F25519_MOD;
    assert three_x.value == (2 * x.value) % F25519_MOD;
    ModAddCompatLemma(2 * x.value, x.value, F25519_MOD);
    assert three_x_2.value == (3 * x.value) % F25519_MOD;
    assert rhs_no_b.value == (x.value * x.value * x.value - 3 * x.value + F25519_MOD) % F25519_MOD;
    ModAddCompatLemma(x.value * x.value * x.value - 3 * x.value + F25519_MOD, HELIOS_B_VALUE, F25519_MOD);
    assert rhs.value == (x.value * x.value * x.value - 3 * x.value + HELIOS_B_VALUE + F25519_MOD) % F25519_MOD;
    if valid {
      assert y_sq.value == rhs.value;
      assert CurveEquationLHS(P.y.value, P.z.value) == (y.value * y.value) % F25519_MOD;
      assert CurveEquationRHS(P.x.value, P.z.value) == (x.value * x.value * x.value - 3 * x.value + HELIOS_B_VALUE + F25519_MOD) % F25519_MOD;
      assert OnCurve(P);
    } else {
      assert y_sq.value != rhs.value;
    }
  }

  // ===================================================================
  // POINT NEGATION
  // ===================================================================

  // negate: [X:Y:Z] -> [X:-Y:Z]
  // original code: $Point { x: self.x, y: -self.y, z: self.z }
  method point_neg(P: HeliosPoint) returns (Q: HeliosPoint)
    requires ValidPoint(P)
    ensures fresh(Q.y)
    ensures ValidPoint(Q)
    ensures OnCurve(P) ==> OnCurve(Q)
    ensures Q.x.value == P.x.value
    ensures Q.y.value == (F25519_MOD - P.y.value) % F25519_MOD
    ensures Q.z.value == P.z.value
  {
    var neg_y := P.y.neg();
    Q := HeliosPoint(P.x, neg_y, P.z);
    assert ValidPoint(Q);
    if OnCurve(P) {
      PointNegOnCurveLemma(P.x.value, P.y.value, P.z.value);
      assert Q.x.value == P.x.value;
      assert Q.y.value == (F25519_MOD - P.y.value) % F25519_MOD;
      assert Q.z.value == P.z.value;
      assert CurveEquationLHS(Q.y.value, Q.z.value) == CurveEquationRHS(P.x.value, P.z.value);
      assert CurveEquationRHS(Q.x.value, Q.z.value) == CurveEquationRHS(P.x.value, P.z.value);
      assert OnCurve(Q);
    }
  }

  // Unported: from_bytes (point.rs:345-370) and to_bytes (point.rs:372-397).
  // Serialization (sign bit encoding, y-recovery via sqrt, negative-zero rejection)
  // is a separate verification concern requiring Field25519 sqrt. See XLATE-113.

  // ===================================================================
  // POINT ADDITION: add-2015-rcb-3
  // ===================================================================
  //
  // Unified addition formula for short Weierstrass curves (a = -3).
  // Source: https://hyperelliptic.org/EFD/g1p/auto-shortw-projective.html#addition-add-2015-rcb-3
  // Cost: 12M + 2S + 6D + 17add
  //
  // Precondition: P and Q are any (possibly equal) points on the curve.
  // Postcondition: result is on the curve and equals P + Q (group law).
  //
  // Future work (SPEC-004): Functional correctness postconditions.
  // Current spec: ensures OnCurve(R) (curve membership preservation only).
  // Missing: ensures R represents the group-law result (P+Q, 2P, scalar*P).
  // Prerequisites: verified Field25519 arithmetic, affine group-law ghost functions,
  // projective-to-affine equivalence predicate.

  method {:verify false} point_add(P: HeliosPoint, Q: HeliosPoint) returns (R: HeliosPoint)
    requires ValidPoint(P)
    requires ValidPoint(Q)
    requires OnCurve(P)
    requires OnCurve(Q)
    ensures fresh(R.x) && fresh(R.y) && fresh(R.z)
    ensures ValidPoint(R)
    ensures OnCurve(R)
  {
    // original code: add-2015-rcb-3
    // X1, Y1, Z1 = P.x, P.y, P.z
    // X2, Y2, Z2 = Q.x, Q.y, Q.z
    var X1 := P.x; var Y1 := P.y; var Z1 := P.z;
    var X2 := Q.x; var Y2 := Q.y; var Z2 := Q.z;

    var t0 := X1.mul(X2);          // t0 = X1*X2
    var t1 := Y1.mul(Y2);          // t1 = Y1*Y2
    var t2 := Z1.mul(Z2);          // t2 = Z1*Z2
    var t3_a := X1.add(Y1);        // t3 = X1+Y1
    var t4_a := X2.add(Y2);        // t4 = X2+Y2
    var t3 := t3_a.mul(t4_a);      // t3 = (X1+Y1)*(X2+Y2)
    var t4_b := t0.add(t1);        // t4 = t0+t1
    t3 := t3.sub(t4_b);            // t3 = t3 - t4  (= X1*Y2+X2*Y1)
    var t4_c := Y1.add(Z1);        // t4 = Y1+Z1
    var X3_a := Y2.add(Z2);        // X3 = Y2+Z2
    t4_c := t4_c.mul(X3_a);        // t4 = (Y1+Z1)*(Y2+Z2)
    var X3_b := t1.add(t2);        // X3 = t1+t2
    t4_c := t4_c.sub(X3_b);        // t4 = t4 - X3  (= Y1*Z2+Y2*Z1)
    var X3_c := X1.add(Z1);        // X3 = X1+Z1
    var Y3_a := X2.add(Z2);        // Y3 = X2+Z2
    X3_c := X3_c.mul(Y3_a);        // X3 = (X1+Z1)*(X2+Z2)
    var Y3_b := t0.add(t2);        // Y3 = t0+t2
    var Y3 := X3_c.sub(Y3_b);      // Y3 = X3-Y3  (= X1*Z2+X2*Z1)
    var b := Field25519.from_int(HELIOS_B_VALUE);
    var Z3_a := b.mul(t2);         // Z3 = B*t2
    var X3 := Y3.sub(Z3_a);        // X3 = Y3-Z3
    var Z3_b := X3.double();       // Z3 = X3+X3
    X3 := X3.add(Z3_b);            // X3 = X3+Z3
    var Z3_c := t1.sub(X3);        // Z3 = t1-X3
    X3 := t1.add(X3);              // X3 = t1+X3
    Y3 := b.mul(Y3);               // Y3 = B*Y3
    var t1_b := t2.double();       // t1 = t2+t2
    t2 := t1_b.add(t2);            // t2 = t1+t2  (= 3*t2)
    Y3 := Y3.sub(t2);              // Y3 = Y3-t2
    Y3 := Y3.sub(t0);              // Y3 = Y3-t0
    var t1_c := Y3.double();       // t1 = Y3+Y3
    Y3 := t1_c.add(Y3);            // Y3 = t1+Y3  (= 3*Y3)
    var t1_d := t0.double();       // t1 = t0+t0
    t0 := t1_d.add(t0);            // t0 = t1+t0  (= 3*t0)
    t0 := t0.sub(t2);              // t0 = t0-t2
    var t1_e := t4_c.mul(Y3);      // t1 = t4*Y3
    t2 := t0.mul(Y3);              // t2 = t0*Y3
    Y3 := X3.mul(Z3_c);            // Y3 = X3*Z3
    Y3 := Y3.add(t2);              // Y3 = Y3+t2
    X3 := t3.mul(X3);              // X3 = t3*X3
    X3 := X3.sub(t1_e);            // X3 = X3-t1
    var Z3 := t4_c.mul(Z3_c);      // Z3 = t4*Z3
    var t1_f := t3.mul(t0);        // t1 = t3*t0
    Z3 := Z3.add(t1_f);            // Z3 = Z3+t1

    R := HeliosPoint(X3, Y3, Z3);
    assert ValidPoint(R);
    PointAddFactorizationLemma(P.x.value, P.y.value, P.z.value, Q.x.value, Q.y.value, Q.z.value);
    assert OnCurve(R);
  }

  // ===================================================================
  // POINT DOUBLING: dbl-2007-bl-2
  // ===================================================================
  //
  // Doubling formula for short Weierstrass curves (assumes a = -3).
  // Source: https://hyperelliptic.org/EFD/g1p/auto-shortw-projective.html#doubling-dbl-2007-bl-2
  // Cost: 5M + 6S + 1D + 9add
  //
  method {:verify false} point_double(P: HeliosPoint) returns (R: HeliosPoint)
    requires ValidPoint(P)
    requires OnCurve(P)
    ensures fresh(R.x) && fresh(R.y) && fresh(R.z)
    ensures ValidPoint(R)
    ensures OnCurve(R)
  {
    // original code: dbl-2007-bl-2
    var X1 := P.x; var Y1 := P.y; var Z1 := P.z;

    // w = (X1-Z1)*(X1+Z1) using a=-3 shortcut (3*(X1-Z1)*(X1+Z1) = 3X1^2 - 3Z1^2)
    var tmp1 := X1.sub(Z1);        // X1-Z1
    var tmp2 := X1.add(Z1);        // X1+Z1
    var w_1x := tmp1.mul(tmp2);    // (X1-Z1)*(X1+Z1)
    var w_2x := w_1x.double();     // 2*(X1-Z1)*(X1+Z1)
    var w := w_2x.add(w_1x);       // w = 3*(X1-Z1)*(X1+Z1)  (= 3X1^2 - 3Z1^2)

    var s_pre := Y1.mul(Z1);       // Y1*Z1
    var s := s_pre.double();       // s = 2*Y1*Z1

    var ss := s.square();          // ss = s^2
    var sss := s.mul(ss);          // sss = s*ss = s^3

    var R_ := Y1.mul(s);           // R = Y1*s
    var RR := R_.square();         // RR = R^2

    var B_ := X1.mul(R_);          // X1*R
    var B_double := B_.double();   // B = 2*(X1*R)

    var w_sq := w.square();        // w^2
    var B_2x := B_double.double(); // 2*B
    var h := w_sq.sub(B_2x);       // h = w^2 - 2*B

    var X3 := h.mul(s);            // X3 = h*s
    var tmp3 := B_double.sub(h);   // B-h
    var w_tmp3 := w.mul(tmp3);     // w*(B-h)
    var RR_double := RR.double();  // 2*RR
    var Y3 := w_tmp3.sub(RR_double); // Y3 = w*(B-h) - 2*RR
    var Z3 := sss;                 // Z3 = sss

    // Handle identity: if P is identity (Z1=0), return identity
    // original code: Self::conditional_select(&res, &Self::identity(), self.is_identity())
    // NOTE: Constant-time divergence — Rust uses conditional_select; Dafny uses if/else branch.
    var P_is_id := P.z.is_zero();
    if P_is_id {
      R := HeliosPoint(X3, Y3, Z3);  // overwrite; identity check below
      var id := point_identity();
      R := id;
    } else {
      R := HeliosPoint(X3, Y3, Z3);
    }
    assert ValidPoint(R);
    if P_is_id {
      assert IsIdentity(P);
      assert OnCurve(R);
    } else {
      PointDoubleOnCurveLemma(P.x.value, P.y.value, P.z.value);
      assert CurveEquationLHS(Y3.value, Z3.value) == CurveEquationRHS(X3.value, Z3.value);
      assert OnCurve(R);
    }
  }

  // ===================================================================
  // POINT SUBTRACTION
  // ===================================================================

  // point_sub: P - Q = P + (-Q)
  // original code: self + other.neg()
  method point_sub(P: HeliosPoint, Q: HeliosPoint) returns (R: HeliosPoint)
    requires ValidPoint(P)
    requires ValidPoint(Q)
    requires OnCurve(P)
    requires OnCurve(Q)
    ensures fresh(R.x) && fresh(R.y) && fresh(R.z)
    ensures ValidPoint(R)
    ensures OnCurve(R)
  {
    var neg_Q := point_neg(Q);
    R := point_add(P, neg_Q);
    assert ValidPoint(R);
    assert OnCurve(R);
  }

  // ===================================================================
  // POINT EQUALITY
  // ===================================================================

  // Analysis (XLATE-110 / SPEC-006): point_eq uses x=0 as identity proxy.
  // Soundness: verified externally that B (Helios curve constant) is a quadratic
  // non-residue mod p=2^255-19 (pow(B,(p-1)/2,p) != 1). Therefore no affine point
  // (0, y) satisfies y^2 = 0^3 - 3*0 + B = B (mod p), so x=0 is a safe proxy.
  //
  // point_eq: P == Q in projective coordinates
  // original code: (P.x.is_zero() & Q.x.is_zero()) | (X1*Z2 == X2*Z1 & Y1*Z2 == Y2*Z1)
  method point_eq(P: HeliosPoint, Q: HeliosPoint) returns (result: bool)
    requires ValidPoint(P)
    requires ValidPoint(Q)
    ensures result <==>
      (P.x.value == 0 && Q.x.value == 0) ||
      (P.x.value * Q.z.value % F25519_MOD == Q.x.value * P.z.value % F25519_MOD &&
       P.y.value * Q.z.value % F25519_MOD == Q.y.value * P.z.value % F25519_MOD)
  {
    var x1z2 := P.x.mul(Q.z);
    var x2z1 := Q.x.mul(P.z);
    var y1z2 := P.y.mul(Q.z);
    var y2z1 := Q.y.mul(P.z);
    var both_x_zero := P.x.is_zero();
    var q_x_zero := Q.x.is_zero();
    var both_zero := both_x_zero && q_x_zero;
    var x_eq := x1z2.f25519_eq(x2z1);
    var y_eq := y1z2.f25519_eq(y2z1);
    result := both_zero || (x_eq && y_eq);
    assert both_zero <==> (P.x.value == 0 && Q.x.value == 0);
    assert x_eq <==> x1z2.value == x2z1.value;
    assert y_eq <==> y1z2.value == y2z1.value;
    assert x1z2.value == (P.x.value * Q.z.value) % F25519_MOD;
    assert x2z1.value == (Q.x.value * P.z.value) % F25519_MOD;
    assert y1z2.value == (P.y.value * Q.z.value) % F25519_MOD;
    assert y2z1.value == (Q.y.value * P.z.value) % F25519_MOD;
  }

  // DIVERGENCE (XLATE-107): Dafny checks z == 0; Rust checks x == 0.
  //   Rust: `self.x.ct_eq(&$Field::ZERO)` — constant-time, uses x == 0 as identity proxy.
  //   Dafny: `P.z.is_zero()` — mathematically correct projective identity test.
  //
  //   Both are correct for this curve. The curve equation is y^2 = x^3 - 3x + B.
  //   For x = 0: y^2 = B, and B is a quadratic non-residue mod p (confirmed by the
  //   Rust `zero_x_is_invalid` test: `recover_y(Field::ZERO)` returns None).
  //   Therefore no valid on-curve affine point has x = 0, so x == 0 iff the point
  //   is the identity (represented as (0, 1, 0) in projective coordinates).
  //
  //   The Dafny spec uses z == 0, which is the standard projective identity test and
  //   is strictly stronger (works for any curve). The Rust optimization is safe because
  //   B is a QNR, but proving this formally would require a verified Euler criterion
  //   check on B over Field25519.
  method point_is_identity(P: HeliosPoint) returns (result: bool)
    requires ValidPoint(P)
    ensures result <==> IsIdentity(P)
  {
    result := P.z.is_zero();
    assert result <==> P.z.value == 0;
  }

  // ===================================================================
  // SCALAR MULTIPLICATION
  // ===================================================================
  //
  // 4-bit windowed scalar multiplication.
  // Scalar is a HelioseleneField element; bits are extracted MSB to LSB.
  // original code: point.rs L276-323
  //
  // {:verify false} — proof requires windowed scalar mul invariant

  method {:verify false} point_scalar_mul(P: HeliosPoint, scalar: HelioseleneField)
    returns (R: HeliosPoint)
    requires ValidPoint(P)
    requires ValidField(scalar)
    requires OnCurve(P)
    ensures fresh(R.x) && fresh(R.y) && fresh(R.z)
    ensures ValidPoint(R)
    ensures OnCurve(R)
  {
    // original code:
    // let mut table = [$Point::identity(); 16];
    // table[1] = self; table[2] = self.double(); ...
    var table: array<HeliosPoint> := new HeliosPoint[16];
    var id := point_identity();
    table[0] := id;
    table[1] := P;
    var t2 := point_double(P);
    table[2] := t2;
    table[3] := point_add(t2, P);
    var t4 := point_double(t2);
    table[4] := t4;
    table[5] := point_add(t4, P);
    var t6 := point_double(table[3]);
    table[6] := t6;
    table[7] := point_add(t6, P);
    var t8 := point_double(t4);
    table[8] := t8;
    table[9] := point_add(t8, P);
    var t10 := point_double(table[5]);
    table[10] := t10;
    table[11] := point_add(t10, P);
    var t12 := point_double(t6);
    table[12] := t12;
    table[13] := point_add(t12, P);
    var t14 := point_double(table[7]);
    table[14] := t14;
    table[15] := point_add(t14, P);

    // original code:
    // let mut res = Self::identity();
    // let mut bits = 0;
    // for (i, mut bit) in other.to_le_bits().iter_mut().rev().enumerate() { ... }
    var res := point_identity();
    var bits: int := 0;
    var scalar_limbs := scalar.inner.as_limbs();

    // Process 256 bits of scalar from MSB to LSB using a 4-bit sliding window.
    var i: int := 0;
    while i < 256
      decreases 256 - i
    {
      // Extract bit (255 - i) from scalar
      var bit_idx := 255 - i;
      var limb_idx := bit_idx / 64;
      var bit_offset := bit_idx % 64;
      var bit: int := (scalar_limbs[limb_idx].word as int / MathHelpers.pow2(bit_offset)) % 2;
      bits := bits * 2 + bit;

      // original code: if ((i + 1) % 4) == 0 { ... }
      if (i + 1) % 4 == 0 {
        if i != 3 {
          // original code: for _ in 0 .. 4 { res = res.double(); }
          var d0 := point_double(res);
          var d1 := point_double(d0);
          var d2 := point_double(d1);
          res := point_double(d2);
        }
        // original code: res += table[usize::from(bits)] (constant-time lookup)
        // NOTE: Constant-time divergence — Rust uses conditional_select loop; Dafny uses direct array indexing.
        res := point_add(res, table[bits]);
        bits := 0;
      }

      i := i + 1;
    }

    R := res;
  }

  // ===================================================================
  // WIDE REDUCE (for non-biased point generation)
  // ===================================================================
  // Helper: select between two points based on a boolean condition
  // original code: Self::conditional_select(&a, &b, choice)
  method point_select(a: HeliosPoint, b: HeliosPoint, choice: bool)
    returns (out: HeliosPoint)
    requires ValidPoint(a)
    requires ValidPoint(b)
    ensures ValidPoint(out)
    ensures !choice ==> out.x.value == a.x.value && out.y.value == a.y.value && out.z.value == a.z.value
    ensures choice ==> out.x.value == b.x.value && out.y.value == b.y.value && out.z.value == b.z.value
  {
    if choice { out := b; } else { out := a; }
    assert ValidPoint(out);
  }
}
