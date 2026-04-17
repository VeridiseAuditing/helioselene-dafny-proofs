module MathHelpers {
    import Power = Std.Arithmetic.Power
    import Power2 = Std.Arithmetic.Power2
    import Mul = Std.Arithmetic.Mul

    function {:rlimit 520} pow(base: int, exp: nat): (power: int)
    {
        Power.Pow(base, exp)
    }

    lemma {:rlimit 25} PowPositiveLemma(base: nat, exp: nat)
        requires base > 0
        ensures pow(base, exp) > 0
    {
        Power.LemmaPowPositive(base, exp);
    }

    function {:rlimit 32} pow2(exp: nat): (power: int)
        ensures pow2(exp) == pow(2, exp)
    {
        Power2.Pow2(exp) as int
    }

    ////////////
    // LEMMAS //
    ////////////

    lemma {:rlimit 26} SumInExponentLemma(base: int, exp1: nat, exp2:  nat)
        ensures pow(base, exp1 + exp2) == pow(base, exp1) * pow(base, exp2)
    {
        Power.LemmaPowAdds(base, exp1, exp2);
    }

    ///////////////////
    // LEMMA Helpers //
    ///////////////////
    lemma {:rlimit 29} AddOneInExponentLemma(base: int, exp: nat)
        ensures pow(base, exp + 1) == pow(base, exp) * pow(base, 1)
    {
        Power.LemmaPowAdds(base, exp, 1);
    }

    // pow2(n) is always positive.
    lemma {:rlimit 32} Pow2PositiveLemma(n: nat)
      ensures pow2(n) > 0
    {
      Power.LemmaPowPositive(2, n);
      Power2.LemmaPow2(n);
    }

    // pow2(n+1) == 2 * pow2(n).
    lemma {:rlimit 63} Pow2DoubleLemma(n: nat)
      ensures pow2(n + 1) == 2 * pow2(n)
    {
      Power2.LemmaPow2(n + 1);
      Power2.LemmaPow2(n);
      Power.LemmaPowAdds(2, n, 1);
      Power.LemmaPow1(2);
      calc {
        pow2(n + 1);
        { }
        Power2.Pow2(n + 1);
        { Power2.LemmaPow2(n + 1); }
        Power.Pow(2, n + 1);
        { Power.LemmaPowAdds(2, n, 1); }
        Power.Pow(2, n) * Power.Pow(2, 1);
        { Power.LemmaPow1(2); }
        Power.Pow(2, n) * 2;
        { Mul.LemmaMulIsCommutative(Power.Pow(2, n), 2); }
        2 * Power.Pow(2, n);
        { Power2.LemmaPow2(n); }
        2 * pow2(n);
      }
    }

    lemma {:rlimit 66} Pow2To64Lemma()
      ensures pow2(64) == 18446744073709551616
    {
      Power2.Lemma2To64();
    }

    lemma {:rlimit 66} Pow2To32Lemma()
      ensures pow2(32) == 4294967296
    {
      Power2.Lemma2To64();
    }

    lemma {:rlimit 520} Pow2To125Lemma()
      ensures pow2(125) == 42535295865117307932921825928971026432
    {
      Power2.Lemma2To64();
      Power2.LemmaPow2(125);
      Power2.LemmaPow2(64);
      Power2.LemmaPow2(32);
      Power2.LemmaPow2(16);
      Power2.LemmaPow2(8);
      Power2.LemmaPow2(4);
      Power2.LemmaPow2(1);
      SumInExponentLemma(2, 64, 61);
      SumInExponentLemma(2, 32, 29);
      SumInExponentLemma(2, 16, 13);
      SumInExponentLemma(2, 8, 5);
      SumInExponentLemma(2, 4, 1);

      calc {
        pow2(125);
        == { Power2.LemmaPow2(125); }
        pow(2, 125);
        == { SumInExponentLemma(2, 64, 61); }
        pow(2, 64) * pow(2, 61);
        == { SumInExponentLemma(2, 32, 29); }
        pow(2, 64) * (pow(2, 32) * pow(2, 29));
        == { SumInExponentLemma(2, 16, 13); }
        pow(2, 64) * (pow(2, 32) * (pow(2, 16) * pow(2, 13)));
        == { SumInExponentLemma(2, 8, 5); }
        pow(2, 64) * (pow(2, 32) * (pow(2, 16) * (pow(2, 8) * pow(2, 5))));
        == { SumInExponentLemma(2, 4, 1); }
        pow(2, 64) * (pow(2, 32) * (pow(2, 16) * (pow(2, 8) * (pow(2, 4) * pow(2, 1)))));
      }

      assert pow(2, 64) == pow2(64);
      assert pow(2, 32) == pow2(32);
      assert pow(2, 16) == pow2(16);
      assert pow(2, 8) == pow2(8);
      assert pow(2, 4) == pow2(4);
      assert pow(2, 1) == pow2(1);
      assert pow2(64) == 18446744073709551616;
      assert pow2(32) == 4294967296;
      assert pow2(16) == 65536;
      assert pow2(8) == 256;
      assert pow2(4) == 16;
      assert pow2(1) == 2;
      assert pow2(125)
        == 18446744073709551616 * 4294967296 * 65536 * 256 * 16 * 2;
      assert 18446744073709551616 * 4294967296 * 65536 * 256 * 16 * 2
        == 42535295865117307932921825928971026432;
    }

    lemma {:rlimit 230} Pow2To512Lemma()
        ensures pow(2, 512) == 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
    {
        Power2.Lemma2To64();
        Power2.LemmaPow2(16);
        assert pow(2, 16) == pow2(16);
        assert pow2(16) == 65536;
        SumInExponentLemma(2, 16, 16);
        Power2.LemmaPow2(32);
        assert pow(2, 32) == pow2(32);
        assert pow2(32) == 4294967296;
        SumInExponentLemma(2, 32, 32);
        Power2.LemmaPow2(64);
        assert pow(2, 64) == pow2(64);
        assert pow2(64) == 18446744073709551616;
        SumInExponentLemma(2, 64, 64);
        assert pow(2, 128) == 340282366920938463463374607431768211456;
        SumInExponentLemma(2, 128, 128);
        assert pow(2, 256) == 115792089237316195423570985008687907853269984665640564039457584007913129639936;
        assert pow(2, 256) * pow(2, 256) == 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096;
        SumInExponentLemma(2, 256, 256);
        assert pow(2, 512) == 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096;
    }
}
