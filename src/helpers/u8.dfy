include "./Math.dfy"

module u8 {
    import opened Std.BoundedInts
    import MathHelpers

    newtype u8 = w: int | 0 <= w < TWO_TO_THE_8

    function u8Shl(x: u8, shift: nat): u8
        requires shift < 8
    {
        ((x as int * MathHelpers.pow2(shift)) % TWO_TO_THE_8) as u8
    } by method {
        // GHOST CODE
        assert u8ShlIsCorrect(x, shift) by {
            assert forall otherShift : nat {:trigger u8ShlIsCorrect(x, otherShift)} | otherShift < 8 :: u8ShlIsCorrect(x, shift) by {
                u8ShlIsCorrectLemma(x);
            }
        }
        // Implementation
        return ((x as bv8) << shift) as int as u8;
    }

    // u8 or, hard-coded to case of inters
    function u8Or(x: u8, y: u8): u8
        requires y == 0 || y == 1
        requires x % 2 == 0
    {
        x + y
    } by method {
        // Implementation
        return ((x as bv8) | (y as bv8)) as u8;
    }

    // ===================================================================
    // Lemmas
    // ===================================================================

    ghost predicate u8ShlIsCorrect(x: u8, shift: nat)
        requires shift < 8
    {
        ((x as int * MathHelpers.pow2(shift)) % TWO_TO_THE_8) as u8
        ==
        ((x as bv8) << shift) as int as u8
    }

    lemma {:isolate_assertions} {:rlimit 280000} u8ShlIsCorrectLemma(x: u8)
        ensures forall shift: nat | shift < 8 :: u8ShlIsCorrect(x, shift)
    {
        assert u8ShlIsCorrect(x, 0);
        assert u8ShlIsCorrect(x, 1);
        assert u8ShlIsCorrect(x, 2);
        assert u8ShlIsCorrect(x, 3);
        assert u8ShlIsCorrect(x, 4);
        assert u8ShlIsCorrect(x, 5);
        assert u8ShlIsCorrect(x, 6);
        assert u8ShlIsCorrect(x, 7);
    }
}