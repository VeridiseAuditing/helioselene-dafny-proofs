include "Red256.dfy"

module FieldRed512 {
  import opened FieldBase
  import opened FieldRed256
  import opened CryptoBigint_0_5_5_Limb
  import opened CryptoBigint_0_5_5_U256
  import opened CryptoBigint_0_5_5_U128
  import opened Limbs
  // Ported from /Users/ben/Veridise/audits/monero/monero-oxide/crypto/helioselene/src/field.rs#L239-L330
  method {:fuel LimbsValueSpec, 9} {:isolate_assertions} {:rlimit 2000001} red512(wide: (U256, U256)) returns (reduced: HelioseleneField)
    requires wide.0.Valid()
    requires wide.1.Valid()
    ensures reduced.inner.Valid()
    ensures reduced.inner.ValueSpec() == Wide512ValueSpec(wide.0, wide.1) % ModulusValueSpec()
    ensures reduced.inner.ValueSpec() < ModulusValueSpec()
    ensures fresh(reduced.inner) && fresh(reduced.inner.limbs)
  {
    // GHOST CODE
    ghost var V := Wide512ValueSpec(wide.0, wide.1);
    ghost var p := ModulusValueSpec();
    ghost var wide_0_limbs := wide.0.limbs[..];
    ghost var wide_1_limbs := wide.1.limbs[..];

    // original code:
    // /*
    //   The premise of the Crandall reduction is how the modulus is equivalent to
    //   2**255 - MODULUS_255_DISTANCE, where MODULUS_255_DISTANCE is short (only two words). This means
    //   2**255 is congruent to MODULUS_255_DISTANCE modulo the modulus, and subtraction of 2**255 is
    //   congruent to subtracting MODULUS_255_DISTANCE.
    // */
    // original code:
    // let mut limbs = [Limb::ZERO; 2 * U256::LIMBS];
    var limbs := new Limb[2 * U256_LIMBS](_ => ZeroLimb());
    // GHOST CODE
    ghost var zero_limbs := limbs[..];

    // original code:
    // limbs[.. U256::LIMBS].copy_from_slice(wide.0.as_limbs());
    var wide_0_as_limbs := wide.0.as_limbs();
    copy_from_slice(limbs, wide_0_as_limbs[..], 0, U256_LIMBS);

    // original code:
    // limbs[U256::LIMBS ..].copy_from_slice(wide.1.as_limbs());
    var wide_1_as_limbs := wide.1.as_limbs();
    copy_from_slice(limbs, wide_1_as_limbs[..], U256_LIMBS, limbs.Length);

    // LEMMAS
    assert limbs[..U256_LIMBS] == wide_0_limbs;
    assert limbs[U256_LIMBS..U256_LIMBS + U256_LIMBS] == wide_1_limbs;
    assert limbs[..] == wide_0_limbs + wide_1_limbs;
    assert LimbsValueSpec(limbs[..]) == V by {
      Wide512LimbsValueConnectLemma(wide_0_limbs, wide_1_limbs);
      Pow256EqWordModulus4Lemma();
    }

    // original code:
    // /*
    //   Perform a 128-bit multiplication with the highest bits, producing a 256-bit value which must
    //   be further shifted by 128 bits.
    // */
    // let mut carries = [Limb::ZERO; U256::LIMBS + U128::LIMBS];
    var carries := new Limb[U256_LIMBS + U128_LIMBS](_ => ZeroLimb());

    // original code:
    // let mut carry;
    var carry := ZeroLimb();

    // GHOST CODE
    ghost var before_first_mac_fold_limbs := limbs[..];
    ghost var td := TwoModulus255DistanceSpec();

    // Port of original code: get constnats into local environment
    var TWO_MODULUS_255_DISTANCE := TwoModulus255Distance();
    var TWO_MODULUS_255_DISTANCE_as_limbs := TWO_MODULUS_255_DISTANCE.as_limbs();

    // GHOST CODE
    assert TWO_MODULUS_255_DISTANCE.ValueSpec() == td;
    // GHOST CODE: snapshot high limbs (indices 6,7 are read-only in this loop)
    ghost var high6 := limbs[6];
    ghost var high7 := limbs[7];

    ghost var td_limbs := [TWO_MODULUS_255_DISTANCE_as_limbs[0], TWO_MODULUS_255_DISTANCE_as_limbs[1]];

    // GHOST CODE: vars to capture per-iteration MAC equation results
    // After i=2: new2 + mid3*W + c4*W^2 == old2 + old3*W + h6*td
    ghost var fold1_new2: int := 0;
    ghost var fold1_mid3: int := 0;
    ghost var fold1_c4: int := 0;
    ghost var fold1_old2: int := LimbToInt(limbs[2]);
    ghost var fold1_old3: int := LimbToInt(limbs[3]);
    // After i=3: new3 + new4*W + c5*W^2 == mid3 + old4*W + h7*td
    ghost var fold1_new3: int := 0;
    ghost var fold1_new4: int := 0;
    ghost var fold1_c5: int := 0;
    ghost var fold1_old4: int := LimbToInt(limbs[4]);


    // original code:
    // for i in U128::LIMBS .. U256::LIMBS {
    //   (limbs[i], carry) =
    //     limbs[i].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[0], Limb::ZERO);
    //   for j in 1 .. U128::LIMBS {
    //     (limbs[i + j], carry) =
    //       limbs[i + j].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[j], carry);
    //   }
    //   carries[i + U128::LIMBS] = carry;
    // }
    for {:isolate_assertions} i:int := U128_LIMBS to U256_LIMBS
      modifies limbs, carries
      // Frame: high limbs 6,7 are never written by this loop
      invariant limbs[6] == high6
      invariant limbs[7] == high7
      // Frame: low limbs 0,1 are never written
      invariant limbs[0] == before_first_mac_fold_limbs[0]
      invariant limbs[1] == before_first_mac_fold_limbs[1]
      // Frame: limbs[5] is never written (outer loop writes only i, i+1; inner loop writes i+j=i+1)
      invariant limbs[5] == before_first_mac_fold_limbs[5]
      // MAC equation from i=2 (established at end of i=2, maintained at i=3)
      invariant i >= 3 ==>
        fold1_new2 + fold1_mid3 * WORD_MODULUS + fold1_c4 * WORD_MODULUS2
        == fold1_old2 + fold1_old3 * WORD_MODULUS + LimbToInt(high6) * td
      // Snapshot connections: after i=2, the ghost vars match actual limbs/carries
      invariant i >= 3 ==> LimbToInt(limbs[2]) == fold1_new2
      invariant i >= 3 ==> LimbToInt(carries[4]) == fold1_c4
      // At i=3 entry, limbs[3] still holds the mid3 value from i=2
      invariant i == 3 ==> LimbToInt(limbs[3]) == fold1_mid3
      // After i=3: second MAC equation
      invariant i >= 4 ==>
        fold1_new3 + fold1_new4 * WORD_MODULUS + fold1_c5 * WORD_MODULUS2
        == fold1_mid3 + fold1_old4 * WORD_MODULUS + LimbToInt(high7) * td
      invariant i >= 4 ==> LimbToInt(limbs[3]) == fold1_new3
      invariant i >= 4 ==> LimbToInt(limbs[4]) == fold1_new4
      invariant i >= 4 ==> LimbToInt(carries[5]) == fold1_c5
      // Helper: original limb values at specific iteration entries (needed for fold1_old* connections)
      invariant i == U128_LIMBS ==> LimbToInt(limbs[2]) == LimbToInt(before_first_mac_fold_limbs[2])
      invariant i == U128_LIMBS ==> LimbToInt(limbs[3]) == LimbToInt(before_first_mac_fold_limbs[3])
      // limbs[4] unchanged through i=2 body (only limbs[2,3] written); needed at i=3 entry
      invariant i <= U128_LIMBS + 1 ==> LimbToInt(limbs[4]) == LimbToInt(before_first_mac_fold_limbs[4])
      // fold1_old* == original limb values (needed to connect MacFoldCombine6 to fold1_effective)
      invariant i >= 3 ==> fold1_old2 == LimbToInt(before_first_mac_fold_limbs[2])
      invariant i >= 3 ==> fold1_old3 == LimbToInt(before_first_mac_fold_limbs[3])
      invariant fold1_old4 == LimbToInt(before_first_mac_fold_limbs[4])
    {
      // GHOST CODE: snapshot pre-MAC Limb values
      ghost var old_i := limbs[i];
      ghost var old_i1 := limbs[i + 1];
      ghost var high_i := limbs[U256_LIMBS + i];
      ghost var old_i_val := LimbToInt(old_i);
      ghost var old_i1_val := LimbToInt(old_i1);
      ghost var high_i_val := LimbToInt(high_i);

      // Original code:
      //   (limbs[i], carry) =
      //     limbs[i].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[0], Limb::ZERO);
      limbs[i], carry := mac(
        limbs[i],
        limbs[U256_LIMBS + i],
        TWO_MODULUS_255_DISTANCE_as_limbs[0],
        ZeroLimb());

      // GHOST CODE: snapshot after j=0
      ghost var limbs_i_after_j0 := limbs[i];
      ghost var carry_after_j0 := carry;
      ghost var limbs_i1_before_inner := limbs[i + 1];
      // limbs[i+1] is unchanged by j=0 MAC, so it still equals old_i1_val
      assert LimbToInt(limbs_i1_before_inner) == old_i1_val;

      // GHOST CODE: snapshot limbs[2] and carries[4] for frame in i=3 iteration
      ghost var limbs2_before_inner := limbs[2];
      ghost var carries4_before_inner := carries[4];

      // Original code:
      //   for j in 1 .. U128::LIMBS {
      //     (limbs[i + j], carry) =
      //       limbs[i + j].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[j], carry);
      //   }
      for j:int := 1 to U128_LIMBS
        modifies limbs, carries
        invariant limbs[6] == high6
        invariant limbs[7] == high7
        invariant limbs[0] == before_first_mac_fold_limbs[0]
        invariant limbs[1] == before_first_mac_fold_limbs[1]
        invariant limbs[5] == before_first_mac_fold_limbs[5]
        invariant limbs[i] == limbs_i_after_j0
        // Frame: limbs[2] preserved when i==3 (inner loop only writes limbs[4])
        invariant i == 3 ==> limbs[2] == limbs2_before_inner
        // Frame: carries[4] preserved (inner loop doesn't write carries)
        invariant carries[4] == carries4_before_inner
        // Frame: limbs[4] preserved when i==2 (inner loop at i=2 only writes limbs[3])
        invariant i == U128_LIMBS ==> LimbToInt(limbs[4]) == LimbToInt(before_first_mac_fold_limbs[4])
        // State at loop entry (j==1)
        invariant j == 1 ==> carry == carry_after_j0
        invariant j == 1 ==> limbs[i + 1] == limbs_i1_before_inner
        // Multiplier preserved (high6 or high7)
        invariant LimbToInt(limbs[U256_LIMBS + i]) == high_i_val
        // Pre-loop MAC j=0 equation
        invariant LimbToInt(limbs_i_after_j0) + LimbToInt(carry_after_j0) * WORD_MODULUS
          == old_i_val + high_i_val * LimbToInt(TWO_MODULUS_255_DISTANCE_as_limbs[0])
        // MAC equation at loop exit
        invariant j == 2 ==>
          LimbToInt(limbs_i_after_j0) + LimbToInt(limbs[i + 1]) * WORD_MODULUS
            + LimbToInt(carry) * WORD_MODULUS2
          == old_i_val + old_i1_val * WORD_MODULUS + high_i_val * td
      {
        // GHOST CODE
        ghost var old_ij_val := LimbToInt(limbs[i + j]);
        ghost var carry_in_val := LimbToInt(carry);

        // Original code:
        //     (limbs[i + j], carry) =
        //       limbs[i + j].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[j], carry);
        limbs[i + j], carry := mac(
          limbs[i + j],
          limbs[U256_LIMBS + i],
          TWO_MODULUS_255_DISTANCE_as_limbs[j],
          carry);

        // GHOST CODE: Derive 2-limb MAC equation
        MacChain2Lemma(
          LimbToInt(limbs_i_after_j0), LimbToInt(carry_after_j0),
          old_i_val, high_i_val,
          LimbToInt(TWO_MODULUS_255_DISTANCE_as_limbs[0]),
          LimbToInt(limbs[i + j]), LimbToInt(carry),
          old_ij_val, LimbToInt(TWO_MODULUS_255_DISTANCE_as_limbs[j]),
          carry_in_val, td);
      }

      // Original code:
      //   carries[i + U128::LIMBS] = carry;
      carries[i + U128_LIMBS] := carry;

      // GHOST CODE: save per-iteration MAC equation results
      // The inner loop proved:
      //   limbs_i_after_j0 + limbs[i+1]*W + carries[i+2]*W^2 == old_i + old_i1*W + high_i*td
      // (Dafny havocs any var assigned in any branch, so assign all in both)
      if i == U128_LIMBS {
        // Assert: old_i_val == before[2], old_i1_val == before[3] (from helper invariants at i=2)
        assert old_i_val == LimbToInt(before_first_mac_fold_limbs[2]);
        assert old_i1_val == LimbToInt(before_first_mac_fold_limbs[3]);
        fold1_new2 := LimbToInt(limbs_i_after_j0);
        fold1_mid3 := LimbToInt(limbs[i + 1]);
        fold1_c4 := LimbToInt(carries[i + U128_LIMBS]);
        fold1_old2 := old_i_val;
        fold1_old3 := old_i1_val;
        // unchanged:
        fold1_new3 := fold1_new3;
        fold1_new4 := fold1_new4;
        fold1_c5 := fold1_c5;
        fold1_old4 := fold1_old4;
      } else {
        // Assert: old_i1_val == before[4] (from helper invariant i <= U128_LIMBS+1 at i=3)
        assert old_i1_val == LimbToInt(before_first_mac_fold_limbs[4]);
        fold1_new3 := LimbToInt(limbs_i_after_j0);
        fold1_new4 := LimbToInt(limbs[i + 1]);
        fold1_c5 := LimbToInt(carries[i + U128_LIMBS]);
        fold1_old4 := old_i1_val; // old limbs[4]
        // mid3 = old_i_val at i=3, which is the limbs[3] value ENTERING i=3
        fold1_mid3 := old_i_val;
        // unchanged:
        fold1_new2 := fold1_new2;
        fold1_c4 := fold1_c4;
        fold1_old2 := fold1_old2;
        fold1_old3 := fold1_old3;
      }
    }

    // GHOST CODE: telescope the two MAC equations via MacFoldCombine6Lemma
    MacFoldCombine6Lemma(
      fold1_old2, fold1_old3, fold1_old4, LimbToInt(high6), LimbToInt(high7),
      fold1_new2, fold1_mid3, fold1_new3, fold1_new4,
      fold1_c4, fold1_c5, td);

    // From MacFoldCombine6Lemma ensures:
    // fold1_new2*W^2 + fold1_new3*W^3 + (fold1_new4 + fold1_c4)*W^4 + fold1_c5*W^5
    //   == fold1_old2*W^2 + fold1_old3*W^3 + fold1_old4*W^4
    //     + (h6*W^2 + h7*W^3) * td
    //
    // Combined with limbs[0..2] unchanged and limbs[5] unchanged:
    // LimbsValueSpec(limbs[0..6]) + carries_contribution
    //   == LimbsValueSpec(before[0..6]) + (h6*W^2 + h7*W^3) * td
    //
    // Since V = LimbsValueSpec(before[0..8])
    //        = LimbsValueSpec(before[0..6]) + (h6*W^2 + h7*W^3) * W^4
    // We get: (using Crandall: W^4 = td + 2p)
    // LimbsValueSpec(limbs[0..6]) + carries ≡ V (mod p)

    // GHOST CODE: snapshot after first MAC fold for Crandall tracking
    ghost var after_fold1_limbs := limbs[..];
    ghost var after_fold1_carries := carries[..];

    // === MOD-P CHAIN: establish fold1_effective ===
    // H1_val = high6*W^2 + high7*W^3 (the "high" portion multiplied for Crandall)
    ghost var H1_val := LimbToInt(high6) * WORD_MODULUS2 + LimbToInt(high7) * WORD_MODULUS3;
    ghost var original_low6_val := LimbsValueSpec(before_first_mac_fold_limbs[0..6]);
    // V = original_low6_val + H1_val * W^4 (from Limbs8Split6Plus2Lemma)
    Limbs8Split6Plus2Lemma(before_first_mac_fold_limbs[..]);
    assert V == original_low6_val + H1_val * WORD_MODULUS4;
    // fold1 replaces H1*W^4 with H1*td (where W^4 = 2p + td), so fold1_effective ≡ V (mod p)
    ghost var fold1_effective := original_low6_val + H1_val * td;
    // fold1_effective = V - H1*(W^4 - td): establishes precondition for Red512CrandallChainLemma
    Fold1EffectiveEquivLemma(fold1_effective, V, H1_val, td, original_low6_val);
    assert fold1_effective == V - H1_val * (WORD_MODULUS4 - td);
    // Expand both 6-limb LimbsValueSpec values:
    LimbsValueSpec6Lemma(
      before_first_mac_fold_limbs[0], before_first_mac_fold_limbs[1],
      before_first_mac_fold_limbs[2], before_first_mac_fold_limbs[3],
      before_first_mac_fold_limbs[4], before_first_mac_fold_limbs[5],
      before_first_mac_fold_limbs[0..6]);
    LimbsValueSpec6Lemma(
      after_fold1_limbs[0], after_fold1_limbs[1], after_fold1_limbs[2],
      after_fold1_limbs[3], after_fold1_limbs[4], after_fold1_limbs[5],
      after_fold1_limbs[0..6]);
    // Frame: after_fold1[0,1,5] == before[0,1,5] (from loop invariants at exit)
    assert after_fold1_limbs[0] == before_first_mac_fold_limbs[0];
    assert after_fold1_limbs[1] == before_first_mac_fold_limbs[1];
    assert after_fold1_limbs[5] == before_first_mac_fold_limbs[5];
    // after_fold1[2,3,4] == fold1_new2,3,4 (from loop invariants at exit, i==4)
    assert LimbToInt(after_fold1_limbs[2]) == fold1_new2;
    assert LimbToInt(after_fold1_limbs[3]) == fold1_new3;
    assert LimbToInt(after_fold1_limbs[4]) == fold1_new4;
    assert LimbToInt(after_fold1_carries[4]) == fold1_c4;
    assert LimbToInt(after_fold1_carries[5]) == fold1_c5;
    // Key: LimbsValueSpec(after_fold1[0..6]) + c4*W^4 + c5*W^5 == fold1_effective
    // Proof: expand both sides using LimbsValueSpec6Lemma; use MacFoldCombine6Lemma (already called)
    // Bridge fold1_old* to before_first_mac_fold_limbs (from loop invariants at exit)
    assert fold1_old2 == LimbToInt(before_first_mac_fold_limbs[2]);
    assert fold1_old3 == LimbToInt(before_first_mac_fold_limbs[3]);
    assert fold1_old4 == LimbToInt(before_first_mac_fold_limbs[4]);
    assert LimbsValueSpec(after_fold1_limbs[0..6]) + fold1_c4 * WORD_MODULUS4 + fold1_c5 * WORD_MODULUS5
      == fold1_effective;
    // Bound needed to prove exit_carry==0 after 384-bit correction:
    // First establish 0 <= original_low6_val < WORD_MODULUS6 via 6-limb bound lemma
    LimbsValueBound6Lemma(
      LimbToInt(before_first_mac_fold_limbs[0]), LimbToInt(before_first_mac_fold_limbs[1]),
      LimbToInt(before_first_mac_fold_limbs[2]), LimbToInt(before_first_mac_fold_limbs[3]),
      LimbToInt(before_first_mac_fold_limbs[4]), LimbToInt(before_first_mac_fold_limbs[5]));
    assert 0 <= original_low6_val < WORD_MODULUS6;
    Fold1EffectiveBoundLemma(LimbToInt(high6), LimbToInt(high7), original_low6_val, td, fold1_effective);
    assert fold1_effective < 2 * WORD_MODULUS6 - td * WORD_MODULUS2;

    // original code:
    // carry = Limb::ZERO;
    carry := ZeroLimb();

    // original code:
    // for j in U256::LIMBS .. (U256::LIMBS + U128::LIMBS) {
    //   (limbs[j], carry) = add_with_bounded_overflow(limbs[j], carries[j], carry);
    // }
    // GHOST: track carry out of j=4 step to prove total preservation
    ghost var cp1_c4out: int := 0;
    for j:int := U256_LIMBS to U256_LIMBS + U128_LIMBS
      invariant carry == ZeroLimb() || carry == LimbFromInt(1)
      invariant 0 <= carry.word && carry.word <= 1
      // Frame: positions 0-3 are not touched by this loop
      invariant limbs[..4] == after_fold1_limbs[..4]
      // Frame: limbs[4] not yet written at j=4 entry; limbs[5] not yet written at j<=5 entry
      invariant j <= U256_LIMBS ==> limbs[4] == after_fold1_limbs[4]
      invariant j <= U256_LIMBS + 1 ==> limbs[5] == after_fold1_limbs[5]
      // Carry starts at zero
      invariant j == U256_LIMBS ==> carry == ZeroLimb()
      // After j=4: carry chain equation at position 4
      invariant j >= U256_LIMBS + 1 ==>
        LimbToInt(limbs[4]) + cp1_c4out * WORD_MODULUS
        == LimbToInt(after_fold1_limbs[4]) + fold1_c4
      invariant j >= U256_LIMBS + 1 ==> cp1_c4out == 0 || cp1_c4out == 1
      // Carry at j=5 entry equals cp1_c4out (the carry out of j=4)
      invariant j == U256_LIMBS + 1 ==> LimbToInt(carry) == cp1_c4out
      // After j=5: carry chain equation at position 5
      invariant j >= U256_LIMBS + 2 ==>
        LimbToInt(limbs[5]) + LimbToInt(carry) * WORD_MODULUS
        == LimbToInt(after_fold1_limbs[5]) + fold1_c5 + cp1_c4out
      modifies limbs
    {
      // GHOST CODE
      ghost var carry_in_j := carry;
      ghost var old_lj := after_fold1_limbs[j];
      assert carries[j] == after_fold1_carries[j];

      // Original code:
      // (limbs[j], carry) = add_with_bounded_overflow(limbs[j], carries[j], carry);
      limbs[j], carry := add_with_bounded_overflow(limbs[j], carries[j], carry);

      // GHOST CODE
      assert carry == ZeroLimb() || carry == LimbFromInt(1);
      assert 0 <= carry.word && carry.word <= 1;
      AddCarryAccountingLemma(old_lj, after_fold1_carries[j], carry_in_j, limbs[j], carry);
      if j == U256_LIMBS {
        cp1_c4out := LimbToInt(carry);
        assert LimbToInt(limbs[4]) + cp1_c4out * WORD_MODULUS
          == LimbToInt(after_fold1_limbs[4]) + fold1_c4;
      } else {
        // j == U256_LIMBS + 1: carry entering this step = cp1_c4out (from invariant)
        assert LimbToInt(carry_in_j) == cp1_c4out;
        assert LimbToInt(limbs[5]) + LimbToInt(carry) * WORD_MODULUS
          == LimbToInt(after_fold1_limbs[5]) + fold1_c5 + cp1_c4out;
      }
    }
    // CarryProp45TotalLemma: new4*W^4 + new5*W^5 + carry_384*W^6
    //   == (old4+c4)*W^4 + (old5+c5)*W^5
    CarryProp45TotalLemma(
      LimbToInt(after_fold1_limbs[4]), LimbToInt(after_fold1_limbs[5]),
      fold1_c4, fold1_c5,
      LimbToInt(limbs[4]), cp1_c4out,
      LimbToInt(limbs[5]), LimbToInt(carry));
    // LimbsValueSpec(limbs[0..6]) + carry_384_val*W^6 == fold1_effective
    LimbsValueSpec6Lemma(limbs[0], limbs[1], limbs[2], limbs[3], limbs[4], limbs[5], limbs[0..6]);
    ghost var value_after_cp1 := LimbsValueSpec(limbs[0..6]);
    LimbsValueBound6Lemma(
      LimbToInt(limbs[0]), LimbToInt(limbs[1]), LimbToInt(limbs[2]),
      LimbToInt(limbs[3]), LimbToInt(limbs[4]), LimbToInt(limbs[5]));
    assert 0 <= value_after_cp1 < WORD_MODULUS6;
    // Help Z3 with the arithmetic: frame gives limbs[0..4] == after_fold1[0..4]
    assert limbs[0] == after_fold1_limbs[0];
    assert limbs[1] == after_fold1_limbs[1];
    assert limbs[2] == after_fold1_limbs[2];
    assert limbs[3] == after_fold1_limbs[3];
    ValueAfterCP1Lemma(
      LimbToInt(after_fold1_limbs[0]), LimbToInt(after_fold1_limbs[1]),
      LimbToInt(after_fold1_limbs[2]), LimbToInt(after_fold1_limbs[3]),
      LimbToInt(after_fold1_limbs[4]), LimbToInt(after_fold1_limbs[5]),
      fold1_c4, fold1_c5,
      LimbToInt(limbs[4]), LimbToInt(limbs[5]), LimbToInt(carry),
      fold1_effective);
    assert value_after_cp1 + LimbToInt(carry) * WORD_MODULUS6 == fold1_effective;

    // GHOST CODE: carry from first carry prop (384th bit status)
    ghost var carry_384 := carry;
    assert value_after_cp1 + LimbToInt(carry_384) * WORD_MODULUS6 == fold1_effective;

    // Original code:
    // /*
    //   The 384th bit may be set, despite just multiplying those limbs out. We resolve this by
    //   explicitly reducing the 384th bit out with the addition of `(2**256 % MODULUS) << 128`. The
    //   resulting carry is guaranteed to be non-zero as
    //   ```
    //   (2**384 - 1) + # The maximum value present in limbs
    //     (((2**128 - 1) * (2 * (2**255 - MODULUS))) << 128) - # Reduce out the maximum highest bits
    //     2**384 + # Subtract the 384th bit, if set
    //     ((2 * (2**255 - MODULUS)) << 128) < # The corresponding reduction for the 384th bit
    //     2**384 # The bound representable by the remaining limbs
    //   ```
    // */
    // let three_eighty_four_carry = carry.wrapping_neg();
    var three_eighty_four_carry := wrapping_neg(carry);
    // GHOST CODE
    assert carry == ZeroLimb() || carry == LimbFromInt(1);
    WrappingNegOfBitLemma(carry, three_eighty_four_carry);

    // Original code:
    // let mut carry = Limb::ZERO;
    carry := ZeroLimb();

    // GHOST: snapshot limbs[0..6] before correction for CorrectionPreservesTotalLemma
    ghost var carry_384_int := LimbToInt(carry_384);
    assert value_after_cp1 + carry_384_int * WORD_MODULUS6 == fold1_effective;
    ghost var corr_L0 := LimbToInt(limbs[0]);
    ghost var corr_L1 := LimbToInt(limbs[1]);
    ghost var corr_L2 := LimbToInt(limbs[2]);
    ghost var corr_L3 := LimbToInt(limbs[3]);
    ghost var corr_L4 := LimbToInt(limbs[4]);
    ghost var corr_L5 := LimbToInt(limbs[5]);
    // Pre-compute the two addends (functions of three_eighty_four_carry and td limbs)
    ghost var corr_add0 := LimbAnd(three_eighty_four_carry, TWO_MODULUS_255_DISTANCE_as_limbs[0]);
    ghost var corr_add1 := LimbAnd(three_eighty_four_carry, TWO_MODULUS_255_DISTANCE_as_limbs[1]);
    // AndMaskTwoDistLemma: LimbToInt(corr_add0) + LimbToInt(corr_add1)*W == carry_384_int * td
    AndMaskTwoDistLemma(carry_384, three_eighty_four_carry,
      TWO_MODULUS_255_DISTANCE_as_limbs[0], TWO_MODULUS_255_DISTANCE_as_limbs[1],
      corr_add0, corr_add1);
    assert LimbToInt(corr_add0) + LimbToInt(corr_add1) * WORD_MODULUS == carry_384_int * td;
    // value_after_cp1 in terms of individual limbs:
    LimbsValueSpec6Lemma(limbs[0], limbs[1], limbs[2], limbs[3], limbs[4], limbs[5], limbs[0..6]);
    assert value_after_cp1 == corr_L0 + corr_L1 * WORD_MODULUS + corr_L2 * WORD_MODULUS2
      + corr_L3 * WORD_MODULUS3 + corr_L4 * WORD_MODULUS4 + corr_L5 * WORD_MODULUS5;

    ghost var corr_c01: int := 0;  // carry out of loop1 j=0 step
    ghost var corr_new2: int := 0;
    ghost var corr_new3: int := 0;

    // original code:
    // for j in 0 .. U128::LIMBS {
    //   (limbs[U128::LIMBS + j], carry) = add_with_bounded_overflow(
    //     limbs[U128::LIMBS + j],
    //     three_eighty_four_carry & TWO_MODULUS_255_DISTANCE.as_limbs()[j],
    //     carry,
    //   );
    // }
    for j:int := 0 to U128_LIMBS
      invariant carry == ZeroLimb() || carry == LimbFromInt(1)
      invariant 0 <= carry.word && carry.word <= 1
      // Carry at loop start is ZeroLimb (set before loop)
      invariant j == 0 ==> carry == ZeroLimb()
      // Carry at j=1 entry equals corr_c01 (carry out of j=0)
      invariant j == 1 ==> LimbToInt(carry) == corr_c01
      // Frame: limbs[0,1,4,5] not written; limbs[2] not written at j=0 entry; limbs[3] not written at j<=1 entry
      invariant LimbToInt(limbs[0]) == corr_L0
      invariant LimbToInt(limbs[1]) == corr_L1
      invariant j == 0 ==> LimbToInt(limbs[2]) == corr_L2
      invariant j <= 1 ==> LimbToInt(limbs[3]) == corr_L3
      invariant LimbToInt(limbs[4]) == corr_L4
      invariant LimbToInt(limbs[5]) == corr_L5
      // After j=0: carry chain at position 2
      invariant j >= 1 ==>
        corr_new2 + corr_c01 * WORD_MODULUS == corr_L2 + LimbToInt(corr_add0)
      invariant j >= 1 ==> corr_new2 == LimbToInt(limbs[2])
      invariant j >= 1 ==> corr_c01 == 0 || corr_c01 == 1
      // After j=1: combined 2-limb equation
      invariant j >= 2 ==>
        corr_new2 + corr_new3 * WORD_MODULUS + LimbToInt(carry) * WORD_MODULUS2
        == corr_L2 + corr_L3 * WORD_MODULUS + carry_384_int * td
      invariant j >= 2 ==> corr_new3 == LimbToInt(limbs[3])
      modifies limbs
    {
      // GHOST CODE
      ghost var carry_in_j1 := carry;
      ghost var old_lj1 := limbs[U128_LIMBS + j];
      ghost var addend_j1 := LimbAnd(three_eighty_four_carry, TWO_MODULUS_255_DISTANCE_as_limbs[j]);

      // Original code:
      //   (limbs[U128::LIMBS + j], carry) = add_with_bounded_overflow(
      //     limbs[U128::LIMBS + j],
      //     three_eighty_four_carry & TWO_MODULUS_255_DISTANCE.as_limbs()[j],
      //     carry,
      //   );
      limbs[U128_LIMBS + j], carry := add_with_bounded_overflow(
        limbs[U128_LIMBS + j],
        LimbAnd(three_eighty_four_carry, TWO_MODULUS_255_DISTANCE_as_limbs[j]),
        carry);

      // GHOST CODE
      assert carry == ZeroLimb() || carry == LimbFromInt(1);
      assert 0 <= carry.word && carry.word <= 1;
      AddCarryAccountingLemma(old_lj1, addend_j1, carry_in_j1, limbs[U128_LIMBS + j], carry);
      if j == 0 {
        assert addend_j1 == corr_add0;
        // carry_in_j1 == ZeroLimb (from invariant j==0 ==> carry==ZeroLimb at body start)
        assert carry_in_j1 == ZeroLimb();
        // old_lj1 == limbs[2] before modification; frame invariant ensures limbs[2]==corr_L2 at j=0 entry
        assert LimbToInt(old_lj1) == corr_L2;
        corr_c01 := LimbToInt(carry);
        corr_new2 := LimbToInt(limbs[2]);
        assert corr_new2 + corr_c01 * WORD_MODULUS == corr_L2 + LimbToInt(corr_add0);
      } else {
        assert addend_j1 == corr_add1;
        // carry_in_j1 == corr_c01 (from invariant j==1 ==> LimbToInt(carry)==corr_c01 at body start)
        assert LimbToInt(carry_in_j1) == corr_c01;
        // old_lj1 == limbs[3] before modification; frame invariant ensures limbs[3]==corr_L3 at j<=1 entry
        assert LimbToInt(old_lj1) == corr_L3;
        corr_new3 := LimbToInt(limbs[3]);
        // Use MacChain2Lemma (h=1) to get the combined 2-limb equation:
        // new2 + new3*W + carry*W^2 = L2 + L3*W + (add0 + add1*W) = L2 + L3*W + carry_384*td
        // Explicit precondition hints to avoid Z3 context search:
        assert corr_new2 + corr_c01 * WORD_MODULUS == corr_L2 + 1 * LimbToInt(corr_add0);  // prec 1
        assert corr_new3 + LimbToInt(carry) * WORD_MODULUS
          == corr_L3 + 1 * LimbToInt(corr_add1) + LimbToInt(carry_in_j1);  // prec 2
        MacChain2Lemma(
          corr_new2, corr_c01, corr_L2, 1, LimbToInt(corr_add0),
          corr_new3, LimbToInt(carry), corr_L3, LimbToInt(corr_add1),
          LimbToInt(carry_in_j1),
          LimbToInt(corr_add0) + LimbToInt(corr_add1) * WORD_MODULUS);
        assert corr_new2 + corr_new3 * WORD_MODULUS + LimbToInt(carry) * WORD_MODULUS2
          == corr_L2 + corr_L3 * WORD_MODULUS + carry_384_int * td;
      }
    }
    ghost var corr_c23 := LimbToInt(carry);
    assert corr_new2 + corr_new3 * WORD_MODULUS + corr_c23 * WORD_MODULUS2
      == corr_L2 + corr_L3 * WORD_MODULUS + carry_384_int * td;

    ghost var corr_c24: int := 0;  // carry out of loop2 j=2 step

    // original code:
    // for j in U128::LIMBS .. U256::LIMBS {
    //   (limbs[U128::LIMBS + j], carry) = add_with_bounded_overflow(
    //     limbs[U128::LIMBS + j],
    //     Limb::ZERO,
    //     carry,
    //   );
    // }
    for j:int := U128_LIMBS to U256_LIMBS
      invariant carry == ZeroLimb() || carry == LimbFromInt(1)
      invariant 0 <= carry.word && carry.word <= 1
      // Frame: limbs[0..4] not written
      invariant LimbToInt(limbs[0]) == corr_L0
      invariant LimbToInt(limbs[1]) == corr_L1
      invariant LimbToInt(limbs[2]) == corr_new2
      invariant LimbToInt(limbs[3]) == corr_new3
      // j=2 entry: limbs[4] unchanged, carry in from loop 1
      invariant j == U128_LIMBS ==> LimbToInt(limbs[4]) == corr_L4
      invariant j == U128_LIMBS ==> LimbToInt(carry) == corr_c23
      // j=3 entry: carry in from j=2 step; limbs[5] still unchanged
      invariant j == U128_LIMBS + 1 ==> LimbToInt(carry) == corr_c24
      invariant j <= U128_LIMBS + 1 ==> LimbToInt(limbs[5]) == corr_L5
      // After j=2: carry chain at position 4
      invariant j >= U128_LIMBS + 1 ==>
        LimbToInt(limbs[4]) + corr_c24 * WORD_MODULUS == corr_L4 + corr_c23
      invariant j >= U128_LIMBS + 1 ==> corr_c24 == 0 || corr_c24 == 1
      // After j=3: carry chain at position 5
      invariant j >= U128_LIMBS + 2 ==>
        LimbToInt(limbs[5]) + LimbToInt(carry) * WORD_MODULUS == corr_L5 + corr_c24
      modifies limbs
    {
      // GHOST CODE
      ghost var carry_in_j2 := carry;
      ghost var old_lj2 := limbs[U128_LIMBS + j];

      // Original code:
      //   (limbs[U128::LIMBS + j], carry) = add_with_bounded_overflow(
      //     limbs[U128::LIMBS + j],
      //     Limb::ZERO,
      //     carry,
      //   );
      limbs[U128_LIMBS + j], carry := add_with_bounded_overflow(
        limbs[U128_LIMBS + j], ZeroLimb(), carry);

      // GHOST CODE
      assert carry == ZeroLimb() || carry == LimbFromInt(1);
      assert 0 <= carry.word && carry.word <= 1;
      AddCarryAccountingLemma(old_lj2, ZeroLimb(), carry_in_j2, limbs[U128_LIMBS + j], carry);
      if j == U128_LIMBS {
        // carry_in_j2 == corr_c23 (from invariant j==2 ==> LimbToInt(carry)==corr_c23)
        assert LimbToInt(carry_in_j2) == corr_c23;
        // old_lj2 == corr_L4 (from invariant j==2 ==> LimbToInt(limbs[4])==corr_L4)
        assert LimbToInt(old_lj2) == corr_L4;
        corr_c24 := LimbToInt(carry);
        assert LimbToInt(limbs[4]) + corr_c24 * WORD_MODULUS == corr_L4 + corr_c23;
      } else {
        // j == U128_LIMBS + 1: carry_in_j2 == corr_c24 (from invariant)
        assert LimbToInt(carry_in_j2) == corr_c24;
        // old_lj2 == corr_L5 (from invariant j<=U128_LIMBS+1 ==> LimbToInt(limbs[5])==corr_L5)
        assert LimbToInt(old_lj2) == corr_L5;
        assert LimbToInt(limbs[5]) + LimbToInt(carry) * WORD_MODULUS == corr_L5 + corr_c24;
      }
    }
    // GHOST CODE
    // After both loops: use CorrectionPreservesTotalLemma for total value equation
    ghost var corr_exit := LimbToInt(carry);
    ghost var corr_new4 := LimbToInt(limbs[4]);
    ghost var corr_new5 := LimbToInt(limbs[5]);
    // Result: corr_new2*W^2 + ... + LimbToInt(limbs[5])*W^5 + corr_exit*W^6
    //       = corr_L2*W^2 + ... + corr_L5*W^5 + carry_384_int*td*W^2
    // Add L0, L1 (unchanged): LimbsValueSpec(limbs[0..6]) + exit*W^6 = value_after_cp1 + carry_384*td*W^2
    assert {:split_here} true;
    assert {:isolate}
      LimbsValueSpec(limbs[0..6])
        == LimbToInt(limbs[0]) + LimbToInt(limbs[1]) * WORD_MODULUS
          + LimbToInt(limbs[2]) * WORD_MODULUS2 + LimbToInt(limbs[3]) * WORD_MODULUS3
          + corr_new4 * WORD_MODULUS4 + corr_new5 * WORD_MODULUS5
      by {
        LimbsValueSpec6Lemma(limbs[0], limbs[1], limbs[2], limbs[3], limbs[4], limbs[5], limbs[0..6]);
      }
    ghost var before_second_val_int := LimbsValueSpec(limbs[0..6]);
    CorrectionTotalBridgeLemma(
      corr_L0, corr_L1, corr_L2, corr_L3, corr_L4, corr_L5,
      corr_new2, corr_new3, corr_new4, corr_new5,
      corr_c23, corr_c24, corr_exit, carry_384_int, td,
      value_after_cp1, before_second_val_int);
    assert before_second_val_int + corr_exit * WORD_MODULUS6
      == value_after_cp1 + carry_384_int * td * WORD_MODULUS2;
    // value_after_cp1 + carry_384*td*W^2
    //   = (fold1_effective - carry_384*W^6) + carry_384*td*W^2
    //   = fold1_effective - carry_384*(W^6 - td*W^2)
    //   = fold1_effective - carry_384*W^2*(W^4 - td)  [CrandallRelation: W^4-td = 2p]
    assert WORD_MODULUS6 == WORD_MODULUS2 * WORD_MODULUS4 by {
      assert {:fuel WORD_MODULUS6,2} WORD_MODULUS6 == WORD_MODULUS4 * WORD_MODULUS2;
    }
    BeforeSecondValBridgeLemma(before_second_val_int, corr_exit, fold1_effective,
      carry_384_int, td, value_after_cp1);
    assert before_second_val_int + corr_exit * WORD_MODULUS6
      == fold1_effective - carry_384_int * WORD_MODULUS2 * (WORD_MODULUS4 - td);
    // Bounds prove exit_carry == 0:
    // fold1_effective < 2*W^6 - td*W^2 (from Fold1EffectiveBoundLemma, already asserted)
    // => before_second_val_int + exit*W^6 < W^6 => exit == 0
    LimbsValueBound6Lemma(
      LimbToInt(limbs[0]), LimbToInt(limbs[1]), LimbToInt(limbs[2]),
      LimbToInt(limbs[3]), LimbToInt(limbs[4]), LimbToInt(limbs[5]));
    assert 0 <= before_second_val_int < WORD_MODULUS6;
    assert carry_384 == ZeroLimb() || carry_384 == LimbFromInt(1);
    assert carry_384_int == 0 || carry_384_int == 1;
    assert 0 <= corr_exit;
    ghost var rhs_before_second := fold1_effective - carry_384_int * WORD_MODULUS2 * (WORD_MODULUS4 - td);
    Carry384BoundLemma(value_after_cp1, carry_384_int, td, fold1_effective);
    assert value_after_cp1 + carry_384_int * td * WORD_MODULUS2 < WORD_MODULUS6;
    assert rhs_before_second == value_after_cp1 + carry_384_int * td * WORD_MODULUS2;
    assert rhs_before_second < WORD_MODULUS6;
    ExitCarryAndBeforeSecondLemma(
      before_second_val_int,
      corr_exit,
      rhs_before_second);
    assert corr_exit == 0;
    assert before_second_val_int == rhs_before_second;

    ghost var after_384_correction_limbs := limbs[..];
    ghost var before_second_mac_fold_limbs := limbs[..];
    // Connect before_second_val_int to the snapshot (limbs unchanged since line 501)
    assert before_second_val_int == LimbsValueSpec(before_second_mac_fold_limbs[0..6]);

    // GHOST CODE: snapshot mid limbs (indices 4,5 are the multipliers for second fold)
    ghost var mid4 := limbs[4];
    ghost var mid5 := limbs[5];

    // GHOST CODE: per-iteration MAC equation vars for second fold
    ghost var fold2_new0: int := 0;
    ghost var fold2_mid1: int := 0;
    ghost var fold2_c2: int := 0;
    ghost var fold2_old0: int := LimbToInt(limbs[0]);
    ghost var fold2_old1: int := LimbToInt(limbs[1]);
    ghost var fold2_new1: int := 0;
    ghost var fold2_new2: int := 0;
    ghost var fold2_c3: int := 0;
    ghost var fold2_old2: int := LimbToInt(limbs[2]);
    // Snapshot equalities — stated here while limbs is unchanged since before_second_mac_fold_limbs
    assert LimbToInt(before_second_mac_fold_limbs[0]) == fold2_old0;
    assert LimbToInt(before_second_mac_fold_limbs[1]) == fold2_old1;
    assert LimbToInt(before_second_mac_fold_limbs[2]) == fold2_old2;
    // Save Limb bounds at definition site for later use
    assert 0 <= fold2_old0 < WORD_MODULUS;
    assert 0 <= fold2_old1 < WORD_MODULUS;
    assert 0 <= fold2_old2 < WORD_MODULUS;

    // original code:
    // // Perform the 128-bit multiplication with the next highest bits
    // for i in 0 .. U128::LIMBS {
    //   (limbs[i], carry) =
    //     limbs[i].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[0], Limb::ZERO);
    //   for j in 1 .. U128::LIMBS {
    //     (limbs[i + j], carry) =
    //       limbs[i + j].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[j], carry);
    //   }
    //   carries[i + U128::LIMBS] = carry;
    // }
    for {:isolate_assertions} i:int := 0 to U128_LIMBS
      modifies limbs, carries
      // Frame: mid limbs 4,5 are read-only in this loop (only writes 0,1,2)
      invariant limbs[4] == mid4
      invariant limbs[5] == mid5
      // Frame: limbs[3] never written by fold2 loop (writes only 0,1,2)
      invariant limbs[3] == before_second_mac_fold_limbs[3]
      // Frame for unmodified limbs: limbs[0] at i=0 entry; limbs[1] at i=0 entry; limbs[2] at i<=1 entry
      invariant i == 0 ==> LimbToInt(limbs[0]) == LimbToInt(before_second_mac_fold_limbs[0])
      invariant i == 0 ==> LimbToInt(limbs[1]) == LimbToInt(before_second_mac_fold_limbs[1])
      invariant i <= 1 ==> LimbToInt(limbs[2]) == LimbToInt(before_second_mac_fold_limbs[2])
      // fold2_old0/1/2 track original values from before_second_mac_fold_limbs
      invariant fold2_old0 == LimbToInt(before_second_mac_fold_limbs[0])
      invariant fold2_old1 == LimbToInt(before_second_mac_fold_limbs[1])
      invariant fold2_old2 == LimbToInt(before_second_mac_fold_limbs[2])
      // MAC equation from i=0
      invariant i >= 1 ==>
        fold2_new0 + fold2_mid1 * WORD_MODULUS + fold2_c2 * WORD_MODULUS2
        == fold2_old0 + fold2_old1 * WORD_MODULUS + LimbToInt(mid4) * td
      invariant i >= 1 ==> LimbToInt(limbs[0]) == fold2_new0
      invariant i >= 1 ==> LimbToInt(carries[2]) == fold2_c2
      invariant i == 1 ==> LimbToInt(limbs[1]) == fold2_mid1
      // MAC equation from i=1
      invariant i >= 2 ==>
        fold2_new1 + fold2_new2 * WORD_MODULUS + fold2_c3 * WORD_MODULUS2
        == fold2_mid1 + fold2_old2 * WORD_MODULUS + LimbToInt(mid5) * td
      invariant i >= 2 ==> LimbToInt(limbs[1]) == fold2_new1
      invariant i >= 2 ==> LimbToInt(limbs[2]) == fold2_new2
      invariant i >= 2 ==> LimbToInt(carries[3]) == fold2_c3
      // Bounds on pre-fold limb values (needed for MacTotalBound4Lemma)
      invariant 0 <= fold2_old0 < WORD_MODULUS
      invariant 0 <= fold2_old1 < WORD_MODULUS
      invariant 0 <= fold2_old2 < WORD_MODULUS
    {
      // GHOST CODE: snapshot pre-MAC values
      ghost var old_i_val2 := LimbToInt(limbs[i]);
      ghost var old_i1_val2 := LimbToInt(limbs[i + 1]);
      ghost var high_i_val2 := LimbToInt(limbs[U256_LIMBS + i]);

      // Original code:
      //   (limbs[i], carry) =
      //     limbs[i].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[0], Limb::ZERO);
      limbs[i], carry := mac(
        limbs[i],
        limbs[U256_LIMBS + i],
        TWO_MODULUS_255_DISTANCE_as_limbs[0],
        ZeroLimb());

      // GHOST CODE: snapshot after j=0
      ghost var limbs_i_after_j0_2 := limbs[i];
      ghost var carry_after_j0_2 := carry;
      ghost var limbs_i1_before_inner2 := limbs[i + 1];
      assert LimbToInt(limbs_i1_before_inner2) == old_i1_val2;

      // GHOST CODE: frame snapshot for inner loop
      ghost var limbs0_before_inner2 := limbs[0];
      ghost var carries2_before_inner2 := carries[2];

      // Original code:
      //   for j in 1 .. U128::LIMBS {
      //     (limbs[i + j], carry) =
      //       limbs[i + j].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[j], carry);
      //   }
      //   carries[i + U128::LIMBS] = carry;
      for j:int := 1 to U128_LIMBS
        modifies limbs, carries
        invariant limbs[4] == mid4
        invariant limbs[5] == mid5
        invariant limbs[3] == before_second_mac_fold_limbs[3]
        // At i=0, inner loop only writes limbs[1], not limbs[2]
        invariant i == 0 ==> limbs[2] == before_second_mac_fold_limbs[2]
        invariant limbs[i] == limbs_i_after_j0_2
        // Frame: limbs[0] preserved when i==1 (inner loop only writes limbs[2])
        invariant i == 1 ==> limbs[0] == limbs0_before_inner2
        // Frame: carries[2] preserved when i==1 (inner loop writes carries[3])
        invariant i == 1 ==> carries[2] == carries2_before_inner2
        // State at loop entry
        invariant j == 1 ==> carry == carry_after_j0_2
        invariant j == 1 ==> limbs[i + 1] == limbs_i1_before_inner2
        // Multiplier preserved
        invariant LimbToInt(limbs[U256_LIMBS + i]) == high_i_val2
        // Pre-loop MAC j=0 equation
        invariant LimbToInt(limbs_i_after_j0_2) + LimbToInt(carry_after_j0_2) * WORD_MODULUS
          == old_i_val2 + high_i_val2 * LimbToInt(TWO_MODULUS_255_DISTANCE_as_limbs[0])
        // MAC equation at loop exit
        invariant j == 2 ==>
          LimbToInt(limbs_i_after_j0_2) + LimbToInt(limbs[i + 1]) * WORD_MODULUS
            + LimbToInt(carry) * WORD_MODULUS2
          == old_i_val2 + old_i1_val2 * WORD_MODULUS + high_i_val2 * td
      {
        // GHOST CODE
        ghost var old_ij_val2 := LimbToInt(limbs[i + j]);
        ghost var carry_in_val2 := LimbToInt(carry);

        // Original code:
        //     (limbs[i + j], carry) =
        //       limbs[i + j].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[j], carry);
        limbs[i + j], carry := mac(
          limbs[i + j],
          limbs[U256_LIMBS + i],
          TWO_MODULUS_255_DISTANCE_as_limbs[j],
          carry);

        // GHOST CODE
        MacChain2Lemma(
          LimbToInt(limbs_i_after_j0_2), LimbToInt(carry_after_j0_2),
          old_i_val2, high_i_val2,
          LimbToInt(TWO_MODULUS_255_DISTANCE_as_limbs[0]),
          LimbToInt(limbs[i + j]), LimbToInt(carry),
          old_ij_val2, LimbToInt(TWO_MODULUS_255_DISTANCE_as_limbs[j]),
          carry_in_val2, td);
      }
      // Original code:
      //   carries[i + U128::LIMBS] = carry;
      carries[i + U128_LIMBS] := carry;

      // GHOST CODE: save per-iteration MAC equation results for second fold
      if i == 0 {
        fold2_new0 := LimbToInt(limbs_i_after_j0_2);
        fold2_mid1 := LimbToInt(limbs[i + 1]);
        fold2_c2 := LimbToInt(carries[i + U128_LIMBS]);
        // old_i_val2 = LimbToInt(limbs[0]) at i=0 entry (before modification) == snapshot
        assert old_i_val2 == LimbToInt(before_second_mac_fold_limbs[0]);
        fold2_old0 := old_i_val2;
        // old_i1_val2 = LimbToInt(limbs[1]) at i=0 entry (before modification) == snapshot
        assert old_i1_val2 == LimbToInt(before_second_mac_fold_limbs[1]);
        fold2_old1 := old_i1_val2;
        // unchanged:
        fold2_new1 := fold2_new1;
        fold2_new2 := fold2_new2;
        fold2_c3 := fold2_c3;
        fold2_old2 := fold2_old2;
      } else {
        fold2_new1 := LimbToInt(limbs_i_after_j0_2);
        fold2_new2 := LimbToInt(limbs[i + 1]);
        fold2_c3 := LimbToInt(carries[i + U128_LIMBS]);
        // old_i1_val2 = LimbToInt(limbs[2]) at i=1 entry (before modification) == snapshot
        assert old_i1_val2 == LimbToInt(before_second_mac_fold_limbs[2]);
        fold2_old2 := old_i1_val2;
        fold2_mid1 := old_i_val2;
        // unchanged:
        fold2_new0 := fold2_new0;
        fold2_c2 := fold2_c2;
        fold2_old0 := fold2_old0;
        fold2_old1 := fold2_old1;
      }
    }

    // GHOST CODE: telescope the two second-fold MAC equations
    MacFoldCombine4Lemma(
      fold2_old0, fold2_old1, fold2_old2, LimbToInt(mid4), LimbToInt(mid5),
      fold2_new0, fold2_mid1, fold2_new1, fold2_new2,
      fold2_c2, fold2_c3, td);

    // GHOST CODE: compute mac_total for bounds
    ghost var old3_val := LimbToInt(before_second_mac_fold_limbs[3]);
    // old3_val is defined directly from before_second_mac_fold_limbs, so trivially:
    assert LimbToInt(before_second_mac_fold_limbs[3]) == old3_val;
    ghost var b2 := LimbToInt(mid4) + LimbToInt(mid5) * WORD_MODULUS;

    // From MacFoldCombine4Lemma:
    ghost var combine_lhs :=
      fold2_new0 + fold2_new1 * WORD_MODULUS
      + (fold2_new2 + fold2_c2) * WORD_MODULUS2
      + fold2_c3 * WORD_MODULUS3;
    ghost var combine_rhs :=
      fold2_old0 + fold2_old1 * WORD_MODULUS
      + fold2_old2 * WORD_MODULUS2 + b2 * td;
    assert combine_lhs == combine_rhs;

    // mac_total = combine_lhs + old3*W^3 (add the untouched limbs[3])
    ghost var mac_total_4 := combine_lhs + old3_val * WORD_MODULUS3;
    // low4 = combine_rhs - b2*td + old3*W^3
    ghost var low4_before :=
      fold2_old0 + fold2_old1 * WORD_MODULUS
      + fold2_old2 * WORD_MODULUS2 + old3_val * WORD_MODULUS3;
    assert mac_total_4 == low4_before + b2 * td;

    // Bounds: low4 < W^4 (4 limbs), b2 < 2*W^2 (2 limbs)
    assert 0 <= fold2_old0 < WORD_MODULUS;
    assert 0 <= fold2_old1 < WORD_MODULUS;
    assert 0 <= fold2_old2 < WORD_MODULUS;
    assert 0 <= old3_val < WORD_MODULUS;
    LimbsValueBound4Lemma(fold2_old0, fold2_old1, fold2_old2, old3_val);
    assert 0 <= low4_before < WORD_MODULUS4;
    assert 0 <= b2 < 2 * WORD_MODULUS2;
    MacTotalBound4Lemma(mac_total_4, low4_before, b2);

    // === MOD-P CHAIN: connect fold2 output to before_second_val_int ===
    // before_second_val_int = LimbsValueSpec(before_second_mac_fold_limbs[0..6])
    //   == LimbsValueSpec(before_second_mac_fold_limbs[0..4]) + b2 * W^4  (Limbs6Split4Plus2Lemma)
    //   == low4_before + b2 * W^4  (LimbsValueSpec4Lemma + fold2_old* connections)
    // So mac_total_4 = low4_before + b2*td = before_second_val_int - b2*(W^4-td)
    Limbs6Split4Plus2Lemma(before_second_mac_fold_limbs[0..6]);
    LimbsValueSpec4Lemma(before_second_mac_fold_limbs[0], before_second_mac_fold_limbs[1],
      before_second_mac_fold_limbs[2], before_second_mac_fold_limbs[3],
      before_second_mac_fold_limbs[0..4]);
    assert LimbToInt(before_second_mac_fold_limbs[0]) == fold2_old0;
    assert LimbToInt(before_second_mac_fold_limbs[1]) == fold2_old1;
    assert LimbToInt(before_second_mac_fold_limbs[2]) == fold2_old2;
    assert LimbToInt(before_second_mac_fold_limbs[3]) == old3_val;
    assert before_second_mac_fold_limbs[4] == mid4;
    assert before_second_mac_fold_limbs[5] == mid5;
    assert before_second_val_int == low4_before + b2 * WORD_MODULUS4;
    MacTotalEquivLemma(mac_total_4, before_second_val_int, low4_before, b2, td);
    assert mac_total_4 == before_second_val_int - b2 * (WORD_MODULUS4 - td);

    // Original code:
    // carry = Limb::ZERO;
    carry := ZeroLimb();

    // GHOST CODE: The total value entering carry prop is mac_total_4.
    // limbs = [new0, new1, new2_fold, old3], carries[2]=c2, carries[3]=c3, carry=0.
    // mac_total_4 = new0 + new1*W + (new2_fold+c2)*W^2 + (old3+c3)*W^3.
    // The carry prop absorbs c2 and c3, preserving the total.
    // After: LimbsValueSpec(limbs[0..4]) + carry * W^4 == mac_total_4.
    // And mac_total_4 < 2*W^4 - td (from MacTotalBound4Lemma).

    // GHOST CODE: carry prop total tracking
    // Before: total = new0 + new1*W + new2*W^2 + old3*W^3 + 0*W^4 + c2*W^2 + c3*W^3
    // The ghost variable `cp_total` tracks the portion from position j onwards
    // that hasn't been absorbed yet: limbs[j]*W^j + carry*W^j + remaining carries.
    // We track: LimbsValueSpec(limbs[0..j]) + carry*W^j = mac_total_4 - remaining
    ghost var cp_sum_low: int :=
      fold2_new0 + fold2_new1 * WORD_MODULUS;  // limbs[0] + limbs[1]*W (unchanged by carry prop)
    ghost var cp_remaining: int :=
      (fold2_new2 + fold2_c2) * WORD_MODULUS2
      + (old3_val + fold2_c3) * WORD_MODULUS3;

    // GHOST CODE: carry prop step tracking
    ghost var cp_old2 := limbs[2];
    ghost var cp_old3 := limbs[3];
    assert LimbToInt(cp_old2) == fold2_new2;
    assert LimbToInt(cp_old3) == old3_val;
    ghost var cp_c2_val: int := 0; // carry after j=2 step

    // Original code:
    // for j in U128::LIMBS .. U256::LIMBS {
    //   (limbs[j], carry) = add_with_bounded_overflow(limbs[j], carries[j], carry);
    // }
    for j:int := U128_LIMBS to U256_LIMBS
      invariant carry == ZeroLimb() || carry == LimbFromInt(1)
      invariant 0 <= carry.word && carry.word <= 1
      // Frame
      invariant LimbToInt(limbs[0]) == fold2_new0
      invariant LimbToInt(limbs[1]) == fold2_new1
      // j=2 entry state
      invariant j == 2 ==> carry == ZeroLimb()
      invariant j == 2 ==> limbs[2] == cp_old2
      invariant j == 2 ==> limbs[3] == cp_old3
      // j=3 entry: limbs[3] not yet written (only written during j=3 body)
      invariant j == 3 ==> limbs[3] == cp_old3
      invariant j >= 3 ==>
        LimbToInt(limbs[2]) + cp_c2_val * WORD_MODULUS
        == LimbToInt(cp_old2) + LimbToInt(carries[2])
      // carry == cp_c2_val at j=3 entry (carry out of j=2); after j=3 body carry is updated
      invariant j == 3 ==> LimbToInt(carry) == cp_c2_val
      invariant j >= 3 ==> cp_c2_val == 0 || cp_c2_val == 1
      // j=3 exit (j==4): carry chain step 2
      invariant j >= 4 ==>
        LimbToInt(limbs[3]) + LimbToInt(carry) * WORD_MODULUS
        == LimbToInt(cp_old3) + LimbToInt(carries[3]) + cp_c2_val
      modifies limbs
    {
      // GHOST CODE
      ghost var old_j := limbs[j];
      ghost var carry_in := carry;

      // Original code:
      //   (limbs[j], carry) = add_with_bounded_overflow(limbs[j], carries[j], carry);
      limbs[j], carry := add_with_bounded_overflow(limbs[j], carries[j], carry);

      // GHOST CODE
      assert carry == ZeroLimb() || carry == LimbFromInt(1);
      AddCarryAccountingLemma(old_j, carries[j], carry_in, limbs[j], carry);
      if j == 2 {
        // limbs[3] was not touched by j=2 step
        assert limbs[3] == cp_old3;
        cp_c2_val := LimbToInt(carry);
        assert LimbToInt(limbs[2]) + cp_c2_val * WORD_MODULUS
          == LimbToInt(cp_old2) + LimbToInt(carries[2]);
      } else {
        // carry_in == cp_c2_val from j==3 ==> LimbToInt(carry) == cp_c2_val invariant
        assert LimbToInt(carry_in) == cp_c2_val;
        assert LimbToInt(limbs[3]) + LimbToInt(carry) * WORD_MODULUS
          == LimbToInt(cp_old3) + LimbToInt(carries[3]) + cp_c2_val;
      }
    }

    // GHOST CODE
    // Telescope: CarryProp2Lemma combines the two carry chain equations
    CarryProp2Lemma(
      LimbToInt(cp_old2), LimbToInt(cp_old3),
      LimbToInt(carries[2]), LimbToInt(carries[3]),
      LimbToInt(limbs[2]), LimbToInt(limbs[3]),
      cp_c2_val, LimbToInt(carry));
    // Result: limbs[2]*W^2 + limbs[3]*W^3 + carry*W^4
    //   == (old2+carries[2])*W^2 + (old3+carries[3])*W^3
    // So: new0 + new1*W + limbs[2]*W^2 + limbs[3]*W^3 + carry*W^4 == mac_total_4
    assert LimbToInt(cp_old2) == fold2_new2;
    assert LimbToInt(cp_old3) == old3_val;
    assert LimbToInt(carries[2]) == fold2_c2;
    assert LimbToInt(carries[3]) == fold2_c3;

    // GHOST CODE: connect to mac_total_4
    // From j==4 invariant: limbs[2]*W^2 + limbs[3]*W^3 + carry*W^4
    //   == (fold2_new2+fold2_c2)*W^2 + (old3+fold2_c3)*W^3
    // Add fold2_new0 + fold2_new1*W to both sides:
    // LimbsValueSpec(limbs[0..4]) + carry*W^4 == mac_total_4

    ghost var before_256_reduction_limbs := limbs[..];
    ghost var pre_val := LimbsValueSpec(before_256_reduction_limbs[0..U256_LIMBS]);
    ghost var bit_carry := carry;
    ghost var old0 := before_256_reduction_limbs[0];
    ghost var old1 := before_256_reduction_limbs[1];
    ghost var old2 := before_256_reduction_limbs[2];
    ghost var old3 := before_256_reduction_limbs[3];
    // Bridge: old0..old3 and bit_carry to fold2 vars (for line asserting pre_val+bit_carry*W^4==mac_total_4)
    // These come from cp2 frame invariants + CarryProp2Lemma result, captured here while all are in scope.
    assert LimbToInt(old0) == fold2_new0;
    assert LimbToInt(old1) == fold2_new1;
    assert LimbToInt(old2) * WORD_MODULUS2 + LimbToInt(old3) * WORD_MODULUS3
      + LimbToInt(bit_carry) * WORD_MODULUS4
      == (fold2_new2 + fold2_c2) * WORD_MODULUS2 + (old3_val + fold2_c3) * WORD_MODULUS3;
    // Expand mac_total_4 = combine_lhs + old3_val*W^3 into distributed form
    Mac4ExpandLemma(mac_total_4, combine_lhs, old3_val,
      fold2_new0, fold2_new1, fold2_new2, fold2_c2, fold2_c3);
    assert mac_total_4 == fold2_new0 + fold2_new1 * WORD_MODULUS
      + (fold2_new2 + fold2_c2) * WORD_MODULUS2 + (old3_val + fold2_c3) * WORD_MODULUS3;
    // Direct sum: old0 + old1*W + old2*W^2 + old3*W^3 + bit_carry*W^4 == mac_total_4
    assert LimbToInt(old0) + LimbToInt(old1) * WORD_MODULUS
      + LimbToInt(old2) * WORD_MODULUS2 + LimbToInt(old3) * WORD_MODULUS3
      + LimbToInt(bit_carry) * WORD_MODULUS4 == mac_total_4;
    assert {:split_here} true;
    ghost var c0 := ZeroLimb();
    ghost var c1 := ZeroLimb();
    ghost var c2 := ZeroLimb();
    ghost var c3 := ZeroLimb();
    // Ghost snapshots of limb values after 256-bit correction (set in loop bodies)
    ghost var new0 := old0;
    ghost var new1 := old1;
    ghost var new2 := old2;
    ghost var new3 := old3;
    ghost var neg_bit_carry := wrapping_neg(bit_carry);
    WrappingNegOfBitLemma(bit_carry, neg_bit_carry);
    ghost var and0 := LimbAnd(neg_bit_carry, TWO_MODULUS_255_DISTANCE_as_limbs[0]);
    ghost var and1 := LimbAnd(neg_bit_carry, TWO_MODULUS_255_DISTANCE_as_limbs[1]);

    // Original code:
    // // As with the 384th bit, we now reduce out the 256th bit if set, which again won't overflow
    // let two_fifty_six_carry = carry.wrapping_neg();
    var two_fifty_six_carry := wrapping_neg(carry);

    // GHOST CODE
    assert bit_carry == ZeroLimb() || bit_carry == LimbFromInt(1);
    assert carry == bit_carry;
    WrappingNegOfBitLemma(carry, two_fifty_six_carry);
    assert neg_bit_carry == two_fifty_six_carry;
    assert {:split_here} true;
    assert {:isolate} and0 == LimbAnd(two_fifty_six_carry, TWO_MODULUS_255_DISTANCE_as_limbs[0]);
    assert {:isolate} and1 == LimbAnd(two_fifty_six_carry, TWO_MODULUS_255_DISTANCE_as_limbs[1]);

    // Original code:
    // let mut carry = Limb::ZERO;
    carry := ZeroLimb();

    // Original code:
    // for i in 0 .. U128::LIMBS {
    //   (limbs[i], carry) = add_with_bounded_overflow(
    //     limbs[i],
    //     two_fifty_six_carry & TWO_MODULUS_255_DISTANCE.as_limbs()[i],
    //     carry,
    //   );
    // }
    for i:int := 0 to U128_LIMBS
      invariant carry == ZeroLimb() || carry == LimbFromInt(1)
      invariant 0 <= carry.word && carry.word <= 1
      invariant i == 0 ==> carry == ZeroLimb()
      invariant i == 0 ==> limbs[0] == before_256_reduction_limbs[0] && limbs[1] == before_256_reduction_limbs[1]
      invariant i == 1 ==> limbs[1] == before_256_reduction_limbs[1]
      invariant i == 1 ==> carry == c0
      invariant i == 2 ==> carry == c1
      // Untouched limbs
      invariant limbs[2] == before_256_reduction_limbs[2]
      invariant limbs[3] == before_256_reduction_limbs[3]
      // Ghost snapshots: carry chain equations use ghost vars, not array
      invariant i >= 1 ==> limbs[0] == new0
      invariant i >= 1 ==> (LimbToInt(new0) + LimbToInt(c0) * WORD_MODULUS
        == LimbToInt(old0) + LimbToInt(and0))
      invariant i >= 1 ==> c0 == ZeroLimb() || c0 == LimbFromInt(1)
      invariant i >= 2 ==> limbs[1] == new1
      invariant i >= 2 ==> (LimbToInt(new1) + LimbToInt(c1) * WORD_MODULUS
        == LimbToInt(old1) + LimbToInt(and1) + LimbToInt(c0))
      invariant i >= 2 ==> (c1 == ZeroLimb() || c1 == LimbFromInt(1))
      modifies limbs
    {
      // GHOST CODE
      ghost var carry_in := carry;

      // Original code:
      //   (limbs[i], carry) = add_with_bounded_overflow(
      //     limbs[i],
      //     two_fifty_six_carry & TWO_MODULUS_255_DISTANCE.as_limbs()[i],
      //     carry,
      //   );
      var limbs_i := limbs[i];
      var addend := LimbAnd(two_fifty_six_carry, TWO_MODULUS_255_DISTANCE_as_limbs[i]);
      limbs[i], carry := add_with_bounded_overflow(limbs_i, addend, carry);

      // GHOST CODE
      assert carry == ZeroLimb() || carry == LimbFromInt(1);
      assert 0 <= carry.word && carry.word <= 1;
      if i == 0 {
        assert limbs_i == before_256_reduction_limbs[0];
        assert carry_in == ZeroLimb() || carry_in == LimbFromInt(1);
        assert (limbs[i], carry) == AddAndCarryLimbSpec(limbs_i, addend, carry_in);
        AddCarryAccountingLemma(limbs_i, addend, carry_in, limbs[i], carry);
        c0 := carry;
        new0 := limbs[0];
        assert addend == and0;
        assert limbs_i == old0;
        assert carry_in == ZeroLimb();
        // From AddCarryAccountingLemma:
        // LimbToInt(limbs[0]) + LimbToInt(carry)*W == limbs_i + addend + carry_in
        // i.e., new0 + c0*W == old0 + and0 + 0
        assert LimbToInt(new0) + LimbToInt(c0) * WORD_MODULUS
          == LimbToInt(limbs_i) + LimbToInt(addend) + LimbToInt(carry_in);
        assert LimbToInt(new0) + LimbToInt(c0) * WORD_MODULUS
          == LimbToInt(old0) + LimbToInt(and0);
      } else {
        assert limbs_i == before_256_reduction_limbs[1];
        assert carry_in == ZeroLimb() || carry_in == LimbFromInt(1);
        assert (limbs[i], carry) == AddAndCarryLimbSpec(limbs_i, addend, carry_in);
        AddCarryAccountingLemma(limbs_i, addend, carry_in, limbs[i], carry);
        c1 := carry;
        new1 := limbs[1];
        assert addend == and1;
        assert limbs_i == old1;
        assert carry_in == c0;
        // From AddCarryAccountingLemma:
        assert LimbToInt(new1) + LimbToInt(c1) * WORD_MODULUS
          == LimbToInt(limbs_i) + LimbToInt(addend) + LimbToInt(carry_in);
        assert LimbToInt(new1) + LimbToInt(c1) * WORD_MODULUS
          == LimbToInt(old1) + LimbToInt(and1) + LimbToInt(c0);
      }
    }

    // Original code:
    // for i in U128::LIMBS .. U256::LIMBS {
    //   let (limb, carry_bool) = limbs[i].0.overflowing_add(carry.0);
    //   (limbs[i], carry) = (Limb(limb), Limb(Word::from(carry_bool)));
    // }
    for i:int := U128_LIMBS to U256_LIMBS
      invariant carry == ZeroLimb() || carry == LimbFromInt(1)
      invariant 0 <= carry.word && carry.word <= 1
      invariant i == 2 ==> carry == c1
      invariant i == 3 ==> carry == c2
      // Frame: limbs[0..2] untouched by this loop (only writes limbs[2..4])
      invariant limbs[0] == new0
      invariant limbs[1] == new1
      // Untouched limbs within this loop
      invariant i <= 2 ==> limbs[2] == before_256_reduction_limbs[2]
      invariant i <= 3 ==> limbs[3] == before_256_reduction_limbs[3]
      // Ghost snapshot carry chain for this loop
      invariant i >= 3 ==> limbs[2] == new2
      invariant i >= 3 ==> (LimbToInt(new2) + LimbToInt(c2) * WORD_MODULUS
        == LimbToInt(old2) + LimbToInt(c1))
      invariant i >= 3 ==> c2 == ZeroLimb() || c2 == LimbFromInt(1)
      invariant i >= 4 ==> limbs[3] == new3
      invariant i >= 4 ==> (LimbToInt(new3) + LimbToInt(c3) * WORD_MODULUS
        == LimbToInt(old3) + LimbToInt(c2))
      invariant i >= 4 ==> (c3 == ZeroLimb() || c3 == LimbFromInt(1))
      invariant i >= 4 ==> carry == c3
      modifies limbs
    {
      // GHOST CODE
      ghost var carry_in := carry;

      // Original code:
      //   let (limb, carry_bool) = limbs[i].0.overflowing_add(carry.0);
      //   (limbs[i], carry) = (Limb(limb), Limb(Word::from(carry_bool)));
      var limbs_i := limbs[i];
      var pair := overflowing_add(limbs_i.word, carry.word);
      var limb := pair.0;
      var carry_bool := pair.1;
      limbs[i] := Limb(limb);
      carry := Limb(WordFromBool(carry_bool));

      // GHOST CODE
      assert carry == ZeroLimb() || carry == LimbFromInt(1);
      assert 0 <= carry.word && carry.word <= 1;
      OverflowingAddAccountingLemma(limbs_i.word, carry_in.word);
      // From OverflowingAddAccountingLemma:
      assert LimbToInt(limbs[i]) + LimbToInt(carry) * WORD_MODULUS
        == LimbToInt(limbs_i) + LimbToInt(carry_in);
      if i == U128_LIMBS {
        c2 := carry;
        new2 := limbs[2];
        assert limbs[2] == limbs[i];
        assert limbs_i == before_256_reduction_limbs[2];
        assert limbs_i == old2;
        assert carry_in == c1;
      } else {
        c3 := carry;
        new3 := limbs[3];
        assert limbs[3] == limbs[i];
        assert limbs_i == before_256_reduction_limbs[3];
        assert limbs_i == old3;
        assert carry_in == c2;
      }
    }

    // LEMMAS
    // After both loops: limbs[0..4] == new0..new3 (from invariants)
    assert limbs[0] == new0;
    assert limbs[1] == new1;
    assert limbs[2] == new2;
    assert limbs[3] == new3;
    assert carry == c3;
    assert two_fifty_six_carry == wrapping_neg(bit_carry);
    assert and0 == LimbAnd(two_fifty_six_carry, TWO_MODULUS_255_DISTANCE_as_limbs[0]);
    assert and1 == LimbAnd(two_fifty_six_carry, TWO_MODULUS_255_DISTANCE_as_limbs[1]);
    // pre_val == LimbsValueSpec([old0, old1, old2, old3])
    // Expand manually to avoid z3 timeout on fuel-9 + slicing
    assert pre_val == LimbsValueSpec(before_256_reduction_limbs[0..U256_LIMBS]);
    LimbsValueSpec4Lemma(old0, old1, old2, old3, before_256_reduction_limbs[0..U256_LIMBS]);
    assert LimbToInt(old0) + LimbToInt(old1) * WORD_MODULUS
      + LimbToInt(old2) * WORD_MODULUS2 + LimbToInt(old3) * WORD_MODULUS3
      == pre_val;

    // td[0] + td[1]*W = TwoModulus255DistanceSpec
    assert LimbToInt(TWO_MODULUS_255_DISTANCE_as_limbs[0])
      + LimbToInt(TWO_MODULUS_255_DISTANCE_as_limbs[1]) * WORD_MODULUS
      == TwoModulus255DistanceSpec() by {
      assert TWO_MODULUS_255_DISTANCE.ValueSpec() == TwoModulus255DistanceSpec();
    }
    // and0 + and1*W = bit_carry * TwoModulus255DistanceSpec()
    AndMaskTwoDistLemma(bit_carry, two_fifty_six_carry,
      TWO_MODULUS_255_DISTANCE_as_limbs[0], TWO_MODULUS_255_DISTANCE_as_limbs[1],
      and0, and1);

    ghost var total := pre_val + LimbToInt(bit_carry) * TwoModulus255DistanceSpec();

    // Bound: total < W^4 (needed for carry==0)
    // TODO: this requires a bound on pre_val from the MAC fold analysis
    // Connect pre_val + bit_carry * W^4 to mac_total_4
    // pre_val = LimbToInt(old0) + LimbToInt(old1)*W + LimbToInt(old2)*W^2 + LimbToInt(old3)*W^3 (line ~1122)
    // old0..old3 + bit_carry*W^4 == mac_total_4 (established near fold2 exit, repeated here for Z3)
    PreValCarryToMacTotalLemma(
      LimbToInt(old0), LimbToInt(old1), LimbToInt(old2), LimbToInt(old3),
      pre_val, LimbToInt(bit_carry), mac_total_4);
    assert pre_val + LimbToInt(bit_carry) * WORD_MODULUS4 == mac_total_4;
    Red512TotalBoundLemma(pre_val, LimbToInt(bit_carry), mac_total_4, p) by {
      assert 0 <= pre_val < WORD_MODULUS4 by {
        LimbsBoundLemma(before_256_reduction_limbs[0..U256_LIMBS]);
        assert pre_val < Power.Pow(WORD_MODULUS, 4);
        assert Power.Pow(WORD_MODULUS, 4) == WORD_MODULUS4 by {
          WordModulusPowLemma();
        }
      }
    }

    assert {:split_here} true;
    Red512Final256Lemma(
      limbs[..U256_LIMBS], before_256_reduction_limbs[..], bit_carry, carry,
      old0, old1, old2, old3,
      and0, and1, c0, c1, c2, c3, pre_val, total, p);

    // GHOST CODE
    ghost var final_low_limbs := limbs[..U256_LIMBS];
    ghost var final_low_val := LimbsValueSpec(final_low_limbs);

    // Original code:
    // let mut res = U256::ZERO;
    // res.as_limbs_mut().copy_from_slice(&limbs[.. U256::LIMBS]);
    var res_limbs := new Limb[U256_LIMBS][limbs[0], limbs[1], limbs[2], limbs[3]];
    var res := new U256(res_limbs);

    // GHOST CODE
    ghost var res_limbs_seq := res.limbs[..];
    assert res_limbs_seq == final_low_limbs;
    assert res.ValueSpec() == final_low_val;

    // Original code:
    // // Convert `res` to a valid scalar
    // red256(res)
    reduced:= red256(res);

    // GHOST CODE
    assert reduced.inner.ValueSpec() == res.ValueSpec() % p;
    assert reduced.inner.ValueSpec() == final_low_val % p;
    // From Red512Final256Lemma: LimbsValueSpec(limbs) % p == (pre_val + bit_carry * W^4) % p
    assert final_low_val % p
      == (pre_val + LimbToInt(bit_carry) * WORD_MODULUS4) % p;

    assert {:split_here} true;
    // The Crandall reduction preserves mod p (chain of 3 CrandallFoldModLemma calls).
    // Reminder assertions for Red512CrandallChainLemma preconditions (facts established earlier):
    assert {:isolate} fold1_effective == V - H1_val * (WORD_MODULUS4 - td);  // from fold1 definition
    assert {:isolate} before_second_val_int == fold1_effective
      - carry_384_int * WORD_MODULUS2 * (WORD_MODULUS4 - td);  // from correction
    assert {:isolate} mac_total_4 == before_second_val_int - b2 * (WORD_MODULUS4 - td);  // from fold2
    assert {:isolate} mac_total_4 % p == V % p by {
      Red512CrandallChainLemma(V, fold1_effective, H1_val, p, td,
        before_second_val_int, carry_384_int, mac_total_4, b2);
    }
    assert {:split_here} true;
    Red512FinalCongruenceLemma(
      reduced.inner.ValueSpec(),
      final_low_val,
      pre_val,
      LimbToInt(bit_carry),
      mac_total_4,
      V,
      p);
    assert reduced.inner.ValueSpec() == V % p;
  }

  // ===================================================================
  // LEMMAS used only by red512 chain
  // ===================================================================

  lemma Red512FinalCongruenceLemma(
    reduced_val: int,
    final_low_val: int,
    pre_val: int,
    bit_carry_val: int,
    mac_total_4: int,
    V: int,
    p: int)
    requires p > 0
    requires reduced_val == final_low_val % p
    requires final_low_val % p == (pre_val + bit_carry_val * WORD_MODULUS4) % p
    requires pre_val + bit_carry_val * WORD_MODULUS4 == mac_total_4
    requires mac_total_4 % p == V % p
    ensures reduced_val == V % p
  {
    assert (pre_val + bit_carry_val * WORD_MODULUS4) % p == mac_total_4 % p;
  }

  lemma PreValCarryToMacTotalLemma(
    old0: int, old1: int, old2: int, old3: int,
    pre_val: int, bit_carry_val: int, mac_total_4: int)
    requires pre_val
      == old0 + old1 * WORD_MODULUS + old2 * WORD_MODULUS2 + old3 * WORD_MODULUS3
    requires old0 + old1 * WORD_MODULUS + old2 * WORD_MODULUS2 + old3 * WORD_MODULUS3
      + bit_carry_val * WORD_MODULUS4 == mac_total_4
    ensures pre_val + bit_carry_val * WORD_MODULUS4 == mac_total_4
  {}

  lemma Carry384BoundLemma(
    value_after_cp1: int,
    carry_384_int: int,
    td: int,
    fold1_effective: int)
    requires 0 <= value_after_cp1 < WORD_MODULUS6
    requires carry_384_int == 0 || carry_384_int == 1
    requires 0 <= td < WORD_MODULUS2
    requires value_after_cp1 + carry_384_int * WORD_MODULUS6 == fold1_effective
    requires fold1_effective < 2 * WORD_MODULUS6 - td * WORD_MODULUS2
    ensures value_after_cp1 + carry_384_int * td * WORD_MODULUS2 < WORD_MODULUS6
  {
    if carry_384_int == 0 {
      assert value_after_cp1 + carry_384_int * td * WORD_MODULUS2 == value_after_cp1;
    } else {
      assert carry_384_int == 1;
      assert value_after_cp1 + WORD_MODULUS6 == fold1_effective;
      assert value_after_cp1 == fold1_effective - WORD_MODULUS6;
      assert value_after_cp1 < WORD_MODULUS6 - td * WORD_MODULUS2;
      assert value_after_cp1 + td * WORD_MODULUS2 < WORD_MODULUS6;
      assert value_after_cp1 + carry_384_int * td * WORD_MODULUS2
        == value_after_cp1 + td * WORD_MODULUS2;
    }
  }

  lemma ExitCarryAndBeforeSecondLemma(
    before_second_val_int: int,
    corr_exit: int,
    rhs_before_second: int)
    requires 0 <= before_second_val_int < WORD_MODULUS6
    requires 0 <= corr_exit
    requires before_second_val_int + corr_exit * WORD_MODULUS6 == rhs_before_second
    requires rhs_before_second < WORD_MODULUS6
    ensures corr_exit == 0
    ensures before_second_val_int == rhs_before_second
  {
    if corr_exit != 0 {
      assert corr_exit >= 1;
      assert corr_exit * WORD_MODULUS6 >= WORD_MODULUS6;
      assert before_second_val_int + corr_exit * WORD_MODULUS6 >= WORD_MODULUS6;
      assert rhs_before_second >= WORD_MODULUS6;
      assert false;
    }
  }

  // Telescopes two overlapping 2-limb MAC equations (at positions i, i+1)
  // when the second equation's input at position i+1 is the first equation's
  // output at position i+1. The intermediate value cancels, giving a total
  // change equation for positions i..i+3.
  //
  // Eq1 (shifted by W^shift): new2*S + mid3*S*W + c4*S*W^2 = orig2*S + orig3*S*W + h6*td*S
  // Eq2 (shifted by W^(shift+1)): new3*S*W + new4*S*W^2 + c5*S*W^3 = mid3*S*W + orig4*S*W^2 + h7*td*S*W
  // Adding: mid3 terms cancel.
  lemma MacFoldTelescopeLemma(
    new2: int, mid3: int, new3: int, new4: int,
    c4: int, c5: int,
    orig2: int, orig3: int, orig4: int,
    h6: int, h7: int, td: int,
    S: int  // shift factor (W^2 for first fold, W^0 for second fold)
  )
    // MAC eq 1 (at position i=2 or i=0)
    requires new2 + mid3 * WORD_MODULUS + c4 * WORD_MODULUS2
      == orig2 + orig3 * WORD_MODULUS + h6 * td
    // MAC eq 2 (at position i=3 or i=1)
    requires new3 + new4 * WORD_MODULUS + c5 * WORD_MODULUS2
      == mid3 + orig4 * WORD_MODULUS + h7 * td
    ensures
      (new2 + new3 * WORD_MODULUS + new4 * WORD_MODULUS2) * S
        + c4 * WORD_MODULUS2 * S + c5 * WORD_MODULUS3 * S
      == (orig2 + orig3 * WORD_MODULUS + orig4 * WORD_MODULUS2) * S
        + h6 * td * S + h7 * td * WORD_MODULUS * S
  {
    // From eq1: new2 + mid3*W = orig2 + orig3*W + h6*td - c4*W^2
    // From eq2: new3 + new4*W = mid3 + orig4*W + h7*td - c5*W^2
    // Multiply eq2 by W: new3*W + new4*W^2 = mid3*W + orig4*W^2 + h7*td*W - c5*W^3
    // Add eq1: new2 + mid3*W + new3*W + new4*W^2 = orig2 + orig3*W + h6*td + mid3*W + orig4*W^2 + h7*td*W - c4*W^2 - c5*W^3
    // Cancel mid3*W: new2 + new3*W + new4*W^2 = orig2 + orig3*W + orig4*W^2 + h6*td + h7*td*W - c4*W^2 - c5*W^3
    // Multiply by S: ...
  }

  // Shows that the imperative 2-MAC chain produces exactly the LimbsMacSpec result.
  // After: limbs[i], carry := mac(limbs[i], h, td[0], 0)
  //        limbs[i+1], carry := mac(limbs[i+1], h, td[1], carry)
  // The result [limbs[i], limbs[i+1], carry] == LimbsMacSpec([old_i, old_i1], h, td, 0)
  lemma MacImperativeMatchesSpec(
    old_i: Limb, old_i1: Limb, h: Limb, td0: Limb, td1: Limb,
    new_i: Limb, carry0: Limb, new_i1: Limb, carry1: Limb
  )
    requires (new_i, carry0) == mAddAndCarryLimbSpec(old_i, h, td0, ZeroLimb())
    // Precondition for the second mAddAndCarryLimbSpec call:
    // carry0 might not be 0 or 1, so we need LimbToInt(td1) < WORD_MODULUS - 1
    requires LimbToInt(td1) < WORD_MODULUS - 1
    requires (new_i1, carry1) == mAddAndCarryLimbSpec(old_i1, h, td1, carry0)
    ensures [new_i, new_i1, carry1] == LimbsMacSpec([old_i, old_i1], h, [td0, td1], ZeroLimb())
  {
    // LimbsMacSpec unfolds: step 0 with (old_i, h, td0, Zero), then recurse
    var macVal0 := LimbToInt(old_i) + LimbToInt(h) * LimbToInt(td0) + LimbToInt(ZeroLimb());
    MacStepBoundLemma(LimbToInt(old_i), LimbToInt(h), LimbToInt(td0), LimbToInt(ZeroLimb()));
    var low0 := LimbFromInt(macVal0 % WORD_MODULUS);
    var c0 := LimbFromInt(macVal0 / WORD_MODULUS);
    // From mAddAndCarryLimbSpec: new_i == low0, carry0 == c0
    assert new_i == low0;
    assert carry0 == c0;
    // Step 1: LimbsMacSpec([old_i1], h, [td1], carry0)
    var macVal1 := LimbToInt(old_i1) + LimbToInt(h) * LimbToInt(td1) + LimbToInt(carry0);
    MacStepBoundLemma(LimbToInt(old_i1), LimbToInt(h), LimbToInt(td1), LimbToInt(carry0));
    var low1 := LimbFromInt(macVal1 % WORD_MODULUS);
    var c1 := LimbFromInt(macVal1 / WORD_MODULUS);
    assert new_i1 == low1;
    assert carry1 == c1;
  }

  // Combines two overlapping MAC fold iterations for 8→6 reduction.
  // After folding limbs[6] into positions 2-3 and limbs[7] into positions 3-4,
  // the total value at positions 2-5 (with carries) equals orig 2-4 plus folded 6-7.
  // The intermediate mid3 value (limbs[3] between iterations) cancels.
  lemma MacFoldCombine6Lemma(
    old2v: int, old3v: int, old4v: int, old6v: int, old7v: int,
    new2v: int, mid3v: int, new3v: int, new4v: int,
    c4v: int, c5v: int,
    td: int
  )
    requires new2v + mid3v * WORD_MODULUS + c4v * WORD_MODULUS2
          == old2v + old3v * WORD_MODULUS + old6v * td
    requires new3v + new4v * WORD_MODULUS + c5v * WORD_MODULUS2
          == mid3v + old4v * WORD_MODULUS + old7v * td
    ensures new2v * WORD_MODULUS2 + new3v * WORD_MODULUS3
          + (new4v + c4v) * WORD_MODULUS4 + c5v * WORD_MODULUS5
         == old2v * WORD_MODULUS2 + old3v * WORD_MODULUS3 + old4v * WORD_MODULUS4
          + (old6v * WORD_MODULUS2 + old7v * WORD_MODULUS3) * td
  {
    assert (new2v + mid3v * WORD_MODULUS + c4v * WORD_MODULUS2) * WORD_MODULUS2
        == (old2v + old3v * WORD_MODULUS + old6v * td) * WORD_MODULUS2;
    assert (new3v + new4v * WORD_MODULUS + c5v * WORD_MODULUS2) * WORD_MODULUS3
        == (mid3v + old4v * WORD_MODULUS + old7v * td) * WORD_MODULUS3;
    assert WORD_MODULUS3 == WORD_MODULUS * WORD_MODULUS2;
    assert WORD_MODULUS4 == WORD_MODULUS * WORD_MODULUS3;
    assert WORD_MODULUS5 == WORD_MODULUS * WORD_MODULUS4;
  }

  // Combines two overlapping MAC fold iterations for 6→4 reduction.
  lemma MacFoldCombine4Lemma(
    old0v: int, old1v: int, old2v: int, old4v: int, old5v: int,
    new0v: int, mid1v: int, new1v: int, new2v: int,
    c2v: int, c3v: int,
    td: int
  )
    requires new0v + mid1v * WORD_MODULUS + c2v * WORD_MODULUS2
          == old0v + old1v * WORD_MODULUS + old4v * td
    requires new1v + new2v * WORD_MODULUS + c3v * WORD_MODULUS2
          == mid1v + old2v * WORD_MODULUS + old5v * td
    ensures new0v + new1v * WORD_MODULUS
          + (new2v + c2v) * WORD_MODULUS2 + c3v * WORD_MODULUS3
         == old0v + old1v * WORD_MODULUS + old2v * WORD_MODULUS2
          + (old4v + old5v * WORD_MODULUS) * td
  {
    assert (new0v + mid1v * WORD_MODULUS + c2v * WORD_MODULUS2) * 1
        == (old0v + old1v * WORD_MODULUS + old4v * td) * 1;
    assert (new1v + new2v * WORD_MODULUS + c3v * WORD_MODULUS2) * WORD_MODULUS
        == (mid1v + old2v * WORD_MODULUS + old5v * td) * WORD_MODULUS;
    assert WORD_MODULUS2 == WORD_MODULUS * WORD_MODULUS;
    assert WORD_MODULUS3 == WORD_MODULUS * WORD_MODULUS2;
  }

  // Telescopes a 2-step carry propagation chain.
  // Step 1: new2 + c2*W = old2 + carry2
  // Step 2: new3 + c3*W = old3 + carry3 + c2
  // Result: new2*W^2 + new3*W^3 + c3*W^4 = (old2+carry2)*W^2 + (old3+carry3)*W^3
  lemma CarryProp2Lemma(
    old2: int, old3: int, carry2: int, carry3: int,
    new2: int, new3: int, c2: int, c3: int
  )
    requires new2 + c2 * WORD_MODULUS == old2 + carry2
    requires new3 + c3 * WORD_MODULUS == old3 + carry3 + c2
    ensures new2 * WORD_MODULUS2 + new3 * WORD_MODULUS3 + c3 * WORD_MODULUS4
      == (old2 + carry2) * WORD_MODULUS2 + (old3 + carry3) * WORD_MODULUS3
  {
    // Multiply eq1 by W^2: new2*W^2 + c2*W^3 = (old2+carry2)*W^2
    // Multiply eq2 by W^3: new3*W^3 + c3*W^4 = (old3+carry3)*W^3 + c2*W^3
    // Add: new2*W^2 + c2*W^3 + new3*W^3 + c3*W^4 = (old2+carry2)*W^2 + (old3+carry3)*W^3 + c2*W^3
    // Cancel c2*W^3: new2*W^2 + new3*W^3 + c3*W^4 = (old2+carry2)*W^2 + (old3+carry3)*W^3
    assert WORD_MODULUS3 == WORD_MODULUS * WORD_MODULUS2;
    assert WORD_MODULUS4 == WORD_MODULUS * WORD_MODULUS3;
  }

  // Splits 8-limb value into 6 low + 2 high * W^4
  lemma {:fuel LimbsValueSpec, 9} Limbs8Split6Plus2Lemma(limbs: seq<Limb>)
    requires |limbs| == 8
    ensures LimbsValueSpec(limbs) == LimbsValueSpec(limbs[0..6])
      + (LimbToInt(limbs[6]) * WORD_MODULUS2 + LimbToInt(limbs[7]) * WORD_MODULUS3)
        * WORD_MODULUS4
  {
    assert WORD_MODULUS6 == WORD_MODULUS2 * WORD_MODULUS4;
    assert WORD_MODULUS7 == WORD_MODULUS3 * WORD_MODULUS4;
  }

  // Splits 6-limb value into 4 low + 2 high * W^4
  lemma {:fuel LimbsValueSpec, 7} Limbs6Split4Plus2Lemma(limbs: seq<Limb>)
    requires |limbs| == 6
    ensures LimbsValueSpec(limbs) == LimbsValueSpec(limbs[0..4])
      + (LimbToInt(limbs[4]) + LimbToInt(limbs[5]) * WORD_MODULUS) * WORD_MODULUS4
  {
    assert WORD_MODULUS4 == WORD_MODULUS4;
    assert WORD_MODULUS5 == WORD_MODULUS * WORD_MODULUS4;
  }

  // Expands LimbsValueSpec for a 4-element sequence into component form.
  lemma {:fuel LimbsValueSpec, 5} LimbsValueSpec4Lemma(
    a: Limb, b: Limb, c: Limb, d: Limb, s: seq<Limb>
  )
    requires s == [a, b, c, d]
    ensures LimbsValueSpec(s) == LimbToInt(a) + LimbToInt(b) * WORD_MODULUS
      + LimbToInt(c) * WORD_MODULUS2 + LimbToInt(d) * WORD_MODULUS3
  {
    assert s[1..] == [b, c, d];
    assert s[1..][1..] == [c, d];
    assert s[1..][1..][1..] == [d];
    assert s[1..][1..][1..][1..] == [];
  }

  // Expands LimbsValueSpec for a 6-element sequence into component form.
  lemma {:fuel LimbsValueSpec, 7} LimbsValueSpec6Lemma(
    a: Limb, b: Limb, c: Limb, d: Limb, e: Limb, f: Limb, s: seq<Limb>
  )
    requires s == [a, b, c, d, e, f]
    ensures LimbsValueSpec(s) == LimbToInt(a) + LimbToInt(b) * WORD_MODULUS
      + LimbToInt(c) * WORD_MODULUS2 + LimbToInt(d) * WORD_MODULUS3
      + LimbToInt(e) * WORD_MODULUS4 + LimbToInt(f) * WORD_MODULUS5
  {
    assert s[1..] == [b, c, d, e, f];
    assert s[1..][1..] == [c, d, e, f];
    assert s[1..][1..][1..] == [d, e, f];
    assert s[1..][1..][1..][1..] == [e, f];
    assert s[1..][1..][1..][1..][1..] == [f];
    assert s[1..][1..][1..][1..][1..][1..] == [];
  }

  // Bounds a 4-limb sum: a + b*W + c*W^2 + d*W^3 < W^4 when 0 <= a,b,c,d < W.
  lemma LimbsValueBound4Lemma(a: int, b: int, c: int, d: int)
    requires 0 <= a < WORD_MODULUS
    requires 0 <= b < WORD_MODULUS
    requires 0 <= c < WORD_MODULUS
    requires 0 <= d < WORD_MODULUS
    ensures 0 <= a + b * WORD_MODULUS + c * WORD_MODULUS2 + d * WORD_MODULUS3 < WORD_MODULUS4
  {
    assert a + b * WORD_MODULUS < WORD_MODULUS2;
    assert c * WORD_MODULUS2 < WORD_MODULUS3;
    assert d * WORD_MODULUS3 < WORD_MODULUS4;
  }

  // Bound: 6-limb value < WORD_MODULUS6
  lemma LimbsValueBound6Lemma(a: int, b: int, c: int, d: int, e: int, f: int)
    requires 0 <= a < WORD_MODULUS
    requires 0 <= b < WORD_MODULUS
    requires 0 <= c < WORD_MODULUS
    requires 0 <= d < WORD_MODULUS
    requires 0 <= e < WORD_MODULUS
    requires 0 <= f < WORD_MODULUS
    ensures 0 <= a + b * WORD_MODULUS + c * WORD_MODULUS2 + d * WORD_MODULUS3
      + e * WORD_MODULUS4 + f * WORD_MODULUS5 < WORD_MODULUS6
  {
    assert a + b * WORD_MODULUS < WORD_MODULUS2;
    assert c * WORD_MODULUS2 + d * WORD_MODULUS3 < WORD_MODULUS4;
    assert e * WORD_MODULUS4 + f * WORD_MODULUS5 < WORD_MODULUS6;
  }

  // Bound on mac_total for 6→4 fold. The MAC fold result fits with room for td.
  lemma MacTotalBound4Lemma(mac_total: int, low4: int, b: int)
    requires mac_total == low4 + b * TwoModulus255DistanceSpec()
    requires 0 <= low4 < WORD_MODULUS4
    requires 0 <= b < 2 * WORD_MODULUS2
    ensures 0 <= mac_total < 2 * WORD_MODULUS4 - TwoModulus255DistanceSpec()
  {
    ghost var td := TwoModulus255DistanceSpec();
    assert td < WORD_MODULUS2 / 2;
    assert b * td < WORD_MODULUS4;
    assert td * (2 * WORD_MODULUS2 + 1) < WORD_MODULUS4;
  }

  // Combines two chained MAC steps into a 2-limb MAC equation.
  // j=0: res0 + c0*W = a0 + h*d0
  // j=1: res1 + c1*W = a1 + h*d1 + c0
  // Combined: res0 + res1*W + c1*W^2 = a0 + a1*W + h*(d0 + d1*W)
  lemma MacChain2Lemma(
    res0: int, c0: int, a0: int, h: int, d0: int,
    res1: int, c1: int, a1: int, d1: int,
    c0_in: int, td: int)
    requires res0 + c0 * WORD_MODULUS == a0 + h * d0
    requires res1 + c1 * WORD_MODULUS == a1 + h * d1 + c0_in
    requires c0_in == c0
    requires td == d0 + d1 * WORD_MODULUS
    ensures res0 + res1 * WORD_MODULUS + c1 * WORD_MODULUS2
      == a0 + a1 * WORD_MODULUS + h * td
  {}

  // Bridge: at each Crandall fold step, replacing high*W^4 with high*td preserves mod p.
  // Formally: (L + H*td + carry_contrib) ≡ (L + H*W^4) (mod p) since W^4 ≡ td (mod p).
  // This is applied at each fold to show the final value ≡ V (mod p).
  //
  // Parameters capture the algebraic state before/after each fold:
  // V_before: value entering this fold step (limbs[0..8] effective value)
  // H: the "high" portion being folded (limbs[4+i] values)
  // The fold replaces H*W^4 with H*td, preserving mod p.
  lemma CrandallFoldModLemma(val_with_high: int, val_with_td: int, H: int, p: int)
    requires p == ModulusValueSpec()
    requires val_with_td == val_with_high - H * (WORD_MODULUS4 - TwoModulus255DistanceSpec())
    ensures val_with_td % p == val_with_high % p
  {
    // W^4 - td = 2p, so H*(W^4 - td) = 2*H*p
    CrandallRelationLemma();
    assert WORD_MODULUS4 - TwoModulus255DistanceSpec() == 2 * p;
    assert val_with_td == val_with_high - H * 2 * p;
    ModAddMultipleLemma(val_with_high, -2 * H, p);
  }

  // Proves: LimbAnd(wrapping_neg(bit_carry), td0) + LimbAnd(wrapping_neg(bit_carry), td1) * W
  // == LimbToInt(bit_carry) * TwoModulus255DistanceSpec()
  // When bit_carry == 0: both ANDs give 0.
  // When bit_carry == 1: wrapping_neg(1) == MAX, AND(MAX, x) == x.
  lemma AndMaskTwoDistLemma(
    bit_carry: Limb, neg_carry: Limb,
    td0: Limb, td1: Limb,
    and0: Limb, and1: Limb
  )
    requires bit_carry == ZeroLimb() || bit_carry == LimbFromInt(1)
    requires neg_carry == wrapping_neg(bit_carry)
    requires and0 == LimbAnd(neg_carry, td0)
    requires and1 == LimbAnd(neg_carry, td1)
    requires LimbToInt(td0) + LimbToInt(td1) * WORD_MODULUS
      == TwoModulus255DistanceSpec()
    ensures LimbToInt(and0) + LimbToInt(and1) * WORD_MODULUS
      == LimbToInt(bit_carry) * TwoModulus255DistanceSpec()
  {
    WrappingNegOfBitLemma(bit_carry, neg_carry);
    if bit_carry == ZeroLimb() {
      assert neg_carry == ZeroLimb();
      LimbAndZeroLemma(td0);
      LimbAndZeroLemma(td1);
      assert LimbToInt(and0) == 0;
      assert LimbToInt(and1) == 0;
    } else {
      assert neg_carry == MaxLimb();
      LimbAndMaxLemma(td0);
      LimbAndMaxLemma(td1);
      assert and0 == td0;
      assert and1 == td1;
    }
  }

  // AND with ZeroLimb gives zero
  lemma LimbAndZeroLemma(x: Limb)
    ensures LimbAnd(ZeroLimb(), x) == ZeroLimb()
  {}

  // AND with MaxLimb gives identity
  lemma LimbAndMaxLemma(x: Limb)
    ensures LimbAnd(MaxLimb(), x) == x
  {}

  // Upper bound on pre_val + bit_carry * d from the Crandall reduction.
  // The MAC fold operations guarantee the result fits in 4 limbs + 1 carry bit.
  // When the carry is set, adding d (which is ~2^128) still fits in 4 limbs
  // because the MAC folds guarantee pre_val < 2p ≈ 2^256 - 2*d, so
  // pre_val + d < 2p + d = W^4 - d < W^4.
  // The carry prop preserves the total: pre_val + bit_carry * W^4 == mac_total.
  // Since mac_total < 2*W^4 - td (from MacTotalBound4Lemma):
  // If bit_carry == 0: pre_val == mac_total < 2*W^4 - td < W^4 (since pre_val < W^4).
  //   So pre_val + 0 * td < W^4. ✓
  // If bit_carry == 1: pre_val == mac_total - W^4 < W^4 - td.
  //   So pre_val + td < W^4. ✓
  // Prove: pre_val + bit_carry * td < W^4.
  // Key input: mac_total (the value from the second MAC fold) satisfies
  //   pre_val + bit_carry * W^4 == mac_total < 2*W^4 - td.
  // The carry prop preserves the total, so this bound transfers.
  lemma Red512TotalBoundLemma(
    pre_val: int, bit_carry: int, mac_total: int, p: int
  )
    requires p == ModulusValueSpec()
    requires bit_carry == 0 || bit_carry == 1
    requires 0 <= pre_val < WORD_MODULUS4
    requires pre_val + bit_carry * WORD_MODULUS4 == mac_total
    requires 0 <= mac_total < 2 * WORD_MODULUS4 - TwoModulus255DistanceSpec()
    ensures pre_val + bit_carry * TwoModulus255DistanceSpec() < WORD_MODULUS4
  {
    ghost var td := TwoModulus255DistanceSpec();
    if bit_carry == 0 {
    } else {
      assert pre_val == mac_total - WORD_MODULUS4;
      assert pre_val < WORD_MODULUS4 - td;
    }
  }

  // Carry chain telescoping for the final 256-bit correction in red512.
  // Proves the 4-step addition chain (add td[0..2] + propagate carry) telescopes
  // correctly, preserves the modular value, and produces no final carry.
  lemma {:rlimit 202245} Red512Final256Lemma(
    limbs: seq<Limb>,
    before_256_reduction_limbs: seq<Limb>,
    bit_carry: Limb,
    carry: Limb,
    old0: Limb, old1: Limb, old2: Limb, old3: Limb,
    and0: Limb, and1: Limb,
    c0: Limb, c1: Limb, c2: Limb, c3: Limb,
    pre_val: int, total: int,
    p: int)
    requires |limbs| == 4
    requires |before_256_reduction_limbs| == 8
    requires p == ModulusValueSpec()
    requires bit_carry == ZeroLimb() || bit_carry == LimbFromInt(1)
    requires carry == ZeroLimb() || carry == LimbFromInt(1)
    // Carry chain equations (from AddCarryAccountingLemma / OverflowingAddAccountingLemma)
    requires LimbToInt(limbs[0]) + LimbToInt(c0) * WORD_MODULUS
      == LimbToInt(old0) + LimbToInt(and0)
    requires LimbToInt(limbs[1]) + LimbToInt(c1) * WORD_MODULUS
      == LimbToInt(old1) + LimbToInt(and1) + LimbToInt(c0)
    requires LimbToInt(limbs[2]) + LimbToInt(c2) * WORD_MODULUS
      == LimbToInt(old2) + LimbToInt(c1)
    requires LimbToInt(limbs[3]) + LimbToInt(c3) * WORD_MODULUS
      == LimbToInt(old3) + LimbToInt(c2)
    requires carry == c3
    // What total and pre_val are
    requires total == pre_val + LimbToInt(bit_carry) * TwoModulus255DistanceSpec()
    requires pre_val == LimbToInt(old0) + LimbToInt(old1) * WORD_MODULUS
      + LimbToInt(old2) * WORD_MODULUS2 + LimbToInt(old3) * WORD_MODULUS3
    // What and0, and1 are: the correction value when bit_carry is set
    requires LimbToInt(and0) + LimbToInt(and1) * WORD_MODULUS
      == LimbToInt(bit_carry) * TwoModulus255DistanceSpec()
    // Carry bounds
    requires c0 == ZeroLimb() || c0 == LimbFromInt(1)
    requires c1 == ZeroLimb() || c1 == LimbFromInt(1)
    requires c2 == ZeroLimb() || c2 == LimbFromInt(1)
    requires c3 == ZeroLimb() || c3 == LimbFromInt(1)
    // Value bound: the pre-reduction value + correction fits in 4 limbs
    // (follows from the Crandall reduction bounds in the Rust comments)
    requires pre_val + LimbToInt(bit_carry) * TwoModulus255DistanceSpec() < WORD_MODULUS4
    ensures LimbsValueSpec(limbs) + LimbToInt(carry) * WORD_MODULUS4 == total
    ensures LimbsValueSpec(limbs) % p
      == (pre_val + LimbToInt(bit_carry) * WORD_MODULUS4) % p
    ensures LimbToInt(carry) == 0
  {
    // Telescoping: sum up the carry chain
    // limbs[0] = old0 + and0 - c0*W
    // limbs[1] = old1 + and1 + c0 - c1*W
    // limbs[2] = old2 + c1 - c2*W
    // limbs[3] = old3 + c2 - c3*W
    //
    // LimbsValueSpec(limbs) = limbs[0] + limbs[1]*W + limbs[2]*W^2 + limbs[3]*W^3
    //   = (old0+and0-c0*W) + (old1+and1+c0-c1*W)*W + (old2+c1-c2*W)*W^2 + (old3+c2-c3*W)*W^3
    //   = old0+and0 + old1*W+and1*W+c0*W-c0*W + old2*W^2+c1*W^2-c1*W^2 + old3*W^3+c2*W^3-c2*W^3 - c3*W^4
    //   = pre_val + (and0 + and1*W) - c3*W^4
    //   = pre_val + bit_carry*TwoModulus255DistanceSpec() - c3*W^4
    //   = total - c3*W^4

    // First prove the telescoping
    ghost var v0 := LimbToInt(limbs[0]);
    ghost var v1 := LimbToInt(limbs[1]);
    ghost var v2 := LimbToInt(limbs[2]);
    ghost var v3 := LimbToInt(limbs[3]);
    ghost var sum := v0 + v1 * WORD_MODULUS + v2 * WORD_MODULUS2 + v3 * WORD_MODULUS3;
    ghost var cc0 := LimbToInt(c0);
    ghost var cc1 := LimbToInt(c1);
    ghost var cc2 := LimbToInt(c2);
    ghost var cc3 := LimbToInt(c3);

    // From carry chain: substitute
    assert v0 == LimbToInt(old0) + LimbToInt(and0) - cc0 * WORD_MODULUS;
    assert v1 == LimbToInt(old1) + LimbToInt(and1) + cc0 - cc1 * WORD_MODULUS;
    assert v2 == LimbToInt(old2) + cc1 - cc2 * WORD_MODULUS;
    assert v3 == LimbToInt(old3) + cc2 - cc3 * WORD_MODULUS;

    // Telescope
    assert sum == pre_val + LimbToInt(and0) + LimbToInt(and1) * WORD_MODULUS
      - cc3 * WORD_MODULUS * WORD_MODULUS3;
    assert WORD_MODULUS * WORD_MODULUS3 == WORD_MODULUS4;
    assert sum == total - cc3 * WORD_MODULUS4;
    assert sum + cc3 * WORD_MODULUS4 == total;

    // LimbsValueSpec matches sum (by fuel or manual expansion)
    assert LimbsValueSpec(limbs) == sum by {
      assert limbs[1..] == [limbs[1], limbs[2], limbs[3]];
      assert limbs[1..][1..] == [limbs[2], limbs[3]];
      assert limbs[1..][1..][1..] == [limbs[3]];
      assert limbs[1..][1..][1..][1..] == [];
    }

    // Ensures 1: sum + c3*W^4 == total
    assert LimbsValueSpec(limbs) + LimbToInt(carry) * WORD_MODULUS4 == total;

    // Ensures 3: carry == 0
    // sum = total - c3*W^4. sum >= 0 (it's a sum of limb values with bounded carries).
    // total = pre_val + bit_carry * d < W^4 (from precondition).
    // If c3 == 1: sum = total - W^4 < 0. But sum >= 0 from LimbsValueSpec. Contradiction.
    assert sum >= 0 by {
      assert v0 >= 0;
      assert v1 >= 0;
      assert v2 >= 0;
      assert v3 >= 0;
    }
    assert total < WORD_MODULUS4;
    if cc3 == 1 {
      assert sum == total - WORD_MODULUS4 < 0;
      assert false;
    }
    assert cc3 == 0;
    assert LimbToInt(carry) == 0;

    // Ensures 2: LimbsValueSpec(limbs) % p == pre_val % p
    // sum = total = pre_val + bit_carry * d
    // sum % p = (pre_val + bit_carry * d) % p
    // We need: (pre_val + bit_carry * d) % p == pre_val % p
    // i.e., bit_carry * d ≡ 0 (mod p)
    // When bit_carry == 0: trivially true
    // When bit_carry == 1: d ≡ 0 (mod p)? No! d = TwoModulus255Distance ≈ 2^128 < p.
    // But W^4 = 2p + d, so d ≡ W^4 (mod p) ≡ -2p ≡ 0... no wait.
    // W^4 = 2p + d, so d = W^4 - 2p. d mod p = (W^4 - 2p) mod p = W^4 mod p.
    // W^4 = 2p + d. So W^4 mod p = d mod p (since 2p mod p = 0).
    // And d < p (since d ≈ 2^128 < 2^255 ≈ p). So d mod p = d ≠ 0.
    //
    // Actually, the ensures should be sum % p == (pre_val + bit_carry * W^4) % p,
    // because the original value before the 256-bit reduction is pre_val + bit_carry * W^4
    // (the carry represents the 256th bit being set). The Crandall trick is:
    // pre_val + bit_carry * W^4 ≡ pre_val + bit_carry * d (mod p) since W^4 ≡ d (mod p).
    // And sum = pre_val + bit_carry * d, so sum ≡ pre_val + bit_carry * W^4 (mod p).
    //
    // So ensures 2 should really be:
    // LimbsValueSpec(limbs) % p == (pre_val + LimbToInt(bit_carry) * WORD_MODULUS4) % p
    //
    // But the existing ensures says: LimbsValueSpec(limbs) % p == pre_val % p
    // These are equal iff bit_carry * W^4 ≡ 0 (mod p), i.e. always since W^4 = 2p + d
    // and we need bit_carry * W^4 % p = bit_carry * d % p.
    // So: pre_val + bit_carry * W^4 ≡ pre_val + bit_carry * d ≡ sum (mod p). But
    // sum % p = (pre_val + bit_carry * d) % p ≠ pre_val % p in general.
    //
    // UNLESS "pre_val" at the call site INCLUDES the bit_carry * W^4 contribution,
    // meaning pre_val represents the FULL value (including bit_carry) rather than just
    // the low limbs. Let me re-check... No, pre_val = LimbsValueSpec(before[0..4]),
    // which is just the low 4 limbs.
    //
    // The ensures 2 is used at the call site to show: final_low_val % p == pre_val % p.
    // Then PreValModBridgeLemma shows: pre_val % p == V % p.
    // So the chain is: sum % p == pre_val % p == V % p.
    // But sum = pre_val + bit_carry * d, so sum ≡ pre_val + bit_carry * d (mod p).
    // For sum ≡ pre_val (mod p), we need d ≡ 0 (mod p), which is false.
    //
    // CONCLUSION: ensures 2 as stated is WRONG when bit_carry == 1.
    // The fix: PreValModBridgeLemma should provide
    //   (pre_val + bit_carry * WORD_MODULUS4) % p == V % p
    // instead of pre_val % p == V % p. Then we need:
    //   sum % p == (pre_val + bit_carry * WORD_MODULUS4) % p
    // which IS true since sum ≡ pre_val + bit_carry * d ≡ pre_val + bit_carry * W^4 (mod p).

    CrandallRelationLemma();
    // 2p + d = W^4, so W^4 ≡ d (mod p)
    // sum = pre_val + bit_carry * d
    // pre_val + bit_carry * W^4 = pre_val + bit_carry * (2p + d) = (pre_val + bit_carry * d) + 2p * bit_carry
    //   = sum + 2p * bit_carry
    // So (pre_val + bit_carry * W^4) % p = (sum + 2p*bit_carry) % p = sum % p
    ModAddMultipleLemma(sum, 2 * LimbToInt(bit_carry), p);
    assert sum % p == (pre_val + LimbToInt(bit_carry) * WORD_MODULUS4) % p;

    // The above proves sum % p == (pre_val + bit_carry*W^4) % p, not sum % p == pre_val % p.
    // For ensures 2 to hold, we need pre_val % p == (pre_val + bit_carry*W^4) % p,
    // which requires bit_carry*W^4 ≡ 0 (mod p). W^4 = 2p + d, so bit_carry*W^4 = 2p*bit_carry + d*bit_carry.
    // 2p*bit_carry ≡ 0 (mod p). So bit_carry*W^4 ≡ d*bit_carry (mod p).
    // Need d*bit_carry ≡ 0 (mod p). d ≈ 2^128 < p. If bit_carry==0: trivial. If bit_carry==1: need d ≡ 0 (mod p). False!
    // ...so ensures 2 cannot be proved as-is. See comment above.
    // We prove the CORRECT modular relation instead, to be used at the call site.
    assert LimbsValueSpec(limbs) % p == (pre_val + LimbToInt(bit_carry) * WORD_MODULUS4) % p;
  }

  // OverflowingAddAccountingLemma: overflow add preserves total value.
  lemma OverflowingAddAccountingLemma(a: Word, b: Word)
    ensures LimbToInt(Limb(overflowing_add(a, b).0))
      + LimbToInt(Limb(WordFromBool(overflowing_add(a, b).1))) * WORD_MODULUS
      == a as int + b as int
  {
    var pair := overflowing_add(a, b);
    assert pair.0 as int + (if pair.1 then 1 else 0) * WORD_MODULUS == a as int + b as int;
    assert LimbToInt(Limb(WordFromBool(pair.1))) == (if pair.1 then 1 else 0);
  }

  // Wide512LimbsValueConnectLemma: LimbsValueSpec(lo ++ hi) == lo_val + hi_val * W^4
  // This connects the 8-limb concatenation to Wide512ValueSpec.
  lemma {:fuel LimbsValueSpec, 9} Wide512LimbsValueConnectLemma(lo: seq<Limb>, hi: seq<Limb>)
    requires |lo| == 4 && |hi| == 4
    ensures LimbsValueSpec(lo + hi) == LimbsValueSpec(lo) + LimbsValueSpec(hi) * WORD_MODULUS4
  {
    var joined := lo + hi;
    // Use the backward spec which decomposes as last-limb + rest * WORD_MODULUS^(n-1)
    // Since LimbsValueSpec has fuel 9, z3 can unroll the 8-element sequence.
    // We help z3 by asserting the sequence relationships:
    assert joined[..4] == lo;
    assert joined[4..] == hi;
    assert joined[1..] == lo[1..] + hi;
    assert (lo + hi)[1..] == lo[1..] + hi;
    // With fuel 9, z3 should be able to expand both sides.
  }

  // Bounds fold1_effective: orig_low6 + H1*td < 2*W^6 - td*W^2
  // Used to prove exit_carry==0 after the 384-bit correction.
  // Key: H1_val = h6*W^2 + h7*W^3 <= W^4 - W^2; td <= W^2 - 1
  // So H1*td <= (W^4-W^2)*(W^2-1) = W^6 - 2*W^4 + W^2 < W^6 - td*W^2
  lemma Fold1EffectiveBoundLemma(h6: int, h7: int, orig_low6: int, td: int, fold1_eff: int)
    requires 0 <= h6 < WORD_MODULUS
    requires 0 <= h7 < WORD_MODULUS
    requires 0 <= orig_low6 < WORD_MODULUS6
    requires 0 <= td < WORD_MODULUS2
    requires fold1_eff == orig_low6 + (h6 * WORD_MODULUS2 + h7 * WORD_MODULUS3) * td
    ensures fold1_eff < 2 * WORD_MODULUS6 - td * WORD_MODULUS2
  {
    assert h6 * WORD_MODULUS2 + h7 * WORD_MODULUS3 <= WORD_MODULUS4 - WORD_MODULUS2;
    assert (WORD_MODULUS4 - WORD_MODULUS2) * (WORD_MODULUS2 - 1)
      == WORD_MODULUS6 - 2 * WORD_MODULUS4 + WORD_MODULUS2;
  }

  // Connects the two 384-bit correction loops' arithmetic to a total value equation.
  // Loop 1 adds carry_384*td to positions 2,3 (with internal carry c23).
  // Loop 2 propagates c23 through positions 4,5 (with carry out exit_carry).
  // Combined: the total of positions 2-5 + exit_carry*W^6 equals original + carry_384*td*W^2.
  lemma CorrectionPreservesTotalLemma(
    L2: int, L3: int, L4: int, L5: int,
    new2: int, new3: int, c23: int,
    new4: int, c24: int, new5: int, exit_carry: int,
    carry_384: int, td: int)
    requires new2 + new3 * WORD_MODULUS + c23 * WORD_MODULUS2 == L2 + L3 * WORD_MODULUS + carry_384 * td
    requires new4 + c24 * WORD_MODULUS == L4 + c23
    requires new5 + exit_carry * WORD_MODULUS == L5 + c24
    ensures new2 * WORD_MODULUS2 + new3 * WORD_MODULUS3
      + new4 * WORD_MODULUS4 + new5 * WORD_MODULUS5 + exit_carry * WORD_MODULUS6
      == L2 * WORD_MODULUS2 + L3 * WORD_MODULUS3 + L4 * WORD_MODULUS4 + L5 * WORD_MODULUS5
        + carry_384 * td * WORD_MODULUS2
  {
    assert WORD_MODULUS3 == WORD_MODULUS * WORD_MODULUS2;
    assert WORD_MODULUS4 == WORD_MODULUS * WORD_MODULUS3;
    assert WORD_MODULUS5 == WORD_MODULUS * WORD_MODULUS4;
    assert WORD_MODULUS6 == WORD_MODULUS * WORD_MODULUS5;
  }

  // Carry propagation at positions 4,5 preserves the "column total" (pos 4-5 + overflow).
  // Used to connect after_fold1 limbs + carries to the 6-limb value after carry prop 1.
  lemma CarryProp45TotalLemma(
    old4: int, old5: int, carry4: int, carry5: int,
    new4: int, c4out: int, new5: int, carry_384: int)
    requires new4 + c4out * WORD_MODULUS == old4 + carry4
    requires new5 + carry_384 * WORD_MODULUS == old5 + carry5 + c4out
    ensures new4 * WORD_MODULUS4 + new5 * WORD_MODULUS5 + carry_384 * WORD_MODULUS6
      == (old4 + carry4) * WORD_MODULUS4 + (old5 + carry5) * WORD_MODULUS5
  {
    assert WORD_MODULUS5 == WORD_MODULUS * WORD_MODULUS4;
    assert WORD_MODULUS6 == WORD_MODULUS * WORD_MODULUS5;
  }

  // Connects the after_fold1 total equation and CarryProp45 result to prove that
  // LimbsValueSpec(limbs[0..6]) + carry_384*W^6 == fold1_effective,
  // where limbs[0..3] == after_fold1_limbs[0..3] (frame), limbs[4..5] are updated.
  lemma ValueAfterCP1Lemma(
    L0: int, L1: int, L2: int, L3: int, L4: int, L5: int,
    c4: int, c5: int,
    new4: int, new5: int, carry_384: int,
    fold1_effective: int)
    // fold1 total: LimbsValueSpec6(L0..L5) + c4*W^4 + c5*W^5 == fold1_effective
    requires L0 + L1 * WORD_MODULUS + L2 * WORD_MODULUS2 + L3 * WORD_MODULUS3
      + L4 * WORD_MODULUS4 + L5 * WORD_MODULUS5
      + c4 * WORD_MODULUS4 + c5 * WORD_MODULUS5 == fold1_effective
    // CarryProp45: new4*W^4 + new5*W^5 + carry_384*W^6 == (L4+c4)*W^4 + (L5+c5)*W^5
    requires new4 * WORD_MODULUS4 + new5 * WORD_MODULUS5 + carry_384 * WORD_MODULUS6
      == (L4 + c4) * WORD_MODULUS4 + (L5 + c5) * WORD_MODULUS5
    ensures L0 + L1 * WORD_MODULUS + L2 * WORD_MODULUS2 + L3 * WORD_MODULUS3
      + new4 * WORD_MODULUS4 + new5 * WORD_MODULUS5 + carry_384 * WORD_MODULUS6 == fold1_effective
  {
    // Substitute (L4+c4)*W^4 + (L5+c5)*W^5 = new4*W^4 + new5*W^5 + carry_384*W^6 into fold1 equation.
  }

  // Bridges CorrectionPreservesTotalLemma + LimbsValueSpec6 expansions to the overall equation:
  // before_second_val + exit_carry*W^6 == value_after_cp1 + carry_384*td*W^2
  lemma CorrectionTotalBridgeLemma(
    L0: int, L1: int, L2: int, L3: int, L4: int, L5: int,
    new2: int, new3: int, new4: int, new5: int,
    c23: int, c24: int, exit_carry: int,
    carry_384: int, td: int,
    value_after_cp1: int, before_second_val: int)
    // CorrectionPreservesTotalLemma preconditions
    requires new2 + new3 * WORD_MODULUS + c23 * WORD_MODULUS2 == L2 + L3 * WORD_MODULUS + carry_384 * td
    requires new4 + c24 * WORD_MODULUS == L4 + c23
    requires new5 + exit_carry * WORD_MODULUS == L5 + c24
    // LimbsValueSpec6 expansion for value_after_cp1
    requires value_after_cp1 == L0 + L1 * WORD_MODULUS + L2 * WORD_MODULUS2
      + L3 * WORD_MODULUS3 + L4 * WORD_MODULUS4 + L5 * WORD_MODULUS5
    // LimbsValueSpec6 expansion for before_second_val
    requires before_second_val == L0 + L1 * WORD_MODULUS + new2 * WORD_MODULUS2
      + new3 * WORD_MODULUS3 + new4 * WORD_MODULUS4 + new5 * WORD_MODULUS5
    ensures before_second_val + exit_carry * WORD_MODULUS6
      == value_after_cp1 + carry_384 * td * WORD_MODULUS2
  {
    CorrectionPreservesTotalLemma(L2, L3, L4, L5, new2, new3, c23, new4, c24, new5, exit_carry, carry_384, td);
    assert WORD_MODULUS3 == WORD_MODULUS * WORD_MODULUS2;
    assert WORD_MODULUS4 == WORD_MODULUS * WORD_MODULUS3;
    assert WORD_MODULUS5 == WORD_MODULUS * WORD_MODULUS4;
    assert WORD_MODULUS6 == WORD_MODULUS * WORD_MODULUS5;
  }

  // Master mod-p chain: three Crandall fold steps, each subtracting a multiple of 2p.
  // fold1: V → fold1_effective (subtract H1 * 2p)
  // correction: fold1_effective → before_second_val (subtract carry_384*W^2 * 2p)
  // fold2: before_second_val → mac_total_4 (subtract b2 * 2p)
  lemma Red512CrandallChainLemma(
    V: int, fold1_effective: int, H1_val: int, p: int, td: int,
    before_second_val: int, carry_384_int: int,
    mac_total_4: int, b2: int)
    requires p == ModulusValueSpec()
    requires td == TwoModulus255DistanceSpec()
    requires fold1_effective == V - H1_val * (WORD_MODULUS4 - td)
    requires before_second_val == fold1_effective - carry_384_int * WORD_MODULUS2 * (WORD_MODULUS4 - td)
    requires mac_total_4 == before_second_val - b2 * (WORD_MODULUS4 - td)
    ensures mac_total_4 % p == V % p
  {
    CrandallFoldModLemma(V, fold1_effective, H1_val, p);
    CrandallFoldModLemma(fold1_effective, before_second_val, carry_384_int * WORD_MODULUS2, p);
    CrandallFoldModLemma(before_second_val, mac_total_4, b2, p);
  }

  // fold1_effective = orig_low + H1*td = (orig_low + H1*W^4) - H1*(W^4-td) = V - H1*(W^4-td)
  lemma Fold1EffectiveEquivLemma(fold1_eff: int, V: int, H1: int, td_val: int, orig_low: int)
    requires fold1_eff == orig_low + H1 * td_val
    requires V == orig_low + H1 * WORD_MODULUS4
    ensures fold1_eff == V - H1 * (WORD_MODULUS4 - td_val)
  {}

  // before_second_val + corr_exit*W^6 == value_cp1 + carry_384*td*W^2
  //   and value_cp1 + carry_384*W^6 == fold1_eff
  //   and W^6 == W^2 * W^4
  // → before_second_val + corr_exit*W^6 == fold1_eff - carry_384*W^2*(W^4-td)
  lemma BeforeSecondValBridgeLemma(
    before_second: int, corr_exit: int, fold1_eff: int,
    carry_384: int, td_val: int, value_cp1: int)
    requires before_second + corr_exit * WORD_MODULUS6
      == value_cp1 + carry_384 * td_val * WORD_MODULUS2
    requires value_cp1 + carry_384 * WORD_MODULUS6 == fold1_eff
    requires WORD_MODULUS6 == WORD_MODULUS2 * WORD_MODULUS4
    ensures before_second + corr_exit * WORD_MODULUS6
      == fold1_eff - carry_384 * WORD_MODULUS2 * (WORD_MODULUS4 - td_val)
  {}

  // mac_total = low4 + b*td = (low4 + b*W^4) - b*(W^4-td) = before_second_val - b*(W^4-td)
  lemma MacTotalEquivLemma(mac: int, before: int, low4: int, b: int, td_val: int)
    requires mac == low4 + b * td_val
    requires before == low4 + b * WORD_MODULUS4
    ensures mac == before - b * (WORD_MODULUS4 - td_val)
  {}

  lemma CarryIntOneWordModulus6Lemma(value_after_cp1: int, fold1_effective: int, carry_384_int: int)
    requires carry_384_int == 1
    requires value_after_cp1 + carry_384_int * WORD_MODULUS6 == fold1_effective
    ensures value_after_cp1 + WORD_MODULUS6 == fold1_effective
  {}

  // Expands mac_total_4 = combine + old3*W^3 where combine = n0+n1*W+(n2+c2)*W^2+c3*W^3
  // into the fully distributed form: n0 + n1*W + (n2+c2)*W^2 + (old3+c3)*W^3
  lemma Mac4ExpandLemma(
    mac: int, combine: int, old3: int,
    n0: int, n1: int, n2: int, c2: int, c3: int)
    requires mac == combine + old3 * WORD_MODULUS3
    requires combine == n0 + n1 * WORD_MODULUS
      + (n2 + c2) * WORD_MODULUS2 + c3 * WORD_MODULUS3
    ensures mac == n0 + n1 * WORD_MODULUS
      + (n2 + c2) * WORD_MODULUS2 + (old3 + c3) * WORD_MODULUS3
  {
    assert WORD_MODULUS3 == WORD_MODULUS * WORD_MODULUS2;
  }
}
