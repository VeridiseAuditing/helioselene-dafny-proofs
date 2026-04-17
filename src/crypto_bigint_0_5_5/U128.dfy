include "Limb.dfy"
include "../helpers/Limbs.dfy"

module CryptoBigint_0_5_5_U128 {
  import opened CryptoBigint_0_5_5_Limb
  import opened Limbs

  const U128_LIMBS: int := 2

  class U128 {
    var limbs: array<Limb>

    ghost predicate Valid() reads this {
      limbs.Length == U128_LIMBS
    }

    //////////////////////
    // HELPER FUNCTIONS //
    //////////////////////

    constructor(limbs: array<Limb>)
      requires limbs.Length == U128_LIMBS
      ensures this.limbs == limbs
      ensures Valid()
    {
      this.limbs := limbs;
    }

    method {:rlimit 20} AsLimbs() returns (limbs: array<Limb>)
    {
      limbs := this.limbs;
    }

    //////////////////////
    // PORTED FUNCTIONS //
    //////////////////////

    // Ported from https://github.com/RustCrypto/crypto-bigint/blob/395bb171178990a93ef571664271dabc50749043/src/uint.rs#L156-159
    method {:rlimit 27} as_limbs() returns (limbs: array<Limb>)
      requires this.Valid()
      ensures limbs == this.limbs
    {
      // Original Code:
      // &self.limbs
      limbs := this.limbs;
    }

    ////////////
    // SPECS  //
    ////////////

    ghost function {:rlimit 271} ValueSpec(): int
    reads this
    reads this.limbs
    requires this.Valid()
    ensures 0 <= this.ValueSpec() < WORD_MODULUS2
    {
      LimbsValueSpec(this.limbs[..])
    }

    ////////////
    // LEMMAS //
    ////////////
  }
}
