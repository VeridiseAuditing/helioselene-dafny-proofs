# Helioselene Dafny

This directory contains Dafny encodings of selected routines from the Helioselene field
and point implementations in monero-oxide, along with functional correctness proofs.

Source reference:
- Repository: https://github.com/monero-oxide/monero-oxide/tree/fcmp++/crypto/helioselene
- Commit: 27b1c7f2918444560c7383e7a5fbddb481dbf2d2

## Verification targets

The following functions are the predetermined verification targets for this audit.

### field.rs

| Function | Ported | Verified | Limitations? |
| --- | --- | --- | --- |
| `red256` | ✅ | ✅ | No |
| `red512` | ✅ | ✅ | No |
| `pow` | ✅ | ✅ | See below |
| `invert` (field_invert, extended binary GCD) | ✅ | ❌✅ | See below |
| `sqrt` (field_sqrt) | ✅ | ✅ | See below |

### point.rs

| Function | Ported | Verified |
| --- | --- | --- |
| `add` (point_add) | Yes | No |
| `double` (point_double) | Yes | No |
| `mul` (point_scalar_mul) | Yes | No |
| `from_bytes` (point_from_bytes) | Yes | No |
| `to_bytes` (point_to_bytes) | Yes | No |

### Limitations

#### `pow()`

1. The initial table pre-computation is computed in a helper function to ease the verification effort.
1. `table[0]` is reused for the Helioselene `ONE` element
1. The `conditional_select()` is replaced with an explicit if statement
1. The `to_le_bits()` is modeled by just directly extracting bits within the loop.

#### `invert()`

> **Upstream bug found during porting.** The Rust `invert()` at commit `27b1c7f` does
> not return a true modular inverse for all nonzero field elements — for example,
> it fails for `y = 3 · 2^66`. The Dafny port replaces the faulty partial-width
> inner loops with a **full-width** variant of the extended binary GCD, and this
> full-width variant is mechanically verified. The `❌✅` in the *Verified* column
> reflects this split: `❌` for the upstream Rust implementation (incorrect on a
> class of inputs), `✅` for the mathematically equivalent full-width Dafny port.
> See [Upstream `invert()` bug](#upstream-invert-bug) below for the reproducer.

**Divergences from the Rust source.**

1. The Rust `CtOption` struct is modeled as a tuple: `(true, value)` corresponds to `Some(value)`, and `(false, value)` corresponds to `None`.
1. The outer range `for limbs in (2 ..= U256::LIMBS).rev()` is encoded as `while limbs >= 2 { ... limbs := limbs - 1; }` and unrolled in the Dafny port; semantics are identical.
1. **Partial-width vs. full-width `a`/`b` inner loops.** Rust's `step()` uses `for l in 0 .. limbs` for the `a - b` subtract chain, the conditional-negate chain, the two `select`s, and the final right-shift, where `limbs` shrinks as the high limbs of `a` and `b` are expected to be zero. The Dafny port uses full-width loops (`0 .. U256::LIMBS`) for all of these. The full-width variant computes the extended binary GCD correctly and agrees with Rust on all inputs for which Rust itself returns a true modular inverse. The class of inputs on which the two disagree — and on which the Rust implementation is incorrect — is characterised in [Upstream `invert()` bug](#upstream-invert-bug) below.
1. **`u`/`v` update uses branching helpers instead of Rust's branchless carry chain.** Rust's `step()` computes the `u`/`v` update as a single branchless carry chain over full-width `u, v`, using the constant `MODULUS_XOR_TWO_MODULUS` to interleave negation with one-or-two modulus additions in the same loop (`field.rs:525-617`). The Dafny port splits the three halving cases (even, odd-and-≥p, odd-and-<p) and delegates to the branching helpers `invert_u_diff` and `invert_halve_u`. Both produce identical results modulo `p`, captured by the `InvertUHalveSpec` postcondition. The full Rust code is quoted as a comment block on the `step_u_v_phase` method header for audit traceability.
1. Rust's nested `fn step` is decomposed into `step_a_b_phase` (ports `field.rs:475-516,612-615`) and `step_u_v_phase` (ports `field.rs:525-617`) in Dafny to keep each method's verification context manageable. Each method header quotes the exact Rust line range it ports.
1. The parity check `a.as_limbs()[0].0 & 1` is implemented as `LimbToInt(a.limbs[0]) % 2`.

<a id="upstream-invert-bug"></a>
**Upstream `invert()` bug.**

The partial-width optimisation in Rust's `step()` is unsound: when a phase
transition occurs while a high limb of `a` or `b` is still nonzero, that limb is
silently truncated, destroying the loop's GCD invariant. The algorithm then
converges to `(0, g)` for some spurious `g ≠ 1`, and the returned `v` satisfies

```
v · y ≡ g   (mod p)
```

rather than `v · y ≡ 1 (mod p)`. For example, for `y = 3 · 2^66`, `y.invert()`
returns a value `v` with `v · y ≡ 5 (mod p)`.

The bug is deterministic for inputs of the form `y = odd · 2^k` with `k ≥ 66`
and `odd > 1`; pure powers of two (`odd = 1`) still return correct inverses.

The following regression test, placed in
[`crypto/helioselene/src/field.rs`](https://github.com/monero-oxide/monero-oxide/blob/27b1c7f2918444560c7383e7a5fbddb481dbf2d2/crypto/helioselene/src/field.rs),
reproduces the failure:

```rust
#[test]
fn test_invert_three_times_two_to_the_66() {
    // Regression: `invert()` must return a true modular inverse for every
    // nonzero field element. For y = 3 * 2^66 the partial-width loop drops a
    // nonzero limb at a phase transition, converging to a spurious GCD
    // instead of 1, and the returned `v` satisfies `v * y = 5 (mod p)`.
    let mut bytes = [0u8; 32];
    bytes[8] = 0x0c; // 3 << 2 at byte offset 8 => 3 * 2^66
    let y = Option::<HelioseleneField>::from(HelioseleneField::from_repr(bytes))
        .unwrap();
    let inv = Option::<HelioseleneField>::from(y.invert()).unwrap();
    assert_eq!(
        inv * y,
        HelioseleneField::ONE,
        "invert() returned a wrong inverse for 3 * 2^66",
    );
}
```

Running

```
cargo test --package helioselene --lib -- \
    field::test_invert_three_times_two_to_the_66 --exact --nocapture
```

reports:

```text
assertion `left == right` failed: invert() returned a wrong inverse for 3 * 2^66
  left: HelioseleneField(Uint(0x0000000000000000000000000000000000000000000000000000000000000005))
 right: HelioseleneField(Uint(0x0000000000000000000000000000000000000000000000000000000000000001))
```

Any one of the following remediations restores correctness:

1. Remove the `limbs`-truncation optimisation and always use full-width limb operations (this is the approach taken by the Dafny port).
2. Retain the optimisation but widen the per-phase iteration count so that any nonzero high limb is fully consumed before it would be truncated.
3. Switch to Pornin's Algorithm 2 (top- and bottom-bit approximation), the algorithm proved correct in the cited paper.

#### `sqrt()`

1. The Rust `Option` struct is modeled as a tuple: `(true, value)` corresponds to `Some(value)`, and `(false, value)` corresponds to `None`.
2. The initial table pre-computation is computed in a helper function to ease the verification effort and reuse proving effort from
3. The `to_le_bits()` is modeled by just directly extracting bits within the loop.
4. The check `(bits & (1 << 3)) != 0` is implemented as `bits >= 8` (along with proving `bits < 16`)
5. `conditional_negate()` is replaced with an `if` statement.
6. The final `CtOption` `ct_eq` check is implemented with an inlined loop
7. Some internal logic is extracted into helper methods

## Additional verified methods

Beyond the official targets, the following methods are also ported and mechanically verified.

### Field operations (field.rs)

| Function | Ported | Verified | Limitations? |
| --- | --- | --- | --- |
| `select_word` | Yes | Yes | No |
| `sub_value` | Yes | Yes | No |
| `red1` | Yes | Yes | No |
| `add` (field_add) | Yes | Yes | No |
| `sub` (field_sub) | Yes | Yes | No |
| `neg` (field_neg) | Yes | Yes | No |
| `double` (field_double) | Yes | Yes | No |
| `mul` (field_mul) | Yes | Yes | No |
| `square` (field_square) | Yes | Yes | No |
| `field_is_zero` | Yes | Yes | No |
| `field_is_odd` | Yes | Yes | Yes |
| `field_from_repr` | Yes | Yes | Yes |
| `field_to_repr` | Yes | Yes | Yes |

#### `field_is_odd()`

1. `&1` is replaced with `%2 == 1`

#### `field_from_repr()`

1. The loop over the limbs is unrolled

### field_to_repr()

1. The type signature is changed to return a `U256` instead of a `[u8; 32]`.

### Point operations (point.rs)

A small
subset of point constructors/helpers is mechanically verified.

| Function | Ported | Verified | Limitations |
| --- | --- | --- | --- |
| `point_identity` | Yes | Yes | No |
| `point_generator` | Yes | Yes | No |
| `point_from_xy` | Yes | Yes | Yes |
| `point_neg` | Yes | Yes | No |
| `point_sub` | Yes | Yes | No |
| `point_eq` | Yes | Yes | No |
| `point_is_identity` | No | Yes | Yes |
| `point_select` | Yes | Yes | Yes |

#### `point_from_xy()`

1. `CtOption` is modeled as a tuple `(isSome, value)`.

#### `point_is_identity()`

1. Checks `z == 0` rather than `x`. Requires Euler criterion to prove correspondence.


#### `point_select()`

1. `conditional_select` is modeled with an `if` statement.

### Crypto-bigint library functions

| Function | Ported | Verified |
| --- | --- | --- |
| `Limb.mac` | Yes | Yes |
| `Limb.sbb` | Yes | Yes |
| `U256.sbb` | Yes | Yes |

## Trusted Computing Base (TCB)

The following items are marked `{:axiom}` or are models of functions
trusted to be correct.
All other assertions are mechanically verified.

### bit-vector operations

Several bit-vector functions were modeled without using bit-vectors directly.
This is because the joint bit-vector / integer theory solvers are not up to the
task of verifying statements reasoning about the two data types simultaneously.
Future work could verify that the bit-vector implementations satisfy the model.

1. `src/crypto_bigint_0_5_5/Limb.dfy`
   1. `WordShr()` : Shifting is implemented as division by the corresponding power of 2.
   2. `WideWordShr()`: Shifting is implemented as division by the corresponding power of 2.
   3. `LimbAnd()`: The `&` operation is only modeled for two hard-coded masks. Dafny proves that, at each callsites, one of the hard-coded masks is used.

Additionally, we added the following axioms

| Axiom | File | Description |
| --- | --- | --- |
| `BvXorAllOnesLemma` | Limb.dfy | NOT(x) as int == MAX - x |
| `BV64ToIntHomomorphicAxiom` | Modular.dfy | (a as int + b as int) % TWO_POW_64 == (a + b) as int |
| `BV64ToIntConversionMonotonicPlusOneAxiom` | Modular.dfy | (a <= b) && (a != b) ==> a <= b - 1 |

### Modified functions

* `src/helpers/Limbs.dfy`
  * `copy_from_slice()`'s signature was modified with start/stop indices and specialized to the `Limb` type. This was done to support Dafny.

### Primality axiom

| Axiom | File | Description |
| --- | --- | --- |
| `ModulusIsPrimeLemma` | field/Sqrt.dfy, field/Invert.dfy | p = 2^255 - 19 is prime (verified externally via Sage) |

### Library code axioms

| Axiom | File | Description |
| --- | --- | --- |
| `mul_wide` | U256.dfy | 256x256 → 512-bit multiply (crypto-bigint 0.5.5) |
| `square_wide` | U256.dfy | 256 → 512-bit square (crypto-bigint 0.5.5) |

### Point operation stubs

All `Field25519` methods
are modeled as correctly implementing
Field25519.

## Trusted Computing Base (TCB): Work-in-progress

These are currently in the TCB, but will hopefully be removed.

### CAS-verified polynomial identities

These polynomial identities were verified using SymPy but are too large
for z3 to check inline.

| Axiom | File | Description |
| --- | --- | --- |
| `PointDoubleFactorizationLemma` | Point.dfy | Point doubling output satisfies curve equation |
| `PointAddFactorizationLemma` | Point.dfy | Point addition output satisfies curve equation |


## Structure

- `src/crypto_bigint_0_5_5/`: Limb/U256/U128 helpers modeled after crypto-bigint 0.5.5.
- `src/helioselene/field/`: Helioselene field routines split into Base, Red256, Red512, Arith, Pow, Sqrt, Invert, and Repr modules.
- `src/helioselene/Field.dfy`: Thin facade that includes and re-exports all field sub-modules.
- `src/helioselene/Point.dfy`: Point operations (structural ports, partially verified).
- `src/helpers/`: Math, modular arithmetic, number theory, and proof infrastructure.
- Standard library arithmetic (DivMod, Power, etc.) provided via `standard-libraries = true` in dfyconfig.toml.

## Dafny

Install Dafny: https://dafny.org/latest/DafnyRef/DafnyRef#sec-install
Project configuration lives in `dfyconfig.toml`.

Verify the whole project with
```
dafny verify dfyconfig.toml --allow-warnings
```
Verify a single file with
```
dafny verify src/helioselene/Field.dfy --standard-libraries --allow-warnings
```
Build into an executable with
```
dafny build ./dfyconfig.toml
```

Standard library modules are enabled via `standard-libraries = true` in `dfyconfig.toml`.
For repo-local agent workflow, see `AGENTS.md` and `ai-instructions/dafny-skill/SKILL.md`.

# Developer setup
For Mac, we have had success with
```
brew install dafny
dafny --version
```
Which should output `4.11.0`.
VSCode can use this by setting
```
{
    "dafny.verificationTimeLimit": 60,
    "dafny.cliPath": "/opt/homebrew/bin/dafny",
    "dafny.version": "custom"
}
```
Note that installing with brew automatically uses z3 `4.15.4`, which is
needed to prove some of the mixed bitvector/int proofs related to XORs/ANDs.
