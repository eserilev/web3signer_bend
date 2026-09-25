# Phase 0 spike: blst in a Bend foreign effect

Result: **pass** (2026-09-23).

## What the spike does

`main.bend` declares one foreign effect, `Bls.sign(sk, root)`. The C side (`bls.c`) calls blst v0.3.17, the version that Lighthouse uses. The effect takes a secret key and a signing root as hex strings, and it returns the compressed signature as a hex string.

## Build

```sh
BEND=~/.bend/bin/bend ./build.sh
../../build/phase0/sign <secret_key_hex> <signing_root_hex>
```

`bend main.bend -o sign` compiles in a temporary directory with fixed clang flags. It cannot find blst there. For this reason, `build.sh` runs `bend main.bend -o sign.c`, and then runs clang itself. It uses the flags of Bend (`-std=c11 -O3 ... -lpthread -lm`) and adds the blst header path and `libblst.a`.

With this method, blst uses its normal assembly build and its public header (`blst.h`). This build is the same as the build that Lighthouse uses.

## Results

| Test | Result |
|---|---|
| `bls12-381-tests` v0.1.1 `sign` vectors | 10/10 pass. The zero key is rejected. |
| Compare with the Lighthouse `bls` crate, 200 random keys and roots | 200/200 signatures are identical. |
| Edge keys `1`, `r-1` (valid) and `0`, `r`, `r+5`, `2^256-1` (not valid) | Same result as Lighthouse for all 6. |
| Bad hex input | Exit 22 with `bad secret key hex`. |

The Bend checker reports the defs that depend on foreign code: `Bls.sign`, `sign_args`, and `main`. This list shows which code no proof covers.

## What did not work

These two methods put blst into one C file, so that `bend -o sign` can build it with no extra flags:

- `#include "src/server.c"` with `__BLST_NO_ASM__`. On x86_64, blst selects 64-bit limbs and then needs `llimb_t`, but blst defines `llimb_t` only for 32-bit limbs. blst does not support this configuration.
- `blst.h` and `server.c` in one file. The public header and the internal code declare the same functions with different types.

These methods can work with hacks: hide `__x86_64__` to get 32-bit limbs, or call the internal types. The separate-compilation method above needs no hacks.

## Open points for phase 1

- The effect runs on the event loop (need `0`). 200 runs of the binary took 0.27 s, and 200 runs of `true` took 0.12 s. So one signature, with the Bend runtime start, takes at most 0.7 ms. Phase 1 moves the effect to `io_work` on a helper thread.
- The secret key goes through a Bend `String`. The pure Bend code does not wipe it. In phase 1, the key never enters Bend: the C side loads the keystore and keeps the key. Bend sees only a key index.
- `main.bend` has no `.js` import, so the effect exists only on the C target. `bend main.bend` (the JavaScript runner) cannot run it.
