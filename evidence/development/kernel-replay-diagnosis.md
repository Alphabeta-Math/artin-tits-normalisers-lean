# Kernel replay diagnosis

The bundled official checker successfully replays each scientific module when
invoked separately. No additional checker installation or scientific source
change was necessary.

Commands ran from the Lake package with the pinned Lean 4.36.0-rc2 toolchain.
Each was captured with `set -o pipefail`; the checker exit status was printed
from `PIPESTATUS[0]` and returned by the shell.

Actual `lean --version` output:

```
Lean (version 4.36.0-rc2, x86_64-unknown-linux-gnu, commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a, Release)
```

The checker executable is the bundled
`/home/lazyinspirit/.elan/toolchains/leanprover--lean4---v4.36.0-rc2/bin/leanchecker`.
It has no implemented version flag. Bundled source SHA256 values:

- `bin/leanchecker`: `2b2ff08805ace61c935b023f8114ac3f7f1d3bc79cb4e8c47ef7801a5af58798`
- `src/lean/LeanChecker.lean`: `4a406b8ed95da0377206600b7b00a03bedc05102c0fadad641ffe0bfdb95122f`
- `src/lean/Lean/Replay.lean`: `251ed00e1cedd95c5d1fc4104ac191beb1de618abbc2fc49319ff0e37d139329`

| Command (after `lake env`) | Actual exit | Output log |
| --- | --- | --- |
| `leanchecker --verbose ArtinNormalisers` (root-owned attempt) | 139 (SIGSEGV) | `kernel-replay-attempt.log` (empty) |
| `leanchecker --verbose DefinitelyNotARealModule` | 1 | `replay-diagnostic-nonexistent.log` |
| `leanchecker --verbose ArtinNormalisers.NormalizerMap` | 0 | `replay-diagnostic-one-module.log` |
| `leanchecker --verbose ArtinNormalisers.QuotientMap` | 0 | `replay-diagnostic-quotient-module.log` |
| `leanchecker --verbose ArtinNormalisers.Kernel` | 0 | `replay-diagnostic-kernel-module.log` |

The nonexistent-module probe returns the documented exception, so the reported
crash is not an unconditional executable startup failure. The three successful
module commands print their module name and complete without diagnostics.

The bundled `src/lean/LeanChecker.lean` selects every module whose name has the
requested prefix, then starts each replay with `IO.asTask`. Consequently
`leanchecker ArtinNormalisers` selects the root and its child modules and
replays them concurrently. Root recorded SIGSEGV failures for that invocation,
the paranoid checker, and the source-script variant. The isolated successes
are consistent with an import/replay concurrency failure; no native backtrace
was available and a specific runtime defect has not been proved.

`--help` is not implemented by this checker: unrecognized flags are partitioned
away, and an argument-free invocation uses the manifest-derived default target.
It is therefore not a valid standalone startup or help probe.

The supported successful alternative is to invoke the official checker once
per scientific module **sequentially**. Do not place all three module names
into one checker invocation, which would again use concurrent replay tasks.
The root import module contains no declarations. Root will use these three
supported commands sequentially in the final harness. No custom replay driver
was written or used.

For each selected module the official routine loads exported, server and
private object data, imports the original prerequisites, collects the module's
constants from the most private part, and calls
`env.toKernelEnv.replay newConstants`. `Lean/Replay.lean` sends safe,
nonpartial definitions and theorems to `addDeclCore 0 0`; it additionally
compares generated constructors and recursors. The project scientific
declarations are definitions/theorems, with no unsafe or partial declarations.

These runs recheck the declarations in the three project modules relative to
their imported mathlib environments. They do **not** freshly recheck all of
mathlib from an empty environment. The official `--fresh` mode would perform
that stronger operation for a single module; it was not invoked here.

The source also supports `--from-export` and explicitly references lean4lean
as a separate verifier with a matching CLI. Neither lean4lean nor a
nanoda/export pipeline was installed or claimed as checked: the supported
official per-module commands already supply the requested kernel replay.

No frozen proof input was modified during this investigation.
