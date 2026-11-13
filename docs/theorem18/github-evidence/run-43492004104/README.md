# Successful CI: Lemma 2.8 and Theorem 1.8 prerequisites

**This run does not prove full Theorem 1.8.** It verifies the completed
algebraic Lemma 2.8 and the separately scoped new geometric/topological
foundations.

- Run: <https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43492004104>
- Source commit: `4e6e7851a9ced34df49584e6bdb77f701698f2f5`.
- Conclusion: `success` on a fresh GitHub-hosted checkout.
- Algebraic artifact: 24 successful commands, 17 individual module replays,
  62 input hashes checked against the actual source tree.
- Foundation artifact: 32 successful commands, 27 individual module replays,
  65 input hashes checked against the actual source tree.
- Both independent-review bindings and every saved command-log SHA-256
  checked against the downloaded records. Artifact ZIP digests match the
  GitHub API's artifact metadata.

`archive-verification.json` records those actual archive checks.
`run.json`, `jobs.json` and `artifacts.json` preserve GitHub metadata;
`actions.log.gz` preserves complete Actions output. The two ZIPs preserve
all raw command logs and their original `verification.json`; copies of the
two verification records are also included for direct reading. `SHA256SUMS`
binds this archive's files.

The foundation audit covers 145 new project declarations and all 733
supplier declarations across exactly 37 modules. Replays use the official
single-module kernel checker relative to its imported mathlib environments;
they do not freshly replay all mathlib or use a second independent kernel.
The remaining chamber/freeness, ribbon/geometric comparison and Deligne
asphericity proofs are listed in the main report and plan.
