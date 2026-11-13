# Coxeter geometric-sign suppliers for landmark 1

These two modules originate in TauCetiProject/TauCeti at
`62bbc0596dc3539d488232e4e924a338548ea0a9`. Their original exact Git-object
bytes are preserved as `upstream/**/*.lean.txt`. Copyright/author headers
remain intact; `LICENSE.TauCeti` is the exact upstream Apache-2.0 license.

For Lake dependency resolution they are mechanically relocated to
`ArtinLandmarkVendor.Geometric.{RankTwo,Sign}`. RankTwo source bytes are
unchanged. Sign changes exactly one import, from
`TauCeti.GroupTheory.Coxeter.Geometric.RankTwo` to
`ArtinLandmarkVendor.Geometric.RankTwo`. Mathematical declaration namespaces,
statements and proofs are unchanged. `provenance.json` records both original
and local hashes, paths, the exact import patch, and all dependencies.

The complete upstream import closure has nine TauCeti modules. Seven are
reused unchanged through the parent package, and no parent module is copied
or overridden. The new modules supply rank-two coefficient formulas, the
root-sign criterion, root-set properties and representation faithfulness.
They do not state real-point stabilizer or complexified-complement freeness.

Upstream uses Lean 4.36.0-rc2 and mathlib
`e8ba86fa9744dd8d90f48c1752bc735f61a4ca81`. The landmark retains parent
mathlib `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. The initial build with
unchanged upstream module paths failed because Lake resolved new modules
through the parent library. Relocated-source compilation, transitive axiom
audit and official kernel replay are root-owned acceptance checks; this
source preparation does not assert they have passed.
