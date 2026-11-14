# TauCeti Čech fundamental-groupoid suppliers

Nine new modules from TauCetiProject/TauCeti commit
`62bbc0596dc3539d488232e4e924a338548ea0a9`, Apache-2.0, form the additional
closure of `FundamentalGroupoid.Cech.Colimit` and `Cech.Map`. The three older
modules Basic, Topology.Homotopy.Path, and Topology.UnitInterval are reused
unchanged from the parent package; their hashes are recorded in provenance.

Only imports of these nine new modules are relocated to ArtinChamberVendor;
all declaration namespaces remain TauCeti. Original bytes are retained as
inactive `.lean.txt` files, alongside complete unified patches, import edges,
source hashes and the upstream license. No mathematical proof or hypothesis
port was needed. Upstream Lean is v4.36.0-rc2 with mathlib e8ba86fa; this
package uses the same Lean with mathlib 65d730f7.

The endpoints concern actual Mathlib fundamental groupoids and actual open
subspaces, with concrete path/homotopy gluing and continuous-map naturality.
They do not construct the relative arrangement cover or prove its Deligne
comparison, ribbon identification, or asphericity. Full Theorem 1.8 remains
unproved. Source-bound executed checks live separately under
`../evidence/providers/`; provenance alone is not supplier acceptance.
