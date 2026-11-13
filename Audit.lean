module

meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms
import ArtinNormalisers

set_option autoImplicit false

#check ArtinNormalisers.normalizerMap
#check ArtinNormalisers.normalizerMap_apply
#check ArtinNormalisers.normalizerMap_maps_subgroup
#check ArtinNormalisers.quotientMap
#check ArtinNormalisers.quotientMap_mk
#check ArtinNormalisers.quotientMap_mem_ker_iff
#check ArtinNormalisers.kernel_eq_image
#check ArtinNormalisers.articleKernelMap
#check ArtinNormalisers.articleKernelImage
#check ArtinNormalisers.articleKernelImage_eq
#check ArtinNormalisers.kernel_eq_articleKernelImage

-- Check every project declaration, including generated auxiliary declarations,
-- against the transitive allowlist. Source-text searches alone are insufficient.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.getRoot == `ArtinNormalisers then
      count := count + 1
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      logInfo m!"AXIOMS {name}: {axioms}"
  if count == 0 then throwError "No project declarations audited"
  logInfo m!"Audited {count} project declarations; axiom allowlist passed"
