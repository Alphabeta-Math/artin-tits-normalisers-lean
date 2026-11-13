module

meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms
import TauCeti.GroupTheory.Coxeter.Artin
import TauCeti.GroupTheory.Coxeter.Matsumoto
import TauCeti.GroupTheory.Coxeter.Parabolic

set_option autoImplicit false

#check TauCeti.ArtinGroup
#check TauCeti.ArtinGroup.gen
#check TauCeti.ArtinGroup.toCoxeterGroup
#check TauCeti.ArtinGroup.toCoxeterGroup_surjective
#check TauCeti.ArtinGroup.prod_map_gen_braidWord
#check TauCeti.matsumoto
#check CoxeterSystem.parabolic
#check CoxeterSystem.exists_isMinimalCosetRep
#check CoxeterSystem.length_mul_of_isMinimalCosetRep
#check CoxeterSystem.exists_isReduced_wordProd_eq_of_mem_parabolic

-- Namespace filtering would miss the supplier's extensions to CoxeterSystem.
-- Audit by defining module instead, including imported auxiliary declarations.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx]!
      if mod.toString.startsWith "TauCeti." then
        count := count + 1
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Forbidden supplier axiom {ax} in {name} ({mod})"
        logInfo m!"PROVIDER_AXIOMS {mod} {name}: {axioms}"
  if count == 0 then throwError "No supplier declarations audited"
  logInfo m!"Audited {count} supplier declarations; axiom allowlist passed"
