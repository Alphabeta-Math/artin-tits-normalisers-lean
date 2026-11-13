module

meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms
import ArtinNormalisersFull

set_option autoImplicit false

#check ArtinNormalisers.Artin.Group
#check ArtinNormalisers.Artin.projection
#check ArtinNormalisers.Artin.parabolic
#check ArtinNormalisers.Artin.coxeterParabolic
#check ArtinNormalisers.Artin.map_parabolic
#check ArtinNormalisers.Artin.exists_normalizer_lift
#check ArtinNormalisers.Artin.normalizerQuotientMap
#check ArtinNormalisers.Artin.pureNormalizerImage
#check ArtinNormalisers.Artin.lemma_2_8
#print axioms ArtinNormalisers.Artin.lemma_2_8

-- Defining-module selection includes private helpers, not just public names.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx]!
      if mod.toString.startsWith "ArtinNormalisers." then
        count := count + 1
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Forbidden project axiom {ax} in {name} ({mod})"
        logInfo m!"PROJECT_TYPE {mod} {name}: {ci.type}"
        logInfo m!"PROJECT_AXIOMS {name}: {axioms}"
  if count == 0 then throwError "No project declarations audited"
  logInfo m!"Audited {count} project declarations; axiom allowlist passed"
