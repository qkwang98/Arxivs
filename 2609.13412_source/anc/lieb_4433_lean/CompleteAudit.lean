import Bridge.Young
import Lean.Elab.Print

/-! Read-only transitive axiom inventory for every theorem declared by this
project's imported mathematical modules. This command proves no theorem and
is not an evaluation mechanism used by the finite certificate. -/

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  for (name, info) in env.constants.toList do
    if !info.isTheorem then continue
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    if !(owner == `Bridge || (`Bridge).isPrefixOf owner) then continue
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"AXIOMS {name}: {axioms.qsort Name.lt |>.toList}"
    checked := checked + 1
  logInfo m!"AUDIT_CHECKED {checked} project theorems"
  unless checked > 100 do
    throwError "Unexpectedly small theorem inventory"

#print LiebBridge.Young.FinalBridge.bridge_inequality
#print LiebBridge.Young.FinalBridge.normalized_bridge
#print LiebBridge.Young.FinalBridge.pdc4433_of_four_pate
