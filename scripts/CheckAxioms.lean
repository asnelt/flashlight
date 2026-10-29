import Flashlight

/-!
Fails if the main theorem depends on axioms beyond `propext`, `Classical.choice` and
`Quot.sound` (for example `sorryAx` from a `sorry`). Run with
`lake env lean scripts/CheckAxioms.lean`.
-/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← liftCoreM <| collectAxioms ``Flashlight.flashlight
  let bad := axioms.filter (!allowed.contains ·)
  unless bad.isEmpty do
    throwError "`Flashlight.flashlight` depends on nonstandard axioms: {bad}"
  logInfo m!"`Flashlight.flashlight` depends on axioms: {axioms}"
