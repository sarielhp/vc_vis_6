import Lean.Elab.Tactic.Basic

/-!
# Zero-Elaborator-Overhead Pure Kernel Reflexivity Tactic (`KernelRfl.lean`)

Assigns `@Eq.refl Bool Bool.true` directly as the proof term without running duplicate
interpreted `Meta.isDefEq` reduction in the elaborator. Lean's trusted C++ kernel still
verifies `lhs =def= Bool.true` from scratch with zero extra axioms (`[propext]` only).
-/

elab "kernel_rfl_true" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  g.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true))
  Lean.Elab.Tactic.replaceMainGoal []
