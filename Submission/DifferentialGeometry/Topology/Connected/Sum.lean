import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions.SumProd

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Function

namespace ConnectedComponents
open _root_.ConnectedComponents

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open _root_.ConnectedComponents in
def sumEquiv : ConnectedComponents (X ⊕ Y) ≃ (ConnectedComponents X ⊕ ConnectedComponents Y) where
  toFun := (Continuous.sumElim
    (continuous_inl.comp ConnectedComponents.continuous_coe)
    (continuous_inr.comp ConnectedComponents.continuous_coe)).connectedComponentsLift
  invFun := Sum.elim continuous_inl.connectedComponentsMap continuous_inr.connectedComponentsMap
  left_inv c := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    cases x <;> rfl
  right_inv c := by
    cases c with
    | inl c => obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c; rfl
    | inr c => obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ConnectedComponents.sumEquiv then
    throwError "Refusing to shadow existing declaration ConnectedComponents.sumEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `ConnectedComponents.sumEquiv ``Submission.ConnectedComponents.sumEquiv

end ConnectedComponents
