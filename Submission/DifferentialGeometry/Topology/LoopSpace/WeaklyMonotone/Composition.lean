import Submission.DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Submission.DifferentialGeometry.Topology

namespace CircleDeg1Lift
open _root_.CircleDeg1Lift

open _root_.CircleDeg1Lift in
theorem exists_continuous_lift_comp
    {σ δ : C(loopCircle, loopCircle)} (f h : CircleDeg1Lift)
    (hf : Continuous f) (hh : Continuous h)
    (hσ : ∀ t : ℝ, (f t : loopCircle) = σ (t : loopCircle))
    (hδ : ∀ t : ℝ, (h t : loopCircle) = δ (t : loopCircle)) :
    ∃ k : CircleDeg1Lift, Continuous k ∧
      ∀ t : ℝ, (k t : loopCircle) = (σ.comp δ) (t : loopCircle) := by
  let k : CircleDeg1Lift :=
    { toFun := fun t => f (h t)
      monotone' := f.monotone.comp h.monotone
      map_add_one' := fun t => by rw [h.map_add_one, f.map_add_one] }
  refine ⟨k, hf.comp hh, ?_⟩
  intro t
  change (f (h t) : loopCircle) = σ (δ (t : loopCircle))
  rw [hσ, hδ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CircleDeg1Lift.exists_continuous_lift_comp then
    throwError "Refusing to shadow existing declaration CircleDeg1Lift.exists_continuous_lift_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `CircleDeg1Lift.exists_continuous_lift_comp ``Submission.CircleDeg1Lift.exists_continuous_lift_comp

end CircleDeg1Lift

end
