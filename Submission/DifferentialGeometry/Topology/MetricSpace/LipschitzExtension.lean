import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

open scoped _root_.NNReal

namespace LipschitzOnWith
open _root_.LipschitzOnWith

variable {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

open _root_.LipschitzOnWith in
theorem exists_lipschitz_extension {f : X → F} {s : Set X} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) :
    ∃ (g : X → F) (L : ℝ≥0), LipschitzWith L g ∧ _root_.Set.EqOn f g s := by
  let e : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) := (Module.finBasis ℝ F).equivFunL
  obtain ⟨g, hg, hfg⟩ :=
    (e.toContinuousLinearMap.lipschitz.comp_lipschitzOnWith hf).extend_pi
  refine ⟨e.symm ∘ g, _, e.symm.toContinuousLinearMap.lipschitz.comp hg, ?_⟩
  intro x hx
  exact (e.symm_apply_apply (f x)).symm.trans (congrArg e.symm (hfg hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LipschitzOnWith.exists_lipschitz_extension then
    throwError "Refusing to shadow existing declaration LipschitzOnWith.exists_lipschitz_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `LipschitzOnWith.exists_lipschitz_extension ``Submission.LipschitzOnWith.exists_lipschitz_extension

end LipschitzOnWith

end
