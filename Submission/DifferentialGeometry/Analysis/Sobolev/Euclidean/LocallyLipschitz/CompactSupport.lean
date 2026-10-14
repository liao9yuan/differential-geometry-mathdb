import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzW1

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

open scoped _root_.NNReal

variable {d : ℕ}

theorem exists_lipschitzWith_of_locallyLipschitz_hasCompactSupport
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyLipschitz u) (huc : HasCompactSupport u) :
    ∃ C : ℝ≥0, LipschitzWith C u := by
  obtain ⟨B₀, hB₀⟩ := huc.exists_bound_of_continuous hu.continuous
  let B : ℝ≥0 := ⟨max B₀ 0, le_max_right _ _⟩
  have hB : ∀ x, _root_.EDist.edist (u x) 0 ≤ B := by
    intro x
    rw [edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_le_coe]
    exact_mod_cast (hB₀ x).trans (le_max_left B₀ 0)
  exact lip_of_local_comp hu huc hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lipschitzWith_of_locallyLipschitz_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lipschitzWith_of_locallyLipschitz_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lipschitzWith_of_locallyLipschitz_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lipschitzWith_of_locallyLipschitz_hasCompactSupport

end DifferentialGeometry.Analysis.Sobolev.Euclidean
