import Submission.DifferentialGeometry.Analysis.Calculus.LipschitzConvolution
import Mathlib.Topology.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open _root_.LipschitzOnWith in
theorem LipschitzOnWith.exists_contDiff_lipschitz_approx
    {f : E → ℝ} {s : Set E} {C : ℝ≥0}
    (hf : LipschitzOnWith C f s) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith C g ∧
      ∀ x ∈ s, _root_.Dist.dist (g x) (f x) < ε := by
  obtain ⟨F, hF, hEq⟩ := hf.extend_real
  obtain ⟨g, hg, hgL, hlim⟩ := hF.exists_contDiff_lipschitz_tendstoUniformly
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.mp hlim ε hε).exists
  refine ⟨g n, hg n, hgL n, ?_⟩
  intro x hx
  rw [hEq hx]
  exact (dist_comm (g n x) (F x)).trans_lt (hn x)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.LipschitzOnWith
  let env ← Lean.getEnv
  if env.contains `LipschitzOnWith.exists_contDiff_lipschitz_approx then
    throwError "Refusing to shadow existing declaration LipschitzOnWith.exists_contDiff_lipschitz_approx"
  Lean.modifyEnv fun env => Lean.addAlias env `LipschitzOnWith.exists_contDiff_lipschitz_approx ``Submission.LipschitzOnWith.exists_contDiff_lipschitz_approx
