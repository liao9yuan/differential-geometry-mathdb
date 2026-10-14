import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Mathlib.Analysis.Normed.Group.Bounded

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open _root_.Bundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_pos_bound_chartBasisVec_on_compact
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {K : Set M} (hK : IsCompact K)
    (hchart : K ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ K, ∀ i : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner x (chartBasisVecFiber (I := I) x₀ i x)
        (chartBasisVecFiber (I := I) x₀ i x)) ≤ R := by
  classical
  have hbound (i : Fin (Module.finrank ℝ E)) : ∃ C : ℝ, ∀ x ∈ K,
      Real.sqrt (chartGramMatrix g x₀ x i i) ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (((chartGramMatrix_entry_contMDiffOn g x₀ i i).continuousOn.mono hchart).sqrt)
    exact ⟨C, fun x hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hC x hx⟩
  choose C hC using hbound
  refine ⟨1 + ∑ i, _root_.Max.max (C i) 0, by positivity, fun x hx i => ?_⟩
  calc
    _ ≤ C i := hC i x hx
    _ ≤ _root_.Max.max (C i) 0 := le_max_left _ _
    _ ≤ ∑ j, _root_.Max.max (C j) 0 :=
      Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ i)
    _ ≤ _ := by linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.exists_pos_bound_chartBasisVec_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.exists_pos_bound_chartBasisVec_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.exists_pos_bound_chartBasisVec_on_compact ``Submission.DifferentialGeometry.Tensor.Coordinates.exists_pos_bound_chartBasisVec_on_compact

end DifferentialGeometry.Tensor.Coordinates
