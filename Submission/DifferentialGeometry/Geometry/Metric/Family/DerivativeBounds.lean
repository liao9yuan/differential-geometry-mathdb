import Submission.DifferentialGeometry.Geometry.Metric.CompactDerivative
import Submission.DifferentialGeometry.Geometry.Metric.Family.UniformEquivalence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_metric_mfderiv_bound_on_compact_time
    (g : ℝ → SmoothRiemannianMetric I M) {K : Set ℝ} (hK : IsCompact K)
    (hg : Curvature.tensor0SFamilyContinuousOnSet
      (I := I) (M := M) 2 K
      (fun t x => DifferentialGeometry.Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) 1 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ C * Real.sqrt ((g t).inner x v v) := by
  obtain ⟨A, hA, hmet⟩ :=
    Curvature.exists_metric_equivalence_bound_on_compact_time g hK hg (g 0)
  obtain ⟨B, hB⟩ := exists_metric_mfderiv_bound (g 0) hf
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hApos : 0 < A := zero_lt_one.trans_le hA
  refine ⟨(B : ℝ) * Real.sqrt A, mul_nonneg B.coe_nonneg (Real.sqrt_nonneg _), ?_⟩
  intro t ht x v
  have hlow := (hmet t ht x v).1
  have hlow' : (g 0).inner x v v ≤ A * (g t).inner x v v := by
    have hh := mul_le_mul_of_nonneg_left hlow hA0
    simpa only [← mul_assoc, mul_inv_cancel₀ hApos.ne', one_mul] using hh
  have hroot : Real.sqrt ((g 0).inner x v v) ≤
      Real.sqrt A * Real.sqrt ((g t).inner x v v) := by
    calc
      _ ≤ Real.sqrt (A * (g t).inner x v v) := Real.sqrt_le_sqrt hlow'
      _ = _ := Real.sqrt_mul hA0 _
  exact (hB x v).trans ((mul_le_mul_of_nonneg_left hroot B.coe_nonneg).trans_eq
    (mul_assoc _ _ _).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_metric_mfderiv_bound_on_compact_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_metric_mfderiv_bound_on_compact_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_metric_mfderiv_bound_on_compact_time ``Submission.DifferentialGeometry.Geometry.exists_metric_mfderiv_bound_on_compact_time

end DifferentialGeometry.Geometry
