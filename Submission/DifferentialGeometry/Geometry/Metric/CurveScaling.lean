import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem distance_parametrized_segment_scaleMetric
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (gamma : ℝ → M) {ell : ℝ} (hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (hmin : ∀ s ∈ _root_.Set.Icc 0 ell, ∀ t ∈ _root_.Set.Icc 0 ell,
      riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t => gamma (t / Real.sqrt c)) ∧
      (fun t => gamma (t / Real.sqrt c)) 0 = gamma 0 ∧
      (fun t => gamma (t / Real.sqrt c)) (Real.sqrt c * ell) = gamma ell ∧
      ∀ s ∈ _root_.Set.Icc 0 (Real.sqrt c * ell), ∀ t ∈ _root_.Set.Icc 0 (Real.sqrt c * ell),
        riemannianEDistOf (scaleMetric c hc g) (gamma (s / Real.sqrt c))
          (gamma (t / Real.sqrt c)) = ENNReal.ofReal |s - t| := by
  have hk := Real.sqrt_pos.mpr hc
  refine ⟨hsmooth.comp (contMDiff_iff_contDiff.mpr (contDiff_id.div_const _)),
    by simp, by dsimp only; rw [mul_div_cancel_left₀ ell hk.ne'], ?_⟩
  intro s hs t ht
  have hs' : s / Real.sqrt c ∈ _root_.Set.Icc (0 : ℝ) ell :=
    ⟨div_nonneg hs.1 hk.le, (div_le_iff₀ hk).mpr (by simpa [mul_comm] using hs.2)⟩
  have ht' : t / Real.sqrt c ∈ _root_.Set.Icc (0 : ℝ) ell :=
    ⟨div_nonneg ht.1 hk.le, (div_le_iff₀ hk).mpr (by simpa [mul_comm] using ht.2)⟩
  rw [edistOf_scale, hmin _ hs' _ ht', ← ENNReal.ofReal_mul hk.le]
  congr 1
  rw [← sub_div, abs_div, abs_of_pos hk, mul_div_cancel₀ _ hk.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.distance_parametrized_segment_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.distance_parametrized_segment_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.distance_parametrized_segment_scaleMetric ``Submission.DifferentialGeometry.Geometry.distance_parametrized_segment_scaleMetric

end DifferentialGeometry.Geometry
