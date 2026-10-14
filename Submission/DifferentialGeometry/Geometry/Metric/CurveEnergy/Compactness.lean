import Submission.DifferentialGeometry.Geometry.Metric.CurveEnergy.Lipschitz
import Submission.DifferentialGeometry.Analysis.Sobolev.Interval.TraceCompactness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] [PseudoMetricSpace X]

theorem tendstoUniformlyOn_of_ae_tendsto_of_intrinsic_curve_energy_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ι : X → M) (hι : ∀ x y, _root_.EDist.edist x y = riemannianEDistOf g (ι x) (ι y))
    (γ : ℕ → ℝ → X) (v : ℝ → X)
    (hLip : ∀ n, ∃ K : ℝ≥0, ∀ s t,
      riemannianEDistOf g (ι (γ n s)) (ι (γ n t)) ≤ (K : ℝ≥0∞) * _root_.EDist.edist s t)
    {a b B : ℝ} (hab : a < b)
    (hint : ∀ n, _root_.MeasureTheory.IntegrableOn (fun t => (riemannianCurveSpeed g (ι ∘ γ n) t) ^ 2) (_root_.Set.Icc a b))
    (hbound : ∀ n, (∫ t in _root_.Set.Icc a b, (riemannianCurveSpeed g (ι ∘ γ n) t) ^ 2) ≤ B)
    (hv : ContinuousOn v (_root_.Set.Icc a b))
    (hae : ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b), _root_.Filter.Tendsto (fun n => γ n t) _root_.Filter.atTop (𝓝 (v t))) :
    TendstoUniformlyOn γ v _root_.Filter.atTop (_root_.Set.Icc a b) := by
  have hordered (n : ℕ) (s t : ℝ) (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) (hst : s ≤ t) :
      dist (γ n s) (γ n t) ≤ Real.sqrt (B * (t - s)) := by
    obtain ⟨K, hK⟩ := hLip n
    have hsub : _root_.Set.Icc s t ⊆ _root_.Set.Icc a b := _root_.Set.Icc_subset_Icc hs.1 ht.2
    have h := riemannianEDistOf_toReal_sq_le_interval_energy g hK hst ((hint n).mono_set hsub)
    have hmono : (∫ z in _root_.Set.Icc s t, (riemannianCurveSpeed g (ι ∘ γ n) z) ^ 2) ≤ B :=
      (_root_.MeasureTheory.setIntegral_mono_set (hint n) (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall hsub)).trans (hbound n)
    have heq : (riemannianEDistOf g (ι (γ n s)) (ι (γ n t))).toReal =
        dist (γ n s) (γ n t) := by rw [← hι, ← dist_edist]
    rw [heq] at h
    have hsq : _root_.Dist.dist (γ n s) (γ n t) ^ 2 ≤ B * (t - s) :=
      h.trans ((mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hst)).trans_eq (mul_comm _ _))
    have hsqrt := Real.sqrt_le_sqrt hsq
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg] using hsqrt
  apply MeasureTheory.tendstoUniformlyOn_Icc_of_ae_tendsto_of_sqrt_dist_bound (B := B) hab ?_ hv hae
  intro n s hs t ht
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hordered n s t hs ht hst
  · simpa only [dist_comm (γ n t) (γ n s), abs_of_nonneg (sub_nonneg.mpr hts)] using
      hordered n t s ht hs hts

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.tendstoUniformlyOn_of_ae_tendsto_of_intrinsic_curve_energy_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.tendstoUniformlyOn_of_ae_tendsto_of_intrinsic_curve_energy_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.tendstoUniformlyOn_of_ae_tendsto_of_intrinsic_curve_energy_bound ``Submission.DifferentialGeometry.Geometry.tendstoUniformlyOn_of_ae_tendsto_of_intrinsic_curve_energy_bound

end DifferentialGeometry.Geometry

end

end
