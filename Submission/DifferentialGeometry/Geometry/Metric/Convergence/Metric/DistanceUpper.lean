import Submission.DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian

variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {l : Filter ι}

theorem eventually_riemannianEDistOf_lt_of_compact_metric_upper
    (g : SmoothRiemannianMetric I M) (g' : ι → SmoothRiemannianMetric I M)
    (hupper : ∀ K : Set M, IsCompact K → ∀ B : ℝ, 1 < B →
      ∀ᶠ i in l, ∀ z ∈ K, ∀ v : TangentSpace I z,
        (g' i).inner z v v ≤ B ^ 2 * g.inner z v v)
    (x y : M) {R : ℝ} (hxy : riemannianEDistOf g x y < ENNReal.ofReal R) :
    ∀ᶠ i in l, riemannianEDistOf (g' i) x y < ENNReal.ofReal R := by
  have hR : 0 < R := ENNReal.ofReal_pos.mp (bot_le.trans_lt hxy)
  obtain ⟨S, hds, hSR⟩ := exists_between (ENNReal.toReal_lt_of_lt_ofReal hxy)
  have hS : 0 < S := ENNReal.toReal_nonneg.trans_lt hds
  have hxyS : riemannianEDistOf g x y < ENNReal.ofReal S :=
    (ENNReal.lt_ofReal_iff_toReal_lt (ne_top_of_lt hxy)).mpr hds
  have hratio : (1 : ℝ) < R / S :=
    (lt_div_iff₀ hS).mpr (by simpa only [one_mul] using hSR)
  obtain ⟨B, hB, hBR⟩ := exists_between hratio
  have hBpos : 0 < B := zero_lt_one.trans hB
  have hBS : B * S < R := (lt_div_iff₀ hS).mp hBR
  obtain ⟨γ, hzero, hone, hγ, hlength⟩ := exists_lt_of_edistOf_lt g hxyS
  have hK : IsCompact (γ '' _root_.Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hγ.continuousOn
  filter_upwards [hupper _ hK B hB] with i hi
  have hlength' : metricPathELength (g' i) γ 0 1 ≤
      ENNReal.ofReal B * metricPathELength g γ 0 1 := by
    rw [metricPathELength_eq, metricPathELength_eq, ← _root_.MeasureTheory.lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top]
    refine _root_.MeasureTheory.setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
    rw [← ENNReal.ofReal_mul hBpos.le]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Real.sqrt (B ^ 2 * g.inner (γ t)
          (mfderiv 𝓘(ℝ) I γ t 1) (mfderiv 𝓘(ℝ) I γ t 1)) :=
        Real.sqrt_le_sqrt (hi (γ t) ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩ _)
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hBpos.le]
  have hd := edistOf_le_metricPathELength (g' i) zero_le_one hγ
  rw [hzero, hone] at hd
  calc
    _ ≤ ENNReal.ofReal B * metricPathELength g γ 0 1 := hd.trans hlength'
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal S := mul_le_mul_right hlength.le _
    _ = ENNReal.ofReal (B * S) := (ENNReal.ofReal_mul hBpos.le).symm
    _ < ENNReal.ofReal R := (ENNReal.ofReal_lt_ofReal_iff hR).mpr hBS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.eventually_riemannianEDistOf_lt_of_compact_metric_upper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.eventually_riemannianEDistOf_lt_of_compact_metric_upper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.eventually_riemannianEDistOf_lt_of_compact_metric_upper ``Submission.DifferentialGeometry.Geometry.Riemannian.eventually_riemannianEDistOf_lt_of_compact_metric_upper

end DifferentialGeometry.Geometry.Riemannian
