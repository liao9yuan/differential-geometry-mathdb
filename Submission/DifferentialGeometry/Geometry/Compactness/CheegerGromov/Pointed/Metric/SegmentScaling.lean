import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scaling
import Submission.DifferentialGeometry.Geometry.Metric.Segment
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem PointedRiemannianManifold.exists_isometric_segment_scaleMetric
    (L : PointedRiemannianManifold.{u, uE, uH} I) (hL : PathConnectedSpace L.M)
    (c : ℝ) (hc : 0 < c) {rho : ℝ} (hrho : 0 < rho) :
    let _ : EMetricSpace L.M := L.emetricSpace
    ∀ g : C(_root_.Set.Ico 0 rho, L.M), Isometry g → g ⟨0, le_rfl, hrho⟩ = L.basepoint →
      _root_.Filter.Tendsto (fun t => metricScalarAt L.metric (g t))
        (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) _root_.Filter.atTop →
      let LB := L.scaleMetric c hc
      let _ : PathConnectedSpace LB.M := hL
      let _ : EMetricSpace LB.M := LB.emetricSpace
      let _ : MetricSpace LB.M := EMetricSpace.toMetricSpace
        (fun x y => riemannianEDistOf_ne_top LB.metric x y)
      ∃ gB : C(_root_.Set.Ico 0 (Real.sqrt c * rho), LB.M),
        (∀ t, gB t = g ⟨t / Real.sqrt c,
          div_nonneg t.property.1 (Real.sqrt_nonneg c),
          (div_lt_iff₀ (Real.sqrt_pos.mpr hc)).mpr (by simpa [mul_comm] using t.property.2)⟩) ∧
        Isometry gB ∧ gB ⟨0, le_rfl, mul_pos (Real.sqrt_pos.mpr hc) hrho⟩ = LB.basepoint ∧
        _root_.Filter.Tendsto (fun t => metricScalarAt LB.metric (gB t))
          (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 (Real.sqrt c * rho) → ℝ) (𝓝 (Real.sqrt c * rho))) _root_.Filter.atTop ∧
        ∃ q : UniformSpace.Completion LB.M,
          _root_.Filter.Tendsto (fun t => (gB t : UniformSpace.Completion LB.M))
            (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 (Real.sqrt c * rho) → ℝ) (𝓝 (Real.sqrt c * rho))) (𝓝 q) ∧
          (∀ t : _root_.Set.Ico 0 (Real.sqrt c * rho),
            _root_.Dist.dist q (gB t : UniformSpace.Completion LB.M) = Real.sqrt c * rho - t) ∧
          q ∉ _root_.Set.range (fun x : LB.M => (x : UniformSpace.Completion LB.M)) := by
  let _ : EMetricSpace L.M := L.emetricSpace
  dsimp only
  intro g hg hbase hblow
  let LB := L.scaleMetric c hc
  let _ : PathConnectedSpace LB.M := hL
  let _ : EMetricSpace LB.M := LB.emetricSpace
  let _ : MetricSpace LB.M := EMetricSpace.toMetricSpace
    (fun x y => riemannianEDistOf_ne_top LB.metric x y)
  have hk := Real.sqrt_pos.mpr hc
  let d : _root_.Set.Ico 0 (Real.sqrt c * rho) → _root_.Set.Ico 0 rho := fun t =>
    ⟨t / Real.sqrt c, div_nonneg t.property.1 hk.le,
      (div_lt_iff₀ hk).mpr (by simpa [mul_comm] using t.property.2)⟩
  have hdcont : Continuous d := (continuous_subtype_val.div_const _).subtype_mk _
  let gB : C(_root_.Set.Ico 0 (Real.sqrt c * rho), LB.M) := ⟨fun t => g (d t), g.continuous.comp hdcont⟩
  have hiso : Isometry gB := by
    intro s t
    change riemannianEDistOf (DifferentialGeometry.scaleMetric c hc L.metric) (g (d s)) (g (d t)) = _root_.EDist.edist s t
    rw [edistOf_scale]
    have hh := hg.edist_eq (d s) (d t)
    change riemannianEDistOf L.metric (g (d s)) (g (d t)) = _ at hh
    rw [hh]
    change ENNReal.ofReal (Real.sqrt c) * _root_.EDist.edist ((s : ℝ) / Real.sqrt c) ((t : ℝ) / Real.sqrt c) =
      _root_.EDist.edist (s : ℝ) (t : ℝ)
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, ← ENNReal.ofReal_mul hk.le]
    congr 1
    rw [← sub_div, abs_div, abs_of_pos hk, mul_div_cancel₀ _ hk.ne']
  have hbaseB : gB ⟨0, le_rfl, mul_pos hk hrho⟩ = LB.basepoint := by
    have hd0 : d ⟨0, le_rfl, mul_pos hk hrho⟩ = ⟨0, le_rfl, hrho⟩ :=
      Subtype.ext (zero_div _)
    change g (d ⟨0, le_rfl, mul_pos hk hrho⟩) = L.basepoint
    rw [hd0]
    exact hbase
  have hd : _root_.Filter.Tendsto d
      (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 (Real.sqrt c * rho) → ℝ) (𝓝 (Real.sqrt c * rho)))
      (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) := by
    apply tendsto_comap_iff.mpr
    have hh := (_root_.Filter.tendsto_comap : _root_.Filter.Tendsto (Subtype.val : _root_.Set.Ico 0 (Real.sqrt c * rho) → ℝ)
      (_root_.Filter.comap Subtype.val (𝓝 (Real.sqrt c * rho))) (𝓝 (Real.sqrt c * rho))).div_const (Real.sqrt c)
    simpa only [d, Function.comp_def, mul_div_cancel_left₀ rho hk.ne'] using hh
  have hblowB : _root_.Filter.Tendsto (fun t => metricScalarAt LB.metric (gB t))
      (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 (Real.sqrt c * rho) → ℝ) (𝓝 (Real.sqrt c * rho))) atTop := by
    have hh := (hblow.comp hd).const_mul_atTop (inv_pos.mpr hc)
    convert hh using 1
    funext t
    change metricScalarAt (DifferentialGeometry.scaleMetric c hc L.metric) (g (d t)) =
      c⁻¹ * metricScalarAt L.metric (g (d t))
    exact metricScalarAt_scaleMetric c hc L.metric (g (d t))
  have hmap : _root_.Filter.NeBot (_root_.Filter.map (Subtype.val : _root_.Set.Ico 0 (Real.sqrt c * rho) → ℝ)
      (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 (Real.sqrt c * rho) → ℝ) (𝓝 (Real.sqrt c * rho)))) := by
    rw [_root_.Filter.map_comap_setCoe_val]
    exact right_nhdsWithin_Ico_neBot (mul_pos hk hrho)
  let _ := hmap.of_map
  obtain ⟨q, hq, hdist⟩ :=
    DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry (mul_pos hk hrho) hiso
  have hmissing : q ∉ _root_.Set.range (fun x : LB.M => (x : UniformSpace.Completion LB.M)) := by
    rintro ⟨x, hx⟩
    exact (UniformSpace.Completion.ne_coe_of_tendsto_atTop
      (f := fun x => metricScalarAt LB.metric x) hq hblowB x
      (metricScalar_smooth LB.metric).continuous.continuousAt) hx.symm
  exact ⟨gB, fun _ => rfl, hiso, hbaseB, hblowB, q, hq, hdist, hmissing⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.exists_isometric_segment_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.exists_isometric_segment_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.exists_isometric_segment_scaleMetric ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.exists_isometric_segment_scaleMetric

end DifferentialGeometry.CheegerGromovCompactness
