import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedModelConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedShiTerminal
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonDistanceConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.Geometry.Riemannian

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem eventually_image_depth_of_windowed_models
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0))
    (hreg : ∀ i, _root_.Set.Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : _root_.Filter.Tendsto phi _root_.Filter.atTop _root_.Filter.atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (_root_.Set.Icc (-A) 0) order eta))
    {V : Set L.M} (hV : IsCompact V) {H : ℝ}
    (hdepth : ∀ y ∈ V, 2 * _root_.Max.max H 0 ≤ metricDistance (L.S.base.metric 0) L.basepoint y) :
    ∀ᶠ i in _root_.Filter.atTop, ∀ z ∈ (partialDiffeomorphTransMixed (F.partialDiffeomorph i)
        (W (phi i)).embedding) '' V,
      H / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) ≤
        metricDistance ((S (phi i)).base.metric (t (phi i))) (x (phi i)) z := by
  let Psi := fun i => partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  let g := fun i => rescaledMetric (S (phi i)) (t (phi i))
    ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).scalar_pos
  have hcompare (K : Set L.M) (hK : IsCompact K) : ∀ᶠ i in _root_.Filter.atTop,
      K ⊆ (Psi i).source ∧
        Nonempty (MetricComparisonOn L.S.base.metric (g i) (Psi i) K
          (_root_.Set.Icc (-1 : ℝ) 0) 0 (1 / 4)) :=
    WindowedModelWitness.eventually_composed_comparison hS W hdelta
      (fun i s hs => ((W i).normalized_window (hreg i)).2 hs) L hcomplete hphi F hcmp
      hK zero_lt_one 0 (by norm_num)
  have hc : RiemannianMetricComplete (L.S.base.metric 0) :=
    ⟨MetricComplete.complete (L.atTime 0) hcomplete⟩
  have hdist := eventually_metricDistance_bounds_on_compact_of_comparisons
    L.S.base.metric g Psi (show (0 : ℝ) ∈ _root_.Set.Icc (-1 : ℝ) 0 by norm_num)
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 : ℝ) / 4 < 1)
    hc hcompare (hV.insert L.basepoint)
  have hhalf : (1 : ℝ) / 2 ≤ Real.sqrt (1 - (1 / 4 : ℝ)) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  filter_upwards [hdist] with i hdi
  rintro _ ⟨y, hy, rfl⟩
  have hbase : Psi i L.basepoint = x (phi i) := by
    change (W (phi i)).embedding (F.map i L.basepoint) = x (phi i)
    have hb : F.map i L.basepoint = (W (phi i)).model.basepoint := F.basepoint_map i
    rw [hb, (W (phi i)).base_map]
  have hlo := (hdi L.basepoint (_root_.Set.mem_insert _ _) y (_root_.Set.mem_insert_of_mem _ hy)).1
  have hmul := mul_le_mul_of_nonneg_right hhalf
    (show 0 ≤ metricDistance (L.S.base.metric 0) L.basepoint y from ENNReal.toReal_nonneg)
  have hlower : H ≤ metricDistance (g i 0) (Psi i L.basepoint) (Psi i y) := by
    linarith [hdepth y hy, le_max_left H 0]
  simp only [g, rescaledMetric, parabolicTime_zero, metricDistance, edistOf_scale,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hlower
  rw [hbase] at hlower
  exact (div_le_iff₀ (Real.sqrt_pos.mpr (W (phi i)).scalar_pos)).mpr (by
    simpa only [mul_comm, metricDistance] using hlower)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_image_depth_of_windowed_models then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_image_depth_of_windowed_models"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_image_depth_of_windowed_models ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_image_depth_of_windowed_models

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
