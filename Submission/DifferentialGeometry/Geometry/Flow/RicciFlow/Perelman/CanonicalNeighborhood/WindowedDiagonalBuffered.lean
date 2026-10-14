import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiagonalCoverCanonical
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCapBufferedLimit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem exists_eventually_buffered_with_cap_neck_charts_of_windowed_models_of_diagonal_cylinder_limit
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
    (hscalar : L.S.scalar 0 L.basepoint = 1) (cover : KappaSolutions.ShrinkingCylinderCover L)
    (hdiagonal : cover.DiagonalModel) {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in _root_.Filter.atTop,
      ∃ B : BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i)),
        B.witness.capTubeHasNeckChart alpha := by
  let eps := neckModelTolerance (alpha / 4) / 2
  have heps : 0 < eps := half_pos (neckModelTolerance_pos (by positivity))
  have hepslt : eps < neckModelTolerance (alpha / 4) := by
    dsimp only [eps]
    exact half_lt_self (neckModelTolerance_pos (by positivity))
  have hepssmall : eps < 1 / 11 := hepslt.trans_le (neckModelTolerance_le (alpha / 4)) |>.trans (by linarith)
  obtain ⟨A, C0, K, cap, hcap, v, neck, hmap, hv, hcentral, hfar⟩ :=
    exists_canonicalWitness_with_neck_tube_of_diagonal_cylinder_cover L cover hdiagonal hscalar heps hepssmall
      (_root_.Max.max 40000 (2 * _root_.Max.max H 0))
  obtain ⟨C, hC, hi⟩ := K.exists_eventually_buffered_image_of_windowed_models_of_cap_with_neck_chart
    hS W hdelta hreg L hcomplete hphi F hcmp hscalar cap hcap neck hmap ha hasmall hepslt
    (fun y hy => (hfar y hy).le)
  refine ⟨C, hC, hi.mono ?_⟩
  intro i hi
  obtain ⟨_Ki, _hK, _capi, _depthi, _hKiAlt, _htubei, _hcorei, _hmapi, _ni, _hniMap, B, _heps, _hU, _hr, _hB, hcharts⟩ := hi
  exact ⟨B, hcharts⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_with_cap_neck_charts_of_windowed_models_of_diagonal_cylinder_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_with_cap_neck_charts_of_windowed_models_of_diagonal_cylinder_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_with_cap_neck_charts_of_windowed_models_of_diagonal_cylinder_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_with_cap_neck_charts_of_windowed_models_of_diagonal_cylinder_limit

theorem exists_eventually_buffered_of_windowed_models_of_diagonal_cylinder_limit
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
    (hscalar : L.S.scalar 0 L.basepoint = 1) (cover : KappaSolutions.ShrinkingCylinderCover L)
    (hdiagonal : cover.DiagonalModel) {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in _root_.Filter.atTop,
      Nonempty (BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i))) := by
  obtain ⟨C, hC, hB⟩ := exists_eventually_buffered_with_cap_neck_charts_of_windowed_models_of_diagonal_cylinder_limit
    hS W hdelta hreg L hcomplete hphi F hcmp hscalar cover hdiagonal ha hasmall H
  exact ⟨C, hC, hB.mono (fun _ ⟨B, _⟩ => ⟨B⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_of_windowed_models_of_diagonal_cylinder_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_of_windowed_models_of_diagonal_cylinder_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_of_windowed_models_of_diagonal_cylinder_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_of_windowed_models_of_diagonal_cylinder_limit


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
