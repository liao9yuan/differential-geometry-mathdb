import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNoncompactOrientedBuffered
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedPositiveBufferedLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactNonroundLimitTopology

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

theorem exists_eventually_buffered_with_cap_neck_charts_of_nonround_oriented_windowed_models
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0))
    (hreg : ∀ i, _root_.Set.Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    {phi : ℕ → ℕ} (hphi : _root_.Filter.Tendsto phi _root_.Filter.atTop _root_.Filter.atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (_root_.Set.Icc (-A) 0) order eta))
    {kappaL : ℝ} (hL : IsAncientKappaSolution kappaL L) (hscalar : L.S.scalar 0 L.basepoint = 1)
    (hnotround : ∀ i, ¬ KappaSolutions.IsShrinkingSphericalSpaceFormFlow (W i).model)
    (orient : ∀ i, TangentOrientationSection (W i).model.M)
    {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in _root_.Filter.atTop,
      ∃ B : BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i)),
        B.witness.capTubeHasNeckChart alpha := by
  by_cases hc : CompactSpace L.M
  · let _ : CompactSpace L.M := hc
    let _ : CompactSpace (L.atTime 0).M := hc
    obtain ⟨data⟩ := nonempty_positiveComponent_of_compact_nonround_pointed_limit
      (fun i => (W i).model) (fun i => (W i).model_ancient) hnotround orient (L.atTime 0) F
    obtain ⟨C, hC, hbuffer⟩ := exists_eventually_buffered_with_cap_tube_neck_chart_of_windowed_models_of_compact_positive_limit
      hS W hdelta hreg L hL hphi F hcmp hscalar data
    exact ⟨C, hC, hbuffer.mono fun i hi => hi alpha ha H⟩
  · have hnc : NoncompactSpace L.M := not_compactSpace_iff.mp hc
    exact exists_eventually_buffered_with_cap_neck_charts_of_windowed_models_of_noncompact_oriented_limit
      hS W hdelta hreg L hphi F hcmp hL hnc hscalar orient ha hasmall H

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_with_cap_neck_charts_of_nonround_oriented_windowed_models then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_with_cap_neck_charts_of_nonround_oriented_windowed_models"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_with_cap_neck_charts_of_nonround_oriented_windowed_models ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_with_cap_neck_charts_of_nonround_oriented_windowed_models

theorem exists_eventually_buffered_of_nonround_oriented_windowed_models
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0))
    (hreg : ∀ i, _root_.Set.Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    {phi : ℕ → ℕ} (hphi : _root_.Filter.Tendsto phi _root_.Filter.atTop _root_.Filter.atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (_root_.Set.Icc (-A) 0) order eta))
    {kappaL : ℝ} (hL : IsAncientKappaSolution kappaL L) (hscalar : L.S.scalar 0 L.basepoint = 1)
    (hnotround : ∀ i, ¬ KappaSolutions.IsShrinkingSphericalSpaceFormFlow (W i).model)
    (orient : ∀ i, TangentOrientationSection (W i).model.M)
    {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in _root_.Filter.atTop,
      Nonempty (BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i))) := by
  obtain ⟨C, hC, hB⟩ := exists_eventually_buffered_with_cap_neck_charts_of_nonround_oriented_windowed_models
    hS W hdelta hreg L hphi F hcmp hL hscalar hnotround orient ha hasmall H
  exact ⟨C, hC, hB.mono (fun _ ⟨B, _⟩ => ⟨B⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_of_nonround_oriented_windowed_models then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_of_nonround_oriented_windowed_models"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_of_nonround_oriented_windowed_models ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_of_nonround_oriented_windowed_models


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
