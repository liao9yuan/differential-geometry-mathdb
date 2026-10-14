import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckCanonical
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BufferedCanonical
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNeckCanonicalLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderNecks

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
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

theorem exists_eventually_buffered_with_cap_tube_neck_chart_of_windowed_models_of_trivial_cylinder_limit
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
    {kappaL : ℝ} (hL : IsAncientKappaSolution kappaL L)
    (hscalar : L.S.scalar 0 L.basepoint = 1) (cover : KappaSolutions.ShrinkingCylinderCover L)
    (htrivial : cover.TrivialModel) {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in _root_.Filter.atTop, ∀ H : ℝ,
      ∃ B : BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i)),
        B.witness.capTubeHasNeckChart alpha := by
  let eps := neckModelTolerance (alpha / 4) / 2
  have heps : 0 < eps := half_pos (neckModelTolerance_pos (by positivity))
  have hepslt : eps < neckModelTolerance (alpha / 4) := by
    dsimp only [eps]
    exact half_lt_self (neckModelTolerance_pos (by positivity))
  have hepssmall : eps < 1 / 11 := hepslt.trans_le (neckModelTolerance_le (alpha / 4)) |>.trans (by linarith)
  obtain ⟨_mark, _e, _hmarked, _hmetric, hnecks⟩ := exists_strongNeck_of_shrinkingCylinderCover_trivialModel L cover htrivial hscalar
  obtain ⟨nk, _hnkmap, _hnkcenter⟩ := hnecks eps heps hepssmall
  obtain ⟨C0, hC0, K, _hKregion, _hKradius, data, hKalt, _hKneck⟩ := nk.exists_canonicalWitness_of_scalar_pos
    (fun y _ => KappaSolutions.ancientKappa_scalar_pos L hL le_rfl y)
  let C1 := _root_.Max.max (sourceCurvatureBound 3 C0)
    (_root_.Max.max (4 * C0) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C0)))
  have hC1 : 1 ≤ _root_.Max.max (_root_.Max.max 9 2) C1 + 1 := by norm_num
  refine ⟨max (_root_.Max.max 9 2) C1 + 1, hC1, ?_⟩
  filter_upwards [K.eventually_neck_image_of_windowed_models hS W hdelta hreg L hcomplete hphi F hcmp
    hscalar data hKalt (by positivity : 0 < alpha / 4) (by linarith) hepslt] with i hi
  obtain ⟨Ki, _hKiCarrier, datai, hKiAlt, _hmap⟩ := hi
  intro H
  obtain ⟨B, _hBeps, _hBDomain, _hBradius, nkB, halt, _hBneck⟩ := Ki.exists_bufferedCanonical_of_neck
    (H := H) (by linarith : 2 * (alpha / 4) < alpha) datai hKiAlt
  refine ⟨B, ?_⟩
  intro cap depth hdepth
  rw [halt] at hdepth
  cases hdepth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_with_cap_tube_neck_chart_of_windowed_models_of_trivial_cylinder_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_with_cap_tube_neck_chart_of_windowed_models_of_trivial_cylinder_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_with_cap_tube_neck_chart_of_windowed_models_of_trivial_cylinder_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_with_cap_tube_neck_chart_of_windowed_models_of_trivial_cylinder_limit

theorem exists_eventually_buffered_of_windowed_models_of_trivial_cylinder_limit
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
    {kappaL : ℝ} (hL : IsAncientKappaSolution kappaL L)
    (hscalar : L.S.scalar 0 L.basepoint = 1) (cover : KappaSolutions.ShrinkingCylinderCover L)
    (htrivial : cover.TrivialModel) {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in _root_.Filter.atTop, ∀ H : ℝ,
      Nonempty (BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i))) := by
  obtain ⟨C, hC, hB⟩ :=
    exists_eventually_buffered_with_cap_tube_neck_chart_of_windowed_models_of_trivial_cylinder_limit
      hS W hdelta hreg L hcomplete hphi F hcmp hL hscalar cover htrivial ha hasmall
  refine ⟨C, hC, ?_⟩
  filter_upwards [hB] with i hi
  intro H
  obtain ⟨B, _⟩ := hi H
  exact ⟨B⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_of_windowed_models_of_trivial_cylinder_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_of_windowed_models_of_trivial_cylinder_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_of_windowed_models_of_trivial_cylinder_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_buffered_of_windowed_models_of_trivial_cylinder_limit

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
