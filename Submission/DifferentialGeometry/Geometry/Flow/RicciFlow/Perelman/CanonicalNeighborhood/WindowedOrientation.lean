import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedArmCapture
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalOrientation
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Exhaustion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
  [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem WindowedModelWitness.orientable_limit_of_orientable_sources
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0))
    (hreg : ∀ i s, s ∈ _root_.Set.Ioo (-modelDepth (delta i)) 0 →
      parabolicTime (t i) ((S i).scalar (t i) (x i)) s ∈ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hL : IsAncientKappaSolution kappa L)
    (o : ∀ i, TangentOrientationSection (M i))
    {phi : ℕ → ℕ} (hphi : _root_.Filter.Tendsto phi _root_.Filter.atTop _root_.Filter.atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ B : ℝ, 0 < B → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (_root_.Set.Icc (-B) 0) order eta)) :
    Nonempty (TangentOrientationSection L.M) := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let _ : ConnectedSpace L.M := hL.connected
  have hcomplete : MetricComplete (L.atTime 0) :=
    hL.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl)
  let Psi : ∀ i, PartialDiffeomorph I3 I3 L.M (M (phi i)) ∞ := fun i =>
    partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  let X : PointedRiemannianSeq.{u, 0, 0} I3 := ⟨fun i => {
    M := M i
    basepoint := x i
    metric := rescaledMetric (S i) (t i) ((S i).scalar (t i) (x i)) (W i).scalar_pos 0 }⟩
  have hbasePsi (i : ℕ) : Psi i L.basepoint = x (phi i) := by
    change (W (phi i)).embedding (F.map i L.basepoint) = x (phi i)
    rw [show F.map i L.basepoint = (W (phi i)).model.basepoint from F.basepoint_map i]
    exact (W (phi i)).base_map
  have hsource : ∀ K : Set L.M, IsCompact K → ∀ᶠ i in _root_.Filter.atTop, K ⊆ (Psi i).source := by
    intro K hK
    exact (WindowedModelWitness.eventually_composed_comparison hS W hdelta hreg L hcomplete
      hphi F hcmp hK zero_lt_one 0 zero_lt_one).mono fun _ hi => hi.1
  let _ : PreconnectedSpace (L.atTime 0).M := inferInstanceAs (PreconnectedSpace L.M)
  obtain ⟨sigma, hsigma, G, _, _, hconn⟩ :=
    PointedRiemannianConvergenceMaps.exists_subsequence_of_eventually_contains_compacts
      (X := X) (P := L.atTime 0) (f := phi) Psi hbasePsi hsource
  obtain ⟨_, _, O, _⟩ := exists_subsequence_preserves_tangentOrientation G
    (fun i => (hconn i).isPreconnected) o
  exact ⟨O⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.orientable_limit_of_orientable_sources then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.orientable_limit_of_orientable_sources"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.orientable_limit_of_orientable_sources ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.orientable_limit_of_orientable_sources

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
