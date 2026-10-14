import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalCoverNoncollapse
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelNoncollapse
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceProductNoncollapse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  [LocallyPathConnectedSpace N] [SemilocallySimplyConnectedSpace N] [Inhabited N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance universalCoverSplitC1N : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitC1N
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitC1N target :: scope.openDecls } }

private local instance universalCoverSplitC1M : IsManifold (𝓡 2) 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitC1M
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitC1M target :: scope.openDecls } }

private local instance universalCoverSplitC1Cover : IsManifold I 1 (UniversalCover N) :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitC1Cover
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitC1Cover target :: scope.openDecls } }

private local instance universalCoverSplitMeasurableN : MeasurableSpace N := borel N

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitMeasurableN
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitMeasurableN target :: scope.openDecls } }
private local instance universalCoverSplitBorelN : BorelSpace N := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitBorelN
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitBorelN target :: scope.openDecls } }
private local instance universalCoverSplitMeasurableM : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitMeasurableM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitMeasurableM target :: scope.openDecls } }
private local instance universalCoverSplitBorelM : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitBorelM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCoverSplitBorelM target :: scope.openDecls } }

theorem universalCover_split_surface_tensor_half_noncollapsed
    (g : SmoothRiemannianMetric I N) (hdim : Module.finrank ℝ E = 3)
    (h : SmoothRiemannianMetric (𝓡 2) M)
    (Phi : (M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover N)
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) g).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
        h.inner y v w + a * c)
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hnoncollapse : ∀ (p : N) (rho : ℝ), 0 < rho →
      (∀ z ∈ riemannianBallOf (I := I) g p rho,
        rho ^ 4 * normSq0S (I := I) g z 4 (metricRm04At (I := I) g z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := N) g
          (riemannianBallOf (I := I) g p rho))
    (y : M) (r : ℝ) (hr : 0 < r)
    (hcurvature : ∀ z ∈ riemannianBallOf (I := 𝓡 2) h y r,
      r ^ 4 * normSq0S (I := 𝓡 2) h z 4 (metricRm04At (I := 𝓡 2) h z) ≤ 1) :
    ENNReal.ofReal (kappa / 2) * ENNReal.ofReal r ^ 2 ≤
      riemannianVolumeMeasure (I := 𝓡 2) (M := M) h
        (riemannianBallOf (I := 𝓡 2) h y r) := by
  let : SigmaCompactSpace (UniversalCover N) :=
    Phi.toHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  let gP : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ, ℝ)) (M × ℝ) :=
    Diffeomorph.pullbackMetricCross (UniversalCover.liftedMetric (I := I) g) Phi
  have hprod : ∀ (p : M × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p),
      gP.inner p v w = h.inner p.1 v.1 w.1 + v.2 * w.2 := by
    rintro ⟨z, s⟩ v w
    change (Diffeomorph.pullbackMetricCross
      (UniversalCover.liftedMetric (I := I) g) Phi).inner (z, s) v w = _
    rw [Diffeomorph.pullbackMetricCross_inner]
    exact hproduct z s v.1 w.1 v.2 w.2
  have hcover : ∀ (p : UniversalCover N) (rho : ℝ), 0 < rho →
      (∀ z ∈ riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) p rho,
        rho ^ 4 * normSq0S (I := I) (UniversalCover.liftedMetric (I := I) g) z 4
          (metricRm04At (I := I) (UniversalCover.liftedMetric (I := I) g) z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal rho ^ 3 ≤
        riemannianVolumeMeasure (I := I) (M := UniversalCover N)
          (UniversalCover.liftedMetric (I := I) g)
          (riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) p rho) := by
    intro p rho hrho hRm
    simpa only [hdim] using
      universalCover_tensor_noncollapsed g kappa hnoncollapse p rho hrho hRm
  have hproductNC : ∀ (p : M × ℝ) (rho : ℝ), 0 < rho →
      (∀ z : M × ℝ,
        riemannianEDistOf (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p z < ENNReal.ofReal rho →
        rho ^ 4 * normSq0S (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP z 4
          (metricRm04At (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal rho ^ 3 ≤
        riemannianVolumeMeasure (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (M := M × ℝ) gP
          {z : M × ℝ |
            riemannianEDistOf (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p z < ENNReal.ofReal rho} := by
    intro p rho hrho hRm
    exact tensor_noncollapsed_pullbackMetricCross
      (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (J := I)
      (UniversalCover.liftedMetric (I := I) g) Phi kappa 3 hcover p rho hrho hRm
  exact surfaceProduct_tensor_half_noncollapsed h gP hprod kappa hkappa
    hproductNC y r hr hcurvature

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_split_surface_tensor_half_noncollapsed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_split_surface_tensor_half_noncollapsed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_split_surface_tensor_half_noncollapsed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_split_surface_tensor_half_noncollapsed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
