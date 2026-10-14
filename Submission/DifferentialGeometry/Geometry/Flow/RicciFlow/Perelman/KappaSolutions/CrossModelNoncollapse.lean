import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelBallTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelCurvatureTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance crossModelNoncollapseMeasurableM : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelNoncollapseMeasurableM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelNoncollapseMeasurableM target :: scope.openDecls } }
private local instance crossModelNoncollapseBorelM : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelNoncollapseBorelM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelNoncollapseBorelM target :: scope.openDecls } }
private local instance crossModelNoncollapseMeasurableN : MeasurableSpace N := borel N

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelNoncollapseMeasurableN
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelNoncollapseMeasurableN target :: scope.openDecls } }
private local instance crossModelNoncollapseBorelN : BorelSpace N := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelNoncollapseBorelN
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelNoncollapseBorelN target :: scope.openDecls } }
private local instance crossModelNoncollapseC1M : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelNoncollapseC1M
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelNoncollapseC1M target :: scope.openDecls } }
private local instance crossModelNoncollapseC1N : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelNoncollapseC1N
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelNoncollapseC1N target :: scope.openDecls } }

theorem tensor_noncollapsed_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (kappa : ℝ) (n : ℕ)
    (hnoncollapse : ∀ (p : N) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf (I := J) g p r,
        r ^ 4 * normSq0S (I := J) g y 4 (metricRm04At (I := J) g y) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ n ≤
        riemannianVolumeMeasure (I := J) (M := N) g
          (riemannianBallOf (I := J) g p r))
    (x : M) (r : ℝ) (hr : 0 < r)
    (hcurvature : ∀ y ∈
      riemannianBallOf (I := I) (Diffeomorph.pullbackMetricCross g Phi) x r,
      r ^ 4 * normSq0S (I := I) (Diffeomorph.pullbackMetricCross g Phi) y 4
        (metricRm04At (I := I) (Diffeomorph.pullbackMetricCross g Phi) y) ≤ 1) :
    ENNReal.ofReal kappa * ENNReal.ofReal r ^ n ≤
      riemannianVolumeMeasure (I := I) (M := M)
        (Diffeomorph.pullbackMetricCross g Phi)
        (riemannianBallOf (I := I) (Diffeomorph.pullbackMetricCross g Phi) x r) := by
  rw [riemannianBallOf_volume_pullbackMetricCross]
  apply hnoncollapse (Phi x) r hr
  intro y hy
  rw [← image_riemannianBallOf_pullbackMetricCross g Phi x r] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  simpa only [metricRmNormSq_pullbackCross] using hcurvature z hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor_noncollapsed_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor_noncollapsed_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor_noncollapsed_pullbackMetricCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tensor_noncollapsed_pullbackMetricCross

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
