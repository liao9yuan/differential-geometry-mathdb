import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.VolumeNaturality
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [CompactSpace N]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace N := borel N

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry_1 : BorelSpace N := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealOfNatWithTopENat_differentialGeometry : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealOfNatWithTopENat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealOfNatWithTopENat_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1 : IsManifold I 1 N := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1 target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem integral_pullbackMetric_comp
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) (f : N → ℝ) :
    (∫ x, f (Phi x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) (Diffeomorph.pullbackMetric g Phi))) =
      ∫ y, f y ∂(riemannianVolumeMeasure (I := I) (M := N) g) :=
  (volumeMeasurePreserving_pullbackMetric g Phi).integral_comp
    Phi.toHomeomorph.measurableEmbedding f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integral_pullbackMetric_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integral_pullbackMetric_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integral_pullbackMetric_comp ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integral_pullbackMetric_comp


omit [CompleteSpace E] in
theorem surfaceArea_pullbackMetric
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) :
    surfaceArea (Diffeomorph.pullbackMetric g Phi) = surfaceArea g := by
  have h := integral_pullbackMetric_comp g Phi (fun _ => (1 : ℝ))
  simpa only [_root_.MeasureTheory.integral_const, smul_eq_mul, mul_one, surfaceArea] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_pullbackMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_pullbackMetric

variable [BoundarylessManifold I M] [BoundarylessManifold I N]


theorem totalScalarCurvature_pullbackMetric
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) :
    totalScalarCurvature (Diffeomorph.pullbackMetric g Phi) = totalScalarCurvature g := by
  unfold totalScalarCurvature
  simp_rw [metricScalarAt_pullback]
  exact integral_pullbackMetric_comp g Phi (fun y => metricScalarAt (I := I) g y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_pullbackMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_pullbackMetric

theorem surfaceEntropy_pullbackMetric
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) :
    surfaceEntropy (Diffeomorph.pullbackMetric g Phi) = surfaceEntropy g := by
  unfold surfaceEntropy
  simp_rw [metricScalarAt_pullback, surfaceArea_pullbackMetric]
  exact integral_pullbackMetric_comp g Phi
    (fun y => metricScalarAt (I := I) g y *
      Real.log (metricScalarAt (I := I) g y * surfaceArea g))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_pullbackMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_pullbackMetric

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
