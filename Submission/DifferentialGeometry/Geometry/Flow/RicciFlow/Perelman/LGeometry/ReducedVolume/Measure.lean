import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)
open scoped _root_.ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : Geometry.Curvature.RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry target :: scope.openDecls } }

def redVolume (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (tau : ℝ) :
    ENNReal :=
  ∫⁻ y, ENNReal.ofReal (redDensity S T x y tau)
    ∂riemannianVolumeMeasure I M (S.base.metric (T - tau))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume

def redDensityMeasure (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (tau : ℝ) :
    Measure M :=
  (riemannianVolumeMeasure I M (S.base.metric (T - tau))).withDensity
    (fun y => ENNReal.ofReal (redDensity S T x y tau))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensityMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redDensityMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensityMeasure ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redDensityMeasure

@[simp]
theorem redDensityMeasure_apply (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ) {A : Set M} (hA : MeasurableSet A) :
    redDensityMeasure S T x tau A =
      ∫⁻ y in A, ENNReal.ofReal (redDensity S T x y tau)
        ∂riemannianVolumeMeasure I M (S.base.metric (T - tau)) :=
  _root_.MeasureTheory.withDensity_apply _ hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensityMeasure_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redDensityMeasure_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensityMeasure_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redDensityMeasure_apply

theorem redDensityMeasure_univ (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ) :
    redDensityMeasure S T x tau Set.univ = redVolume S T x tau := by
  rw [redDensityMeasure_apply _ _ _ _ MeasurableSet.univ]
  exact MeasureTheory.setLIntegral_univ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensityMeasure_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redDensityMeasure_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensityMeasure_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redDensityMeasure_univ

end DifferentialGeometry.PDE.RicciFlow.Perelman
