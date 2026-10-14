import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Naturality
import Submission.DifferentialGeometry.Analysis.Integration.Measure.ModelChange
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

theorem redDensity_transContinuousLinearEquiv
    (S : SolutionOn (I := I) (M := M) D) (e : E ≃L[ℝ] F)
    (T : ℝ) (x y : M) (tau : ℝ) :
    redDensity (S.pullback (ContinuousLinearEquiv.toTransContinuousLinearEquiv
      (n := ∞) I M e).symm) T x y tau = redDensity S T x y tau := by
  have hcost := lCost_pullback_cross S
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm T x y tau
  change lCost (S.pullback (ContinuousLinearEquiv.toTransContinuousLinearEquiv
    (n := ∞) I M e).symm) T x y tau = lCost S T x y tau at hcost
  unfold redDensity redLength
  rw [hcost, ← e.toLinearEquiv.finrank_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_transContinuousLinearEquiv ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_transContinuousLinearEquiv

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

theorem redVolume_transContinuousLinearEquiv [SigmaCompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (e : E ≃L[ℝ] F)
    (T : ℝ) (x : M) (tau : ℝ) :
    redVolume (S.pullback (ContinuousLinearEquiv.toTransContinuousLinearEquiv
      (n := ∞) I M e).symm) T x tau = redVolume S T x tau := by
  unfold redVolume
  simp_rw [redDensity_transContinuousLinearEquiv]
  change (∫⁻ y, ENNReal.ofReal (redDensity S T x y tau)
    ∂riemannianVolumeMeasure (I := I.transContinuousLinearEquiv e)
      (M := M) ((S.base.metric (T - tau)).transContinuousLinearEquiv e)) = _
  rw [riemannianVolumeMeasure_transContinuousLinearEquiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_transContinuousLinearEquiv ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_transContinuousLinearEquiv

end DifferentialGeometry.PDE.RicciFlow.Perelman
