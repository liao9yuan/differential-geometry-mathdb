import Submission.DifferentialGeometry.Geometry.Connection.MetricTrace.Iterated
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.IteratedCovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Operator.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem normSq_hessian_metricTrace_le
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) ∞ 2) (x : M) :
    normSq0S g x 2
      (hessianSec (I := I) (leviCivitaConnectionOfMetric g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally g)
        (fun y => metricTracePair0SAt g (A y)) (trace02_smooth g A) x) ≤
      (Module.finrank ℝ E : ℝ) ^ 4 * normSq0S g x 4 (iterCov g 2 A 2 x) := by
  let B := metricTraceFirstTwoField g A
  have hB : ∀ y, B y Fin.elim0 = metricTracePair0SAt g (A y) := by
    intro y
    dsimp only [B]
    rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
      traceFirstTwo_elim0]
  have heq := iterCov_zeroTensor_two_eq_hessianSec g B
    (fun y => metricTracePair0SAt g (A y)) (trace02_smooth g A) hB
  have hbound := iterCov_metricTrace_normSq_le g A 2 x
  change normSq0S g x 2 (iterCov g 0 B 2 x) ≤
    (Module.finrank ℝ E : ℝ) ^ 4 * normSq0S g x 4 (iterCov g 2 A 2 x) at hbound
  rw [heq] at hbound
  exact hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normSq_hessian_metricTrace_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normSq_hessian_metricTrace_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normSq_hessian_metricTrace_le ``Submission.DifferentialGeometry.Geometry.Operator.normSq_hessian_metricTrace_le

theorem sqrt_normSq_hessian_metricTrace_le
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) ∞ 2) (x : M) :
    Real.sqrt (normSq0S g x 2
      (hessianSec (I := I) (leviCivitaConnectionOfMetric g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally g)
        (fun y => metricTracePair0SAt g (A y)) (trace02_smooth g A) x)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        Real.sqrt (normSq0S g x 4 (iterCov g 2 A 2 x)) := by
  have hbound := Real.sqrt_le_sqrt (normSq_hessian_metricTrace_le g A x)
  have hp : (Module.finrank ℝ E : ℝ) ^ 4 = ((Module.finrank ℝ E : ℝ) ^ 2) ^ 2 := by
    ring
  rwa [hp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)] at hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.sqrt_normSq_hessian_metricTrace_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.sqrt_normSq_hessian_metricTrace_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.sqrt_normSq_hessian_metricTrace_le ``Submission.DifferentialGeometry.Geometry.Operator.sqrt_normSq_hessian_metricTrace_le

end DifferentialGeometry.Geometry.Operator
