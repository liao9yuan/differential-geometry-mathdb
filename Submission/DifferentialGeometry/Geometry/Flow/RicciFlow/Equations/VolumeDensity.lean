import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.ScalarTrace
import Submission.DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

namespace PDE.RicciFlow

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem traceTimeDerivMetric_eq_neg_two_scalar_of_ricciFlow
    (g : ℝ → SmoothRiemannianMetric I M) {t : ℝ}
    (hpde : ∀ (x : M) (v w : TangentSpace I x),
      HasDerivAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (I := I) (g t) x v w) t) (x : M) :
    traceTimeDerivMetric (I := I) g t x = -2 * metricScalarAt (g t) x := by
  classical
  have hscalar := metricScalar_chartTrace_eq (g t) x
    (self_mem_chartLeviCivitaGoodSet (I := I) (α := x))
  have hx : (extChartAt I x).symm (extChartAt I x x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source x)
  simp only [chartInvGramOnE_def, hx, chartInvGramMatrix] at hscalar
  have hd (i j : Fin (Module.finrank ℝ E)) :
      deriv (fun s => chartGramMatrix (I := I) (g s) x x i j) t =
        -2 * ricciTensor (I := I) (g t) x
          (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x) := by
    simpa only [chartGramMatrix_apply] using
      (hpde x (chartBasisVecFiber (I := I) x i x)
        (chartBasisVecFiber (I := I) x j x)).deriv
  rw [traceTimeDerivMetric_eq, Matrix.trace_mul_comm, hscalar]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, hd]
  have hsymm (i j : Fin (Module.finrank ℝ E)) :
      ((chartGramMatrix (I := I) (g t) x x)⁻¹) j i =
        ((chartGramMatrix (I := I) (g t) x x)⁻¹) i j := by
    have hh := (chartGramMatrix_isHermitian (I := I) (g t) x x).inv
    simpa only [_root_.TrivialStar.star_trivial] using hh.apply i j
  simp_rw [hsymm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.traceTimeDerivMetric_eq_neg_two_scalar_of_ricciFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.traceTimeDerivMetric_eq_neg_two_scalar_of_ricciFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.traceTimeDerivMetric_eq_neg_two_scalar_of_ricciFlow ``Submission.DifferentialGeometry.PDE.RicciFlow.traceTimeDerivMetric_eq_neg_two_scalar_of_ricciFlow

end PDE.RicciFlow

end DifferentialGeometry
