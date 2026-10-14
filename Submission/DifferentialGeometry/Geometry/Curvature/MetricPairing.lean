import Submission.DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

private instance instContMDiffMetricCov (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivative (metricCov (I := I) g) ∞ :=
  CovariantDerivative.contMDiffCovariantDerivativeOn_univ_iff.mp
    (metricCov_smooth (I := I) g isOpen_univ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instContMDiffMetricCov
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instContMDiffMetricCov target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem metricRm04At_inner (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04At (I := I) g x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) =
      g.inner x
        (DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g) x X Y Z)
        W := by
  have h :=
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_apply_const
      (I := I) g (metricCov (I := I) g) (metricCov_smooth (I := I) g) X Y Z W
  rw [DifferentialGeometry.connectionRiemannCurvatureField_tangentConst_eq_riemannOp
    (I := I) (metricCov (I := I) g) (metricCov_smooth (I := I) g) x X Y Z] at h
  rw [show metricRm04At (I := I) g x =
      DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
        (I := I) g (metricCov (I := I) g) (metricCov_smooth (I := I) g) x from rfl, h]
  exact g.symm x W _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricRm04At_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricRm04At_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricRm04At_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.metricRm04At_inner


end DifferentialGeometry.PDE.RicciFlow
