import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Family.Stationary
import Submission.DifferentialGeometry.Geometry.Metric.Euclidean
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection (LeviCivita)
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
def SolutionOn.const (g : SmoothRiemannianMetric I M) (D : RealTimeInterval) :
    SolutionOn (I := I) (M := M) D where
  base.metric := fun _ => g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.const ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.const

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
@[simp] theorem SolutionOn.const_metric (g : SmoothRiemannianMetric I M)
    (D : RealTimeInterval) (t : ℝ) :
    (SolutionOn.const g D).base.metric t = g := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.const_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.const_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.const_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.const_metric

theorem isSolutionOn_const_of_ricciTensor_eq_zero
    (g : SmoothRiemannianMetric I M)
    (hric : ∀ x (v w : TangentSpace I x), ricciTensor g x v w = 0)
    (D : RealTimeInterval) :
    IsSolutionOn (SolutionOn.const g D) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply isSolutionOn_of_reg (fun _ => g)
  · exact metricFamilySmoothOn_stationary g D
  · intro t _ x v w
    rw [hric, _root_.MulZeroClass.mul_zero]
    exact hasDerivAt_const t (g.inner x v w)
  · exact ((metricScalar_smooth g).continuous.comp continuous_snd).continuousOn
  · intro t _ x
    exact differentiableWithinAt_const (c := metricScalarAt g x)
  · have hc := (metricRicci g).contMDiff.continuous.comp
      (continuous_snd : Continuous (Prod.snd : {t : ℝ // t ∈ D.carrier} × M → M))
    simpa only [tensor0SFamilyContinuousOnSet, Function.comp_def, metricRicci_apply] using hc
  · have hc := (metricRm04 g).contMDiff.continuous.comp
      (continuous_snd : Continuous (Prod.snd : {t : ℝ // t ∈ D.carrier} × M → M))
    simpa only [tensor0SFamilyContinuousOnSet, Function.comp_def, metricRm04_apply] using hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_const_of_ricciTensor_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.isSolutionOn_const_of_ricciTensor_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_const_of_ricciTensor_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.isSolutionOn_const_of_ricciTensor_eq_zero

theorem isSolutionOn_const_euclidean_real (D : RealTimeInterval) :
    IsSolutionOn (SolutionOn.const (euclideanMetric (E := ℝ)) D) := by
  apply isSolutionOn_const_of_ricciTensor_eq_zero
  intro x v w
  rw [ricciTensor_apply]
  have hz : ricciEndo (euclideanMetric (E := ℝ)) x v w = 0 := by
    apply LinearMap.ext
    intro z
    exact riemannOp_eq_zero_of_finrank_le_one (LeviCivita (euclideanMetric (E := ℝ)))
      (by simp) x z v w
  rw [hz, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_const_euclidean_real then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.isSolutionOn_const_euclidean_real"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_const_euclidean_real ``Submission.DifferentialGeometry.PDE.RicciFlow.isSolutionOn_const_euclidean_real

end DifferentialGeometry.PDE.RicciFlow
