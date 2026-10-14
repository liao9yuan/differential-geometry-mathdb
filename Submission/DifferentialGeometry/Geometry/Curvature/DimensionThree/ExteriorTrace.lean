import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorReaction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem trace_traceNormalizedCurvatureEndomorphism_metricRm04At
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ := metricRm04At g x
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      exact mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
    letI : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI targetNorm : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
    letI : ∀ y : M, SeminormedAddCommGroup (TangentSpace I y) :=
      fun y => (targetNorm y).toSeminormedAddCommGroup
    letI : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) :=
      fun y => Bundle.instInnerProductSpaceReal y
    LinearMap.trace ℝ (⋀[ℝ]^2 (TangentSpace I x))
      (exteriorPower.traceNormalizedCurvatureEndomorphism T hT).toLinearMap =
      metricScalarAt g x := by
  intro T hT
  let _ : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let targetNorm : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let _ : ∀ y : M, SeminormedAddCommGroup (TangentSpace I y) :=
    fun y => (targetNorm y).toSeminormedAddCommGroup
  let _ : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) :=
    fun y => Bundle.instInnerProductSpaceReal y
  let b := (stdOrthonormalBasis ℝ (TangentSpace I x)).reindex (finCongr hdim)
  have horth : OrthonormalBasisAt g x b.toBasis := by
    intro i j
    exact b.inner_eq_ite i j
  rw [LinearMap.trace_eq_matrix_trace ℝ (curvatureBivectorBasis b).toBasis,
    traceNormalizedCurvatureEndomorphism_toMatrix]
  exact traceNormalizedMetricCurvatureOperatorMatrixAt_trace_eq_metricScalarAt g x b.toBasis horth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.DimensionThree.trace_traceNormalizedCurvatureEndomorphism_metricRm04At then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.DimensionThree.trace_traceNormalizedCurvatureEndomorphism_metricRm04At"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.DimensionThree.trace_traceNormalizedCurvatureEndomorphism_metricRm04At ``Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.trace_traceNormalizedCurvatureEndomorphism_metricRm04At

end DifferentialGeometry.Geometry.Curvature.DimensionThree
