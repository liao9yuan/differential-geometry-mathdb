import Submission.DifferentialGeometry.Geometry.Metric.BundlePullback
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorConjugation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousConstSMul ℝ (V x)]

theorem traceNormalizedCurvatureEndomorphism_metric_pullback_eq_conjugate
    (g : SmoothRiemannianMetric I M) (h : _root_.Bundle.RiemannianMetric V)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ∀ x v w, g.inner x (ι x v) (ι x w) = h.inner x v w) (x : M) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ := metricRm04At g x
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      exact mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
    let e := g.toRiemannianMetric.toLinearIsometryEquiv h id ι hι x
    letI : FiniteDimensional ℝ (V x) := (ι x).symm.toLinearEquiv.finiteDimensional
    letI : _root_.Bundle.RiemannianBundle V := ⟨h⟩
    letI sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
    letI : ∀ y, SeminormedAddCommGroup (V y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
    letI : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
    letI : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI targetNorm : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
    letI : ∀ y : M, SeminormedAddCommGroup (TangentSpace I y) :=
      fun y => (targetNorm y).toSeminormedAddCommGroup
    letI : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) :=
      fun y => Bundle.instInnerProductSpaceReal y
    let F₂ := exteriorPower.mapLinearIsometryEquiv 2 e
    let Rg := exteriorPower.traceNormalizedCurvatureEndomorphism T hT
    let Rbar := exteriorPower.traceNormalizedCurvatureEndomorphism
      (T.compContinuousLinearMap (fun _ => (ι x).toContinuousLinearMap))
      (hT.compContinuousLinearMap (ι x).toContinuousLinearMap)
    e.toContinuousLinearEquiv = ι x ∧
      Rbar = F₂.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (Rg.comp F₂.toContinuousLinearEquiv.toContinuousLinearMap) ∧
      (∀ a b c d : V x,
        ⟪Rbar (exteriorPower.ιMulti ℝ 2 ![a, b]), exteriorPower.ιMulti ℝ 2 ![c, d]⟫ =
          2 * T ![ι x a, ι x b, ι x d, ι x c]) ∧
      IsSelfAdjoint Rbar := by
  intro T hT e F₂ Rg Rbar
  let _ : FiniteDimensional ℝ (V x) := (ι x).symm.toLinearEquiv.finiteDimensional
  let _ : _root_.Bundle.RiemannianBundle V := ⟨h⟩
  let sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let _ : ∀ y, SeminormedAddCommGroup (V y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
  let _ : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let targetNorm : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let _ : ∀ y : M, SeminormedAddCommGroup (TangentSpace I y) :=
    fun y => (targetNorm y).toSeminormedAddCommGroup
  let _ : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) :=
    fun y => Bundle.instInnerProductSpaceReal y
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · exact exteriorPower.traceNormalizedCurvatureEndomorphism_pullback_eq_conjugate e T hT
  · intro a b c d
    rw [exteriorPower.inner_traceNormalizedCurvatureEndomorphism_ιMulti]
    congr 1
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureEndomorphism_metric_pullback_eq_conjugate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureEndomorphism_metric_pullback_eq_conjugate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureEndomorphism_metric_pullback_eq_conjugate ``Submission.DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureEndomorphism_metric_pullback_eq_conjugate

end DifferentialGeometry.Geometry.Curvature
