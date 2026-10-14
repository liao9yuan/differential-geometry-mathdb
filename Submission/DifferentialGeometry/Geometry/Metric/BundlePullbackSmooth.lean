import Submission.DifferentialGeometry.Bundle.Hom
import Submission.DifferentialGeometry.Geometry.Metric.BundlePullback
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

namespace Bundle.ContMDiffRiemannianMetric
open _root_.Bundle _root_.Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  {FV FW : Type*} [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW]
  {V W : B → Type*} [TopologicalSpace (TotalSpace FV V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle FV V] [VectorBundle ℝ FV V]
  [TopologicalSpace (TotalSpace FW W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  {n : ℕ∞ω}

open _root_.Bundle _root_.Bundle.ContMDiffRiemannianMetric in
def pullbackFiberwiseContinuousLinearEquiv
    (g : _root_.Bundle.ContMDiffRiemannianMetric I n FW W) (e : ∀ x, V x ≃L[ℝ] W x)
    (he : ContMDiff I (I.prod 𝓘(ℝ, FV →L[ℝ] FW)) n
      (fun x => (⟨x, (e x).toContinuousLinearMap⟩ :
        _root_.Bundle.TotalSpace (FV →L[ℝ] FW) (fun x => V x →L[ℝ] W x)))) :
    _root_.Bundle.ContMDiffRiemannianMetric I n FV V where
  inner := (g.toRiemannianMetric.pullback id e).inner
  symm := (g.toRiemannianMetric.pullback id e).symm
  pos := (g.toRiemannianMetric.pullback id e).pos
  isVonNBounded := (g.toRiemannianMetric.pullback id e).isVonNBounded
  contMDiff := by
    let : _root_.Bundle.RiemannianBundle W := ⟨g.toRiemannianMetric⟩
    let : _root_.Bundle.RiemannianBundle V := ⟨g.toRiemannianMetric.pullback id e⟩
    have h := g.contMDiff.clm_bundle_bilinearComp he he
    exact h.congr fun x => by
      apply TotalSpace.mk_inj.mpr
      ext v w
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.ContMDiffRiemannianMetric.pullbackFiberwiseContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration Bundle.ContMDiffRiemannianMetric.pullbackFiberwiseContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.ContMDiffRiemannianMetric.pullbackFiberwiseContinuousLinearEquiv ``Submission.Bundle.ContMDiffRiemannianMetric.pullbackFiberwiseContinuousLinearEquiv

open _root_.Bundle _root_.Bundle.ContMDiffRiemannianMetric in
@[simp]
theorem pullbackFiberwiseContinuousLinearEquiv_inner
    (g : _root_.Bundle.ContMDiffRiemannianMetric I n FW W) (e : ∀ x, V x ≃L[ℝ] W x)
    (he : ContMDiff I (I.prod 𝓘(ℝ, FV →L[ℝ] FW)) n
      (fun x => (⟨x, (e x).toContinuousLinearMap⟩ :
        _root_.Bundle.TotalSpace (FV →L[ℝ] FW) (fun x => V x →L[ℝ] W x))))
    (x : B) (v w : V x) :
    (g.pullbackFiberwiseContinuousLinearEquiv e he).inner x v w =
      g.inner x (e x v) (e x w) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.ContMDiffRiemannianMetric.pullbackFiberwiseContinuousLinearEquiv_inner then
    throwError "Refusing to shadow existing declaration Bundle.ContMDiffRiemannianMetric.pullbackFiberwiseContinuousLinearEquiv_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.ContMDiffRiemannianMetric.pullbackFiberwiseContinuousLinearEquiv_inner ``Submission.Bundle.ContMDiffRiemannianMetric.pullbackFiberwiseContinuousLinearEquiv_inner

open _root_.Bundle _root_.Bundle.ContMDiffRiemannianMetric in
@[simp]
theorem pullbackFiberwiseContinuousLinearEquiv_toRiemannianMetric
    (g : _root_.Bundle.ContMDiffRiemannianMetric I n FW W) (e : ∀ x, V x ≃L[ℝ] W x)
    (he : ContMDiff I (I.prod 𝓘(ℝ, FV →L[ℝ] FW)) n
      (fun x => (⟨x, (e x).toContinuousLinearMap⟩ :
        _root_.Bundle.TotalSpace (FV →L[ℝ] FW) (fun x => V x →L[ℝ] W x)))) :
    (g.pullbackFiberwiseContinuousLinearEquiv e he).toRiemannianMetric =
      g.toRiemannianMetric.pullback id e := by
  apply RiemannianMetric.ext
  intro x v w
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.ContMDiffRiemannianMetric.pullbackFiberwiseContinuousLinearEquiv_toRiemannianMetric then
    throwError "Refusing to shadow existing declaration Bundle.ContMDiffRiemannianMetric.pullbackFiberwiseContinuousLinearEquiv_toRiemannianMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.ContMDiffRiemannianMetric.pullbackFiberwiseContinuousLinearEquiv_toRiemannianMetric ``Submission.Bundle.ContMDiffRiemannianMetric.pullbackFiberwiseContinuousLinearEquiv_toRiemannianMetric

end Bundle.ContMDiffRiemannianMetric
