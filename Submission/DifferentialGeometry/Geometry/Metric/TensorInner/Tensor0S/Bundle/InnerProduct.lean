import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Riemannian
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Bornology
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Tensor
namespace Tensor0SRiemannian

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private instance bundleDualTopologicalSpace (s : ℕ) (b : M) :
    TopologicalSpace (Tensor0SSpace s I b →L[ℝ] ℝ) :=
  ContinuousLinearMap.topologicalSpace
    (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := Tensor0SSpace s I b) (F := ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.bundleDualTopologicalSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannian.bundleDualTopologicalSpace target :: scope.openDecls } }

private def innerModelBilin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →ₗ[ℝ] Tensor0SModel s ℝ E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun T S => covariantTensorInnerPointwise (I := I) (M := M) s g b T S)
    (fun T₁ T₂ S =>
      tensorInnerPointwise_0s_add_left (I := I) (M := M) g b s T₁ T₂ S)
    (fun c T S =>
      tensorInnerPointwise_0s_smul_left (I := I) (M := M) g b s c T S)
    (fun T S₁ S₂ =>
      tensorInnerPointwise_0s_add_right (I := I) (M := M) g b s T S₁ S₂)
    (fun c T S =>
      tensorInnerPointwise_0s_smul_right (I := I) (M := M) g b s c T S)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelBilin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelBilin target :: scope.openDecls } }

@[simp] private lemma innerModelBilin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SModel s ℝ E) :
    innerModelBilin (I := I) (M := M) g s b T S =
      covariantTensorInnerPointwise (I := I) (M := M) s g b T S := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelBilin_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelBilin_apply target :: scope.openDecls } }

private def innerModelLinearOuter
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →ₗ[ℝ] (Tensor0SModel s ℝ E →L[ℝ] ℝ) where
  toFun := fun T =>
    LinearMap.toContinuousLinearMap
      (innerModelBilin (I := I) (M := M) g s b T)
  map_add' := fun T₁ T₂ => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change covariantTensorInnerPointwise (I := I) (M := M) s g b (T₁ + T₂) S =
      covariantTensorInnerPointwise (I := I) (M := M) s g b T₁ S +
        covariantTensorInnerPointwise (I := I) (M := M) s g b T₂ S
    exact tensorInnerPointwise_0s_add_left (I := I) (M := M) g b s T₁ T₂ S
  map_smul' := fun c T => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change covariantTensorInnerPointwise (I := I) (M := M) s g b (c • T) S =
      c • covariantTensorInnerPointwise (I := I) (M := M) s g b T S
    rw [tensorInnerPointwise_0s_smul_left]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelLinearOuter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelLinearOuter target :: scope.openDecls } }

def innerModelCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (innerModelLinearOuter (I := I) (M := M) g s b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelCLM ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelCLM

@[simp] lemma innerModelCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SModel s ℝ E) :
    innerModelCLM (I := I) (M := M) g s b T S =
      covariantTensorInnerPointwise (I := I) (M := M) s g b T S := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelCLM_apply ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelCLM_apply

private def bundleCLE (s : ℕ) (b : M) :
    Tensor0SSpace s I b ≃L[ℝ]
      Tensor0SModel s ℝ E :=
  Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (𝕜 := ℝ) (E := E) (I := I) (M := M) s b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.bundleCLE
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannian.bundleCLE target :: scope.openDecls } }

private def bundleToModelCLM (s : ℕ) (b : M) :
    Tensor0SSpace s I b →L[ℝ]
      Tensor0SModel s ℝ E :=
  (bundleCLE (I := I) (M := M) (E := E) s b).toContinuousLinearMap

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.bundleToModelCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannian.bundleToModelCLM target :: scope.openDecls } }

@[simp] private lemma bundleToModelCLM_apply (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) :
    bundleToModelCLM (I := I) (M := M) (E := E) s b T =
      Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.bundleToModelCLM_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannian.bundleToModelCLM_apply target :: scope.openDecls } }

private def modelToBundleCLM (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →L[ℝ]
      Tensor0SSpace s I b :=
  (bundleCLE (I := I) (M := M) (E := E) s b).symm.toContinuousLinearMap

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.modelToBundleCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannian.modelToBundleCLM target :: scope.openDecls } }

private def precompBundleCLM (s : ℕ) (b : M) :
    (Tensor0SModel s ℝ E →L[ℝ] ℝ) →L[ℝ]
      (Tensor0SSpace s I b →L[ℝ] ℝ) :=
  ((bundleCLE (I := I) (M := M) (E := E) s b).symm.arrowCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)).toContinuousLinearMap

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.precompBundleCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannian.precompBundleCLM target :: scope.openDecls } }

@[simp] private lemma precompBundleCLM_apply (s : ℕ) (b : M)
    (f : Tensor0SModel s ℝ E →L[ℝ] ℝ) (T : Tensor0SSpace s I b) :
    precompBundleCLM (I := I) (M := M) (E := E) s b f T =
      f (Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T) :=
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.precompBundleCLM_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Tensor0SRiemannian.precompBundleCLM_apply target :: scope.openDecls } }

def innerBundleCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SSpace s I b →L[ℝ]
      Tensor0SSpace s I b →L[ℝ] ℝ :=
  let modelPairing : Tensor0SModel s ℝ E →L[ℝ] (Tensor0SSpace s I b →L[ℝ] ℝ) :=
    (precompBundleCLM (I := I) (M := M) (E := E) s b).comp
      (innerModelCLM (I := I) (M := M) g s b)
  modelPairing.comp (bundleToModelCLM (I := I) (M := M) (E := E) s b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM

@[simp] lemma innerBundleCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    innerBundleCLM (I := I) (M := M) g s b T S =
      covariantTensorInnerPointwise (I := I) (M := M) s g b
        (Tensor0SBundle.Tensor0SSpace.toModel (I := I) (M := M)
          (𝕜 := ℝ) (E := E) (s := s) (x := b) T)
        (Tensor0SBundle.Tensor0SSpace.toModel (I := I) (M := M)
          (𝕜 := ℝ) (E := E) (s := s) (x := b) S) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM_apply ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM_apply

lemma innerBundleCLM_symm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    innerBundleCLM (I := I) (M := M) g s b T S =
      innerBundleCLM (I := I) (M := M) g s b S T := by
  rw [innerBundleCLM_apply, innerBundleCLM_apply]
  exact tensorInnerPointwise_0s_symm (I := I) (M := M) g b s _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM_symm ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM_symm

lemma innerBundleCLM_pos
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) (hT : T ≠ 0) :
    0 < innerBundleCLM (I := I) (M := M) g s b T T := by
  rw [innerBundleCLM_apply]
  have hTm :
      Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T ≠ 0 := by
    intro h
    apply hT
    have hinj :=
      Tensor0SBundle.Tensor0SSpace.toModel_injective
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
    have hzero :
        Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (0 : Tensor0SSpace s I b) = 0 :=
      Tensor0SBundle.Tensor0SSpace.toModel_zero
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
    exact hinj (h.trans hzero.symm)
  have hnn :
      0 ≤ covariantTensorInnerPointwise (I := I) (M := M) s g b
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T)
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T) :=
    tensorInnerPointwise_0s_nonneg (I := I) (M := M) g b s _
  rcases lt_or_eq_of_le hnn with hlt | heq
  · exact hlt
  · exfalso
    apply hTm
    exact (tensorInnerPointwise_0s_eq_zero_iff
      (I := I) (M := M) g b s _).mp heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM_pos ``Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian.innerBundleCLM_pos

end Tensor0SRiemannian
end Tensor
end DifferentialGeometry

end
