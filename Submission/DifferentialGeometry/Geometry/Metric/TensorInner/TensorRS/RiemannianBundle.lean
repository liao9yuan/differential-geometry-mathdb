import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Bundle.SectionRegularity
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Bundle.Riemannian
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SInnerSectionContinuity
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.TensorRS.Riemannian
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian

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
namespace TensorRSRiemannianBundle

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def innerModelBilinRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    TensorRSModel r s ℝ E →ₗ[ℝ] TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun T S => tensorInnerPointwise (I := I) (M := M) g r s b T S)
    (fun T₁ T₂ S =>
      tensorInnerPointwise_add_left (I := I) (M := M) g r s b T₁ T₂ S)
    (fun c T S =>
      tensorInnerPointwise_smul_left (I := I) (M := M) g r s b c T S)
    (fun T S₁ S₂ =>
      tensorInnerPointwise_add_right (I := I) (M := M) g r s b T S₁ S₂)
    (fun c T S =>
      tensorInnerPointwise_smul_right (I := I) (M := M) g r s b c T S)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelBilinRS
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelBilinRS target :: scope.openDecls } }

@[simp] private lemma innerModelBilinRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) :
    innerModelBilinRS (I := I) (M := M) g r s b T S =
      tensorInnerPointwise (I := I) (M := M) g r s b T S := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelBilinRS_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelBilinRS_apply target :: scope.openDecls } }

private def innerModelLinearOuterRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    TensorRSModel r s ℝ E →ₗ[ℝ] (TensorRSModel r s ℝ E →L[ℝ] ℝ) where
  toFun := fun T =>
    LinearMap.toContinuousLinearMap
      (innerModelBilinRS (I := I) (M := M) g r s b T)
  map_add' := fun T₁ T₂ => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change tensorInnerPointwise (I := I) (M := M) g r s b (T₁ + T₂) S =
      tensorInnerPointwise (I := I) (M := M) g r s b T₁ S +
        tensorInnerPointwise (I := I) (M := M) g r s b T₂ S
    exact tensorInnerPointwise_add_left (I := I) (M := M) g r s b T₁ T₂ S
  map_smul' := fun c T => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change tensorInnerPointwise (I := I) (M := M) g r s b (c • T) S =
      c • tensorInnerPointwise (I := I) (M := M) g r s b T S
    rw [tensorInnerPointwise_smul_left]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelLinearOuterRS
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelLinearOuterRS target :: scope.openDecls } }

def innerModelCLMRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (innerModelLinearOuterRS (I := I) (M := M) g r s b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS

@[simp] lemma innerModelCLMRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b T S =
      tensorInnerPointwise (I := I) (M := M) g r s b T S := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_apply ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_apply

lemma innerModelCLMRS_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b T S =
      innerModelCLMRS (I := I) (M := M) g r s b S T := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_symm (I := I) (M := M) g r s b _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_symm ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_symm

lemma innerModelCLMRS_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSModel r s ℝ E) (hT : T ≠ 0) :
    0 < innerModelCLMRS (I := I) (M := M) g r s b T T := by
  rw [innerModelCLMRS_apply]
  have hnn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b T T :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b T
  rcases lt_or_eq_of_le hnn with hlt | heq
  · exact hlt
  · exfalso
    apply hT
    exact (tensorInnerPointwise_eq_zero_iff
      (I := I) (M := M) g r s b T).mp heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_pos ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_pos

lemma innerModelCLMRS_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSModel r s ℝ E) :
    0 ≤ innerModelCLMRS (I := I) (M := M) g r s b T T := by
  rw [innerModelCLMRS_apply]
  exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s b T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_nonneg ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_nonneg

lemma innerModelCLMRS_add_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T₁ T₂ S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b (T₁ + T₂) S =
      innerModelCLMRS (I := I) (M := M) g r s b T₁ S +
        innerModelCLMRS (I := I) (M := M) g r s b T₂ S := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_add_left (I := I) (M := M) g r s b _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_add_left ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_add_left

lemma innerModelCLMRS_add_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S₁ S₂ : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b T (S₁ + S₂) =
      innerModelCLMRS (I := I) (M := M) g r s b T S₁ +
        innerModelCLMRS (I := I) (M := M) g r s b T S₂ := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_add_right (I := I) (M := M) g r s b _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_add_right ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_add_right

lemma innerModelCLMRS_smul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b (c • T) S =
      c * innerModelCLMRS (I := I) (M := M) g r s b T S := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_smul_left (I := I) (M := M) g r s b c _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_smul_left ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_smul_left

lemma innerModelCLMRS_smul_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b T (c • S) =
      c * innerModelCLMRS (I := I) (M := M) g r s b T S := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_smul_right (I := I) (M := M) g r s b c _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_smul_right ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_smul_right

private def bundleCLERS (r s : ℕ) (b : M) :
    TensorRSSpace r s I b ≃L[ℝ] TensorRSModel r s ℝ E :=
  Tensor0SBundle.tensorRSSpaceContinuousLinearEquiv
    (𝕜 := ℝ) (E := E) (I := I) (M := M) r s b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.bundleCLERS
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.bundleCLERS target :: scope.openDecls } }

private def bundleToModelCLMRS (r s : ℕ) (b : M) :
    TensorRSSpace r s I b →L[ℝ] TensorRSModel r s ℝ E :=
  (bundleCLERS (I := I) (M := M) (E := E) r s b).toContinuousLinearMap

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.bundleToModelCLMRS
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.bundleToModelCLMRS target :: scope.openDecls } }

private def precompBundleCLMRS (r s : ℕ) (b : M) :
    (TensorRSModel r s ℝ E →L[ℝ] ℝ) →L[ℝ]
      (TensorRSSpace r s I b →L[ℝ] ℝ) :=
  ((bundleCLERS (I := I) (M := M) (E := E) r s b).symm.arrowCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)).toContinuousLinearMap

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.precompBundleCLMRS
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.precompBundleCLMRS target :: scope.openDecls } }

@[simp] private lemma precompBundleCLMRS_apply (r s : ℕ) (b : M)
    (f : TensorRSModel r s ℝ E →L[ℝ] ℝ) (T : TensorRSSpace r s I b) :
    precompBundleCLMRS (I := I) (M := M) (E := E) r s b f T =
      f (Tensor0SBundle.TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T) :=
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.precompBundleCLMRS_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.precompBundleCLMRS_apply target :: scope.openDecls } }

def tensorRSRiemannianInnerCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    TensorRSSpace r s I b →L[ℝ] TensorRSSpace r s I b →L[ℝ] ℝ :=
  let modelPairing : TensorRSModel r s ℝ E →L[ℝ] (TensorRSSpace r s I b →L[ℝ] ℝ) :=
    (precompBundleCLMRS (I := I) (M := M) (E := E) r s b).comp
      (innerModelCLMRS (I := I) (M := M) g r s b)
  modelPairing.comp (bundleToModelCLMRS (I := I) (M := M) (E := E) r s b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM

@[simp] lemma tensorRSRiemannianInnerCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T S =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T)
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) S) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply

theorem tensorRSRiemannianInnerCLM_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T S =
      tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b S T := by
  rw [tensorRSRiemannianInnerCLM_apply, tensorRSRiemannianInnerCLM_apply]
  exact tensorInnerPointwise_symm (I := I) (M := M) g r s b _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_symm ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_symm

theorem tensorRSRiemannianInnerCLM_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) (hT : T ≠ 0) :
    0 < tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T T := by
  rw [tensorRSRiemannianInnerCLM_apply]
  have hTm :
      Tensor0SBundle.TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T ≠ 0 := by
    intro h
    apply hT
    have hinj :=
      Tensor0SBundle.TensorRSSpace.toModel_injective
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
    have hzero :
        Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (0 : TensorRSSpace r s I b) = 0 :=
      Tensor0SBundle.TensorRSSpace.toModel_zero
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
    exact hinj (h.trans hzero.symm)
  have hnn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T)
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  rcases lt_or_eq_of_le hnn with hlt | heq
  · exact hlt
  · exfalso
    apply hTm
    exact (tensorInnerPointwise_eq_zero_iff
      (I := I) (M := M) g r s b _).mp heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_pos ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_pos

theorem tensorRSRiemannianInnerCLM_smul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b (c • T) S =
      c * tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T S := by
  have h := ContinuousLinearMap.map_smul
    (tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b) c T
  change tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b (c • T) S = _
  rw [h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_smul_left ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_smul_left

theorem tensorRSRiemannianInnerCLM_smul_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T (c • S) =
      c * tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T S := by
  have h := ContinuousLinearMap.map_smul
    ((tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b) T) c S
  change (tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T) (c • S) = _
  rw [h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_smul_right ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_smul_right

private lemma innerModelRS_quadratic_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    Continuous (fun T : TensorRSModel r s ℝ E =>
      tensorInnerPointwise (I := I) (M := M) g r s b T T) := by
  classical
  let ι := Fin (Module.finrank ℝ (TensorRSModel r s ℝ E))
  let basis : Module.Basis ι ℝ (TensorRSModel r s ℝ E) :=
    Module.finBasis ℝ (TensorRSModel r s ℝ E)
  let φ : ι → (TensorRSModel r s ℝ E →ₗ[ℝ] ℝ) := fun i => basis.coord i
  have hφ_cont : ∀ i, Continuous (φ i) := fun i =>
    LinearMap.continuous_of_finiteDimensional (φ i)
  have hexpand : ∀ T : TensorRSModel r s ℝ E,
      T = ∑ i : ι, (φ i T) • basis i := by
    intro T
    have := basis.linearCombination_repr T
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype] at this
    · exact this.symm
    · intros; rw [zero_smul]
  have hgen_left : ∀ (a : ι → ℝ) (S : TensorRSModel r s ℝ E),
      tensorInnerPointwise (I := I) (M := M) g r s b
        (∑ i : ι, a i • basis i) S =
        ∑ i : ι, (a i) *
          tensorInnerPointwise (I := I) (M := M) g r s b (basis i) S := by
    intro a S
    let LL : TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
      { toFun := fun T' => tensorInnerPointwise (I := I) (M := M) g r s b T' S
        map_add' := fun T₁ T₂ =>
          tensorInnerPointwise_add_left (I := I) (M := M) g r s b T₁ T₂ S
        map_smul' := fun c T' => by
          change tensorInnerPointwise (I := I) (M := M) g r s b (c • T') S = c • _
          rw [tensorInnerPointwise_smul_left]
          rfl }
    have hLL_sum : LL (∑ i : ι, a i • basis i) =
        ∑ i : ι, LL (a i • basis i) :=
      map_sum LL _ _
    change LL _ = _
    rw [hLL_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [LL.map_smul]
    rfl
  have hgen_right : ∀ (a : ι → ℝ) (i : ι),
      tensorInnerPointwise (I := I) (M := M) g r s b (basis i)
        (∑ j : ι, a j • basis j) =
        ∑ j : ι, (a j) *
          tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
    intro a i
    let RR : TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
      { toFun := fun S' => tensorInnerPointwise (I := I) (M := M) g r s b (basis i) S'
        map_add' := fun S₁ S₂ =>
          tensorInnerPointwise_add_right (I := I) (M := M) g r s b (basis i) S₁ S₂
        map_smul' := fun c S' => by
          change tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (c • S') = c • _
          rw [tensorInnerPointwise_smul_right]
          rfl }
    have hRR_sum : RR (∑ j : ι, a j • basis j) =
        ∑ j : ι, RR (a j • basis j) :=
      map_sum RR _ _
    change RR _ = _
    rw [hRR_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [RR.map_smul]
    rfl
  have hbilin_aux : ∀ (T : TensorRSModel r s ℝ E) (a : ι → ℝ),
      T = ∑ i : ι, a i • basis i →
      tensorInnerPointwise (I := I) (M := M) g r s b T T =
        ∑ i : ι, ∑ j : ι, (a i) * (a j) *
          tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
    intro T a hT
    calc tensorInnerPointwise (I := I) (M := M) g r s b T T
        = tensorInnerPointwise (I := I) (M := M) g r s b
            (∑ i : ι, a i • basis i) (∑ j : ι, a j • basis j) := by rw [← hT]
      _ = ∑ i : ι, (a i) *
            tensorInnerPointwise (I := I) (M := M) g r s b (basis i)
              (∑ j : ι, a j • basis j) :=
            hgen_left a (∑ j : ι, a j • basis j)
      _ = ∑ i : ι, (a i) *
            ∑ j : ι, (a j) *
              tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hgen_right a i]
      _ = ∑ i : ι, ∑ j : ι, (a i) * (a j) *
            tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
  have hbilin_expand : ∀ T : TensorRSModel r s ℝ E,
      tensorInnerPointwise (I := I) (M := M) g r s b T T =
        ∑ i : ι, ∑ j : ι, (φ i T) * (φ j T) *
          tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
    intro T
    exact hbilin_aux T (fun i => φ i T) (hexpand T)
  have hcont : Continuous (fun T : TensorRSModel r s ℝ E =>
      ∑ i : ι, ∑ j : ι, (φ i T) * (φ j T) *
        tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j)) := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    refine continuous_finsetSum _ (fun j _ => ?_)
    refine ((hφ_cont i).mul (hφ_cont j)).mul continuous_const
  refine hcont.congr ?_
  intro T
  exact (hbilin_expand T).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelRS_quadratic_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelRS_quadratic_continuous target :: scope.openDecls } }

lemma tensorRSRiemannianInnerCLM_diagonal_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    Continuous (fun v : TensorRSSpace r s I b =>
      tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v) := by
  have heq : (fun v : TensorRSSpace r s I b =>
      tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v) =
      (fun v : TensorRSSpace r s I b =>
        tensorInnerPointwise (I := I) (M := M) g r s b
          (Tensor0SBundle.TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) v)
          (Tensor0SBundle.TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) v)) := by
    funext v; rw [tensorRSRiemannianInnerCLM_apply]
  rw [heq]
  exact (innerModelRS_quadratic_continuous (I := I) (M := M) g r s b).comp
    (Tensor0SBundle.TensorRSSpace.toModel_continuous
      (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_diagonal_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_diagonal_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_diagonal_continuous ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_diagonal_continuous

theorem tensorRSRiemannianInnerCLM_diagonal_continuousAt_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    ContinuousAt (fun v : TensorRSSpace r s I b =>
      tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v) 0 :=
  (tensorRSRiemannianInnerCLM_diagonal_continuous (I := I) (M := M) g r s b).continuousAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_diagonal_continuousAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_diagonal_continuousAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_diagonal_continuousAt_zero ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_diagonal_continuousAt_zero

private lemma innerModelRS_diagonal_sublevel_isBounded
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    Bornology.IsBounded
      {T : TensorRSModel r s ℝ E |
        innerModelCLMRS (I := I) (M := M) g r s b T T < 1} := by
  have hPD : ∀ v : TensorRSModel r s ℝ E,
      v ≠ 0 → 0 < innerModelCLMRS (I := I) (M := M) g r s b v v := by
    intro v hv
    change 0 < tensorInnerPointwise (I := I) (M := M) g r s b v v
    have hQpos := (tensorInnerPointwise_eq_zero_iff
      (I := I) (M := M) g r s b v).not.mpr hv
    have hnn := tensorInnerPointwise_nonneg (I := I) (M := M) g r s b v
    exact lt_of_le_of_ne hnn (Ne.symm hQpos)
  exact Tensor0SRiemannian.posDef_bilin_unit_ball_isBounded
    (innerModelCLMRS (I := I) (M := M) g r s b) hPD

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelRS_diagonal_sublevel_isBounded
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelRS_diagonal_sublevel_isBounded target :: scope.openDecls } }

private lemma innerModelRS_diagonal_sublevel_isVonNBounded
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    _root_.Bornology.IsVonNBounded ℝ
      {T : TensorRSModel r s ℝ E |
        innerModelCLMRS (I := I) (M := M) g r s b T T < 1} :=
  NormedSpace.isVonNBounded_of_isBounded ℝ
    (innerModelRS_diagonal_sublevel_isBounded (I := I) (M := M) g r s b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelRS_diagonal_sublevel_isVonNBounded
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelRS_diagonal_sublevel_isVonNBounded target :: scope.openDecls } }

private lemma tensorRSRiemannianInner_diagonal_clm_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T T =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T)
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T) := by
  rw [tensorRSRiemannianInnerCLM_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInner_diagonal_clm_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInner_diagonal_clm_apply target :: scope.openDecls } }

theorem tensorRSRiemannianInnerCLM_isVonNBounded
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    _root_.Bornology.IsVonNBounded ℝ
      {v : TensorRSSpace r s I b |
        tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v < 1} := by
  set e : TensorRSSpace r s I b ≃L[ℝ] TensorRSModel r s ℝ E :=
    Tensor0SBundle.tensorRSSpaceContinuousLinearEquiv
      (𝕜 := ℝ) (E := E) (I := I) (M := M) r s b with he_def
  have hModel := innerModelRS_diagonal_sublevel_isVonNBounded
    (I := I) (M := M) g r s b
  have hImage :=
    hModel.image (e.symm.toContinuousLinearMap)
  have hSetEq :
      e.symm.toContinuousLinearMap ''
        {T : TensorRSModel r s ℝ E |
          innerModelCLMRS (I := I) (M := M) g r s b T T < 1} =
      {v : TensorRSSpace r s I b |
          tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v < 1} := by
    ext v
    refine ⟨?_, ?_⟩
    · rintro ⟨T, hT, rfl⟩
      rw [Set.mem_ofPred_eq] at hT
      rw [Set.mem_ofPred_eq, tensorRSRiemannianInner_diagonal_clm_apply]
      have hRound : (e (e.symm T) : _) = T := e.apply_symm_apply T
      have hToModel :
          Tensor0SBundle.TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
            ((e.symm.toContinuousLinearMap :
              TensorRSModel r s ℝ E →L[ℝ] TensorRSSpace r s I b) T) = T := hRound
      rw [hToModel]
      change tensorInnerPointwise (I := I) (M := M) g r s b T T < 1
      rw [innerModelCLMRS_apply] at hT
      exact hT
    · intro hv
      refine ⟨e v, ?_, ?_⟩
      · rw [Set.mem_ofPred_eq]
        rw [Set.mem_ofPred_eq, tensorRSRiemannianInner_diagonal_clm_apply] at hv
        rw [innerModelCLMRS_apply]
        exact hv
      · exact e.symm_apply_apply v
  rw [← hSetEq]
  exact hImage

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_isVonNBounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_isVonNBounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_isVonNBounded ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_isVonNBounded

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
noncomputable def tensorRSRiemannianMetric
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Bundle.RiemannianMetric (E := fun b : M => TensorRSSpace r s I b) where
  inner := fun b => tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b
  symm := fun b T S =>
    tensorRSRiemannianInnerCLM_symm (I := I) (M := M) g r s b T S
  pos := fun b T hT =>
    tensorRSRiemannianInnerCLM_pos (I := I) (M := M) g r s b T hT
  continuousAt := fun b =>
    tensorRSRiemannianInnerCLM_diagonal_continuousAt_zero
      (I := I) (M := M) g r s b
  isVonNBounded := fun b =>
    tensorRSRiemannianInnerCLM_isVonNBounded (I := I) (M := M) g r s b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianMetric ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianMetric

end TensorRSRiemannianBundle
end Tensor
end DifferentialGeometry

namespace DifferentialGeometry
namespace Tensor0SBundle

open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

@[reducible]
noncomputable def tensorRSRiemannianBundle
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
  ⟨tensorRSRiemannianMetric (I := I) (M := M) g r s⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tensorRSRiemannianBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tensorRSRiemannianBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tensorRSRiemannianBundle ``Submission.DifferentialGeometry.Tensor0SBundle.tensorRSRiemannianBundle

end Tensor0SBundle
end DifferentialGeometry
