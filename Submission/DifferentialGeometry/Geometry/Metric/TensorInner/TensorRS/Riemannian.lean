import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Bundle.SectionRegularity
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
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
namespace TensorRSRiemannian

open _root_.Submission.DifferentialGeometry (SmoothRiemannianMetric)
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def loweredCompose
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T : TensorRSModel r s ℝ E) : Tensor0SModel (r + s) ℝ E :=
  (lowerAllUpperIndices (I := I) (M := M) g r s b T).compContinuousLinearMap
    (fun _ : Fin (r + s) =>
      DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
        (I := I) (M := M) α b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose

@[simp] lemma loweredCompose_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    loweredCompose (I := I) (M := M) g r s α b T v =
      lowerAllUpperIndices (I := I) (M := M) g r s b T
        (fun i =>
          DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
            (I := I) (M := M) α b (v i)) := by
  unfold loweredCompose
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_apply ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_apply

lemma loweredCompose_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T₁ T₂ : TensorRSModel r s ℝ E) :
    loweredCompose (I := I) (M := M) g r s α b (T₁ + T₂) =
      loweredCompose (I := I) (M := M) g r s α b T₁ +
        loweredCompose (I := I) (M := M) g r s α b T₂ := by
  unfold loweredCompose
  rw [ContinuousLinearMap.map_add]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_add ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_add

lemma loweredCompose_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (c : ℝ) (T : TensorRSModel r s ℝ E) :
    loweredCompose (I := I) (M := M) g r s α b (c • T) =
      c • loweredCompose (I := I) (M := M) g r s α b T := by
  unfold loweredCompose
  rw [ContinuousLinearMap.map_smul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_smul ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_smul

lemma loweredCompose_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M) :
    loweredCompose (I := I) (M := M) g r s α b (0 : TensorRSModel r s ℝ E) =
      (0 : Tensor0SModel (r + s) ℝ E) := by
  unfold loweredCompose
  rw [ContinuousLinearMap.map_zero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_zero ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.loweredCompose_zero

noncomputable def chartTensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) : ℝ :=
  chartTensorInnerPointwise0s (I := I) (M := M) (r + s) g α b
    (loweredCompose (I := I) (M := M) g r s α b T)
    (loweredCompose (I := I) (M := M) g r s α b S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise

@[simp] lemma chartTensorInnerPointwise_apply
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T S =
      chartTensorInnerPointwise0s (I := I) (M := M) (r + s) g α b
        (loweredCompose (I := I) (M := M) g r s α b T)
        (loweredCompose (I := I) (M := M) g r s α b S) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_apply ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_apply

lemma chartTensorInnerPointwise_add_left
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T₁ T₂ S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b (T₁ + T₂) S =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b T₁ S +
        chartTensorInnerPointwise (I := I) (M := M) g α r s b T₂ S := by
  rw [chartTensorInnerPointwise_apply, chartTensorInnerPointwise_apply,
    chartTensorInnerPointwise_apply, loweredCompose_add]
  exact chartTensorInnerPointwise_0s_add_left
    (I := I) (M := M) g α b (r + s) _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_add_left ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_add_left

lemma chartTensorInnerPointwise_add_right
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T S₁ S₂ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T (S₁ + S₂) =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b T S₁ +
        chartTensorInnerPointwise (I := I) (M := M) g α r s b T S₂ := by
  rw [chartTensorInnerPointwise_apply, chartTensorInnerPointwise_apply,
    chartTensorInnerPointwise_apply, loweredCompose_add]
  exact chartTensorInnerPointwise_0s_add_right
    (I := I) (M := M) g α b (r + s) _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_add_right ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_add_right

lemma chartTensorInnerPointwise_smul_left
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b (c • T) S =
      c * chartTensorInnerPointwise (I := I) (M := M) g α r s b T S := by
  rw [chartTensorInnerPointwise_apply, chartTensorInnerPointwise_apply,
    loweredCompose_smul]
  exact chartTensorInnerPointwise_0s_smul_left
    (I := I) (M := M) g α b (r + s) c _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_smul_left ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_smul_left

lemma chartTensorInnerPointwise_smul_right
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T (c • S) =
      c * chartTensorInnerPointwise (I := I) (M := M) g α r s b T S := by
  rw [chartTensorInnerPointwise_apply, chartTensorInnerPointwise_apply,
    loweredCompose_smul]
  exact chartTensorInnerPointwise_0s_smul_right
    (I := I) (M := M) g α b (r + s) c _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_smul_right ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_smul_right

lemma chartTensorInnerPointwise_zero_left
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b 0 S = 0 := by
  rw [chartTensorInnerPointwise_apply, loweredCompose_zero]
  have h := chartTensorInnerPointwise_0s_add_left
    (I := I) (M := M) g α b (r + s) (0 : Tensor0SModel (r + s) ℝ E) 0
    (loweredCompose (I := I) (M := M) g r s α b S)
  have h₀ : (0 : Tensor0SModel (r + s) ℝ E) + 0 = 0 := add_zero _
  rw [h₀] at h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_zero_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_zero_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_zero_left ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_zero_left

lemma chartTensorInnerPointwise_zero_right
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T 0 = 0 := by
  rw [chartTensorInnerPointwise_apply, loweredCompose_zero]
  have h := chartTensorInnerPointwise_0s_add_right
    (I := I) (M := M) g α b (r + s)
    (loweredCompose (I := I) (M := M) g r s α b T)
    (0 : Tensor0SModel (r + s) ℝ E) 0
  have h₀ : (0 : Tensor0SModel (r + s) ℝ E) + 0 = 0 := add_zero _
  rw [h₀] at h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_zero_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_zero_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_zero_right ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_zero_right

theorem tensorInnerPointwise_bridge_identity
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (T S : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s b T S =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b T S := by
  unfold tensorInnerPointwise chartTensorInnerPointwise loweredCompose
  exact tensorInnerPointwise_0s_bridge_identity
    (I := I) (M := M) g α (r + s) hb _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.tensorInnerPointwise_bridge_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.tensorInnerPointwise_bridge_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.tensorInnerPointwise_bridge_identity ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.tensorInnerPointwise_bridge_identity

lemma chartTensorInnerPointwise_symm
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (T S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T S =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b S T := by
  rw [← tensorInnerPointwise_bridge_identity (I := I) (M := M) g α r s hb T S,
    ← tensorInnerPointwise_bridge_identity (I := I) (M := M) g α r s hb S T]
  exact tensorInnerPointwise_symm (I := I) (M := M) g r s b T S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_symm ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_symm

theorem chartTensorInnerPointwise_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (T S : M → TensorRSModel r s ℝ E)
    (hT : ContinuousOn (fun b : M => loweredCompose
        (I := I) (M := M) g r s α b (T b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hS : ContinuousOn (fun b : M => loweredCompose
        (I := I) (M := M) g r s α b (S b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousOn
      (fun b : M => chartTensorInnerPointwise
        (I := I) (M := M) g α r s b (T b) (S b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  have hcont :
      ContinuousOn (fun b : M => chartTensorInnerPointwise0s
        (I := I) (M := M) (r + s) g α b
          (loweredCompose (I := I) (M := M) g r s α b (T b))
          (loweredCompose (I := I) (M := M) g r s α b (S b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartTensorInnerPointwise_0s_continuousOn_smooth_args
      (I := I) (M := M) g α (r + s)
      (fun b => loweredCompose (I := I) (M := M) g r s α b (T b))
      (fun b => loweredCompose (I := I) (M := M) g r s α b (S b)) hT hS
  exact hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_continuousOn ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_continuousOn

theorem chartLocal_continuous_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : ∀ y : M, TensorRSSpace r s I y) (α : M)
    (hTα : ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hSα : ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousOn
      (fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
            (T b))
          (TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
            (S b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  have hbridge : ∀ b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet,
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b))
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)) =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b))
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)) := by
    intro b hb
    exact tensorInnerPointwise_bridge_identity
      (I := I) (M := M) g α r s hb _ _
  refine ContinuousOn.congr ?_ hbridge
  exact chartTensorInnerPointwise_continuousOn
    (I := I) (M := M) g α r s
    (fun b : M => TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
        (T b))
    (fun b : M => TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
        (S b))
    hTα hSα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_continuous_inner_of_smooth_sections then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_continuous_inner_of_smooth_sections"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_continuous_inner_of_smooth_sections ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_continuous_inner_of_smooth_sections

end TensorRSRiemannian
end Tensor
end DifferentialGeometry

namespace TensorRSBundle

open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry (SmoothRiemannianMetric)
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem continuous_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : ∀ y : M, TensorRSSpace r s I y)
    (hT_charts : ∀ α : M, ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hS_charts : ∀ α : M, ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    Continuous (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b))
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b))) := by
  rw [continuous_iff_continuousAt]
  intro b
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) b).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ b
  have hOpen : IsOpen (_root_.FiberBundle.trivializationAt E (TangentSpace I) b).baseSet :=
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) b).open_baseSet
  have hLocal :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_continuous_inner_of_smooth_sections
      (I := I) (M := M) g r s T S b (hT_charts b) (hS_charts b)
  exact hLocal.continuousAt (hOpen.mem_nhds hb_base)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TensorRSBundle.continuous_inner_of_smooth_sections then
    throwError "Refusing to shadow existing declaration TensorRSBundle.continuous_inner_of_smooth_sections"
  Lean.modifyEnv fun env => Lean.addAlias env `TensorRSBundle.continuous_inner_of_smooth_sections ``Submission.TensorRSBundle.continuous_inner_of_smooth_sections

end TensorRSBundle
