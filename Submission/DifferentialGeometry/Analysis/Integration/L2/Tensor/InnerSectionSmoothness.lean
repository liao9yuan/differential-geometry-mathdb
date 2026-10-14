import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.TensorRS.Riemannian
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.MetricLowering
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Tensor
namespace TensorRSRiemannian

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian
open _root_.Submission.DifferentialGeometry.TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance tensor0SModelNormedSpace_local {n : ℕ} :
    NormedSpace ℝ (Tensor0SModel n ℝ E) :=
  Tensor0SBundle.tensor0SModelNormedSpace n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.tensor0SModelNormedSpace_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TensorRSRiemannian.tensor0SModelNormedSpace_local target :: scope.openDecls } }

private local instance tensor0SModelNormedAddCommGroup_local {n : ℕ} :
    NormedAddCommGroup (Tensor0SModel n ℝ E) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.tensor0SModelNormedAddCommGroup_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TensorRSRiemannian.tensor0SModelNormedAddCommGroup_local target :: scope.openDecls } }


omit [IsManifold I ∞ M] in
lemma contMDiffOn_eval_basisTuple_of_into_tensor0SModel
    {n : ℕ} {U : Set M} {Φ : M → Tensor0SModel n ℝ E}
    (hΦ : ContMDiffOn I 𝓘(ℝ, Tensor0SModel n ℝ E) ∞ Φ U)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => Φ b (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k))) U := by
  set evalCLM :
      Tensor0SModel n ℝ E →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℝ
      (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)) with hevalCLM
  have heq : (fun b : M => Φ b (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)))
      = fun b : M => evalCLM (Φ b) := by
    funext b
    rfl
  rw [heq]
  exact evalCLM.contMDiff.comp_contMDiffOn hΦ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.contMDiffOn_eval_basisTuple_of_into_tensor0SModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.contMDiffOn_eval_basisTuple_of_into_tensor0SModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.contMDiffOn_eval_basisTuple_of_into_tensor0SModel ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.contMDiffOn_eval_basisTuple_of_into_tensor0SModel


theorem chartTensorInnerPointwise_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (T S : M → TensorRSModel r s ℝ E)
    (hT : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b (T b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hS : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b (S b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => chartTensorInnerPointwise
        (I := I) (M := M) g α r s b (T b) (S b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  have hsmooth :
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => chartTensorInnerPointwise0s
          (I := I) (M := M) (r + s) g α b
            (loweredCompose (I := I) (M := M) g r s α b (T b))
            (loweredCompose (I := I) (M := M) g r s α b (S b)))
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartTensorInnerPointwise_0s_contMDiffOn_smooth_args
      (I := I) (M := M) g α (r + s)
      (fun b => loweredCompose (I := I) (M := M) g r s α b (T b))
      (fun b => loweredCompose (I := I) (M := M) g r s α b (S b))
      (fun φ => contMDiffOn_eval_basisTuple_of_into_tensor0SModel
        (I := I) (M := M) hT φ)
      (fun φ => contMDiffOn_eval_basisTuple_of_into_tensor0SModel
        (I := I) (M := M) hS φ)
  exact hsmooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_contMDiffOn ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_contMDiffOn


theorem chartLocal_contMDiff_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : ∀ y : M, TensorRSSpace r s I y) (α : M)
    (hTα : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hSα : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffOn I 𝓘(ℝ) ∞
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
  refine ContMDiffOn.congr ?_ hbridge
  exact chartTensorInnerPointwise_contMDiffOn
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
  if env.contains `DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections ``Submission.DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections

end TensorRSRiemannian
end Tensor
end DifferentialGeometry

namespace TensorRSBundle

open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.TensorMetricLowering
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance tensor0SModelNormedSpace_local {n : ℕ} :
    NormedSpace ℝ (Tensor0SModel n ℝ E) :=
  Tensor0SBundle.tensor0SModelNormedSpace n

run_cmd do
  let target := ``Submission.TensorRSBundle.tensor0SModelNormedSpace_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `TensorRSBundle.tensor0SModelNormedSpace_local target :: scope.openDecls } }


theorem contMDiff_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : ∀ y : M, TensorRSSpace r s I y)
    (hT_charts : ∀ α : M, ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hS_charts : ∀ α : M, ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b))
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b))) := by
  intro b
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) b).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ b
  have hOpen : IsOpen (_root_.FiberBundle.trivializationAt E (TangentSpace I) b).baseSet :=
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) b).open_baseSet
  have hLocal :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections
      (I := I) (M := M) g r s T S b (hT_charts b) (hS_charts b)
  exact hLocal.contMDiffAt (hOpen.mem_nhds hb_base)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TensorRSBundle.contMDiff_inner_of_smooth_sections then
    throwError "Refusing to shadow existing declaration TensorRSBundle.contMDiff_inner_of_smooth_sections"
  Lean.modifyEnv fun env => Lean.addAlias env `TensorRSBundle.contMDiff_inner_of_smooth_sections ``Submission.TensorRSBundle.contMDiff_inner_of_smooth_sections

end TensorRSBundle

namespace DifferentialGeometry
namespace Tensor

open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.TensorMetricLowering
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem tensorInnerPointwise_contMDiff_of_mdiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel (T b))
        (TensorRSSpace.toModel (S b))) :=
  TensorRSBundle.contMDiff_inner_of_smooth_sections
    (I := I) (M := M) g r s
    (fun b : M => T b) (fun b : M => S b)
    (fun α : M =>
      TensorMetricLowering.contMDiffOn_loweredCompose
        (I := I) (M := M) g r s T α)
    (fun α : M =>
      TensorMetricLowering.contMDiffOn_loweredCompose
        (I := I) (M := M) g r s S α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.tensorInnerPointwise_contMDiff_of_mdiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.tensorInnerPointwise_contMDiff_of_mdiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.tensorInnerPointwise_contMDiff_of_mdiff ``Submission.DifferentialGeometry.Tensor.tensorInnerPointwise_contMDiff_of_mdiff


theorem tensorInnerPointwise_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel (S.toSection b))
        (TensorRSSpace.toModel (T.toSection b))) :=
  tensorInnerPointwise_contMDiff_of_mdiff
    (I := I) (M := M) g r s S.toSection T.toSection

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.tensorInnerPointwise_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.tensorInnerPointwise_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.tensorInnerPointwise_contMDiff ``Submission.DifferentialGeometry.Tensor.tensorInnerPointwise_contMDiff

end Tensor
end DifferentialGeometry

end
