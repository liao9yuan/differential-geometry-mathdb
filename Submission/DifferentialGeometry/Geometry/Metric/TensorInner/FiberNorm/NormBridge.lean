import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.TensorRS.RiemannianBundle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance tensorRSRiemannianNormedAddCommGroup_local
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M ↦ Tensor0SBundle.TensorRSSpace r s I b)]
    (b : M) : NormedAddCommGroup (Tensor0SBundle.TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorRSRiemannianNormedAddCommGroup_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorRSRiemannianNormedAddCommGroup_local target :: scope.openDecls } }

private local instance tensorRSModelAdd_local (r s : ℕ) :
    Add (Tensor0SBundle.TensorRSModel r s ℝ E) :=
  ContinuousLinearMap.addCommGroup.toAddCommMonoid.toAddCommSemigroup.toAddCommMagma.toAdd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorRSModelAdd_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorRSModelAdd_local target :: scope.openDecls } }

private local instance tensorRSModelSub_local (r s : ℕ) :
    Sub (Tensor0SBundle.TensorRSModel r s ℝ E) :=
  ContinuousLinearMap.sub

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorRSModelSub_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorRSModelSub_local target :: scope.openDecls } }

private local instance tensorRSModelNeg_local (r s : ℕ) :
    Neg (Tensor0SBundle.TensorRSModel r s ℝ E) :=
  ContinuousLinearMap.neg

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorRSModelNeg_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorRSModelNeg_local target :: scope.openDecls } }

private local instance tensorRSModelZero_local (r s : ℕ) :
    Zero (Tensor0SBundle.TensorRSModel r s ℝ E) :=
  ContinuousLinearMap.zero

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorRSModelZero_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorRSModelZero_local target :: scope.openDecls } }

private local instance tensorRSModelSMul_local (r s : ℕ) :
    SMul ℝ (Tensor0SBundle.TensorRSModel r s ℝ E) :=
  ContinuousLinearMap.mulAction.toSMul

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorRSModelSMul_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorRSModelSMul_local target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem inner_self_eq_tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (T : TensorRSSpace r s I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    (_root_.Inner.inner ℝ T T : ℝ) =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel T) (TensorRSSpace.toModel T) := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  have hclm : (tensorRSRiemannianInnerCLM (I := I) (M := M) g r s x T T : ℝ) =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel T) (TensorRSSpace.toModel T) :=
    tensorRSRiemannianInnerCLM_apply (I := I) (M := M) g r s x T T
  rw [← hclm]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.inner_self_eq_tensorInnerPointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.inner_self_eq_tensorInnerPointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.inner_self_eq_tensorInnerPointwise ``Submission.DifferentialGeometry.Analysis.Elliptic.inner_self_eq_tensorInnerPointwise

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompleteSpace E] in
theorem norm_eq_sqrt_tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (T : TensorRSSpace r s I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    ‖T‖ =
      Real.sqrt
        (tensorInnerPointwise (I := I) (M := M) g r s x
          (TensorRSSpace.toModel T) (TensorRSSpace.toModel T)) := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  rw [← inner_self_eq_tensorInnerPointwise (I := I) (M := M) g r s x T]
  rw [real_inner_self_eq_norm_sq]
  exact (Real.sqrt_sq (norm_nonneg T)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.norm_eq_sqrt_tensorInnerPointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.norm_eq_sqrt_tensorInnerPointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.norm_eq_sqrt_tensorInnerPointwise ``Submission.DifferentialGeometry.Analysis.Elliptic.norm_eq_sqrt_tensorInnerPointwise

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompleteSpace E] in
theorem norm_eq_of_tensorInnerPointwise_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T S : TensorRSSpace r s I x)
    (h : tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel T) (TensorRSSpace.toModel T) =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel S) (TensorRSSpace.toModel S)) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    ‖T‖ = ‖S‖ := by
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  rw [norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r s x T,
    norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r s x S, h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.norm_eq_of_tensorInnerPointwise_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.norm_eq_of_tensorInnerPointwise_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.norm_eq_of_tensorInnerPointwise_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.norm_eq_of_tensorInnerPointwise_eq

end Elliptic
end Analysis
end DifferentialGeometry

end
