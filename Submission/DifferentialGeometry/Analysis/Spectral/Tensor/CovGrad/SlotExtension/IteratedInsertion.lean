import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.ApplicationJets
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.SlotInsertion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

private local instance slotIterTensorRSModelNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedAddCommGroup r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.slotIterTensorRSModelNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.slotIterTensorRSModelNormedAddCommGroup target :: scope.openDecls } }

private local instance slotIterTensorRSModelNormedSpace (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedSpace r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.slotIterTensorRSModelNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.slotIterTensorRSModelNormedSpace target :: scope.openDecls } }

private local instance slotIterTensorRSTotalSpaceTopology (r s : ℕ) :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x)) :=
  Tensor0SBundle.tensorRSBundleTopology r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.slotIterTensorRSTotalSpaceTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.slotIterTensorRSTotalSpaceTopology target :: scope.openDecls } }

private local instance slotIterTensorRSFiberBundle (r s : ℕ) :
    FiberBundle (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x) :=
  Tensor0SBundle.tensorRSBundleFiber r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.slotIterTensorRSFiberBundle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.slotIterTensorRSFiberBundle target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem slotExtIter_apply (g : SmoothRiemannianMetric I M) (s w : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (x : M) (A : Tensor0SSpace ((s + 1) + w) I x) :
    (show Tensor0SSpace ((s + 1) + w) I x →L[ℝ]
        Tensor0SSpace ((s + 1) + w) I x from
      (slotExtendIter (I := I) (M := M) g (s + 1) (s + 1) w
        (endoSlotZeroCcTensor (I := I) (M := M) g s Λ)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) ((s + 1) + w) ⟨w, by omega⟩ x (Λ x) A := by
  induction w with
  | zero =>
      rfl
  | succ w ih =>
      change slotExtendPointwise (I := I) (M := M) ((s + 1) + w) ((s + 1) + w) x
          (show Tensor0SSpace ((s + 1) + w) I x →L[ℝ]
              Tensor0SSpace ((s + 1) + w) I x from
            (slotExtendIter (I := I) (M := M) g (s + 1) (s + 1) w
              (endoSlotZeroCcTensor (I := I) (M := M) g s Λ)).toSection x) A = _
      change _ =
        (slotInsertEndoFib (I := I) (M := M) (((s + 1) + w) + 1)
          (⟨w, by omega⟩ : Fin ((s + 1) + w)).succ x (Λ x)) A
      rw [slotInsertEndoFib_succ (I := I) (M := M) ((s + 1) + w)
        ⟨w, by omega⟩ x (Λ x)]
      apply Tensor0SSpace.toModel_injective
      refine ContinuousMultilinearMap.ext (fun m => ?_)
      rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
      rw [slotExtendFib_apply_eval (I := I) (M := M) ((s + 1) + w) ((s + 1) + w),
        slotExtendFib_apply_eval (I := I) (M := M) ((s + 1) + w) ((s + 1) + w)]
      rw [ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.slotExtIter_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.slotExtIter_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.slotExtIter_apply ``Submission.DifferentialGeometry.Analysis.Spectral.slotExtIter_apply

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem app_slotExt_apply (g : SmoothRiemannianMetric I M) (s w : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (W : SmoothCcTensor g 0 ((s + 1) + w)) (x : M) (d : Tensor0SSpace 0 I x) :
    (ccOperatorFieldComp (I := I) (M := M) g 0 ((s + 1) + w) ((s + 1) + w)
      (slotExtendIter (I := I) (M := M) g (s + 1) (s + 1) w
        (endoSlotZeroCcTensor (I := I) (M := M) g s Λ)) W).toSection x d =
      slotInsertEndoFib (I := I) (M := M) ((s + 1) + w) ⟨w, by omega⟩ x (Λ x)
        (W.toSection x d) := by
  rw [operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply]
  exact slotExtIter_apply (I := I) (M := M) g s w Λ x (W.toSection x d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.app_slotExt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.app_slotExt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.app_slotExt_apply ``Submission.DifferentialGeometry.Analysis.Spectral.app_slotExt_apply

end Spectral
end Analysis
end DifferentialGeometry
