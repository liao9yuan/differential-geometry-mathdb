import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.Covariant
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTensor.Mixed

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2Inner_covGrad_operatorFieldApplication_eq_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (T : SmoothCcTensor g 0 (s + 1)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s
          (operatorFieldApply (I := I) (M := M) g r s Φ W)).toFun T.toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (operatorFieldApply (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s Φ) W).toFun T.toFun +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ)
            (covGrad (I := I) (M := M) g 0 r W)).toFun T.toFun := by
  classical
  set A1 : SmoothCcTensor g 0 (s + 1) :=
    operatorFieldApply (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W with hA1
  set A2 : SmoothCcTensor g 0 (s + 1) :=
    operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
      (covGrad (I := I) (M := M) g 0 r W) with hA2
  have hB : covGrad (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ W) = A1 +
    A2 :=
    covGrad_operatorFieldApply_eq (I := I) (M := M) g r s Φ W
  have hstep := congrArg
    (fun Z : SmoothCcTensor g 0 (s + 1) =>
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Z.toFun T.toFun) hB
  rw [hstep, SmoothCcTensor.toFun_add]
  exact tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
    A1.toFun A2.toFun T.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A1 T)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A2 T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_operatorFieldApplication_eq_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_operatorFieldApplication_eq_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_operatorFieldApplication_eq_add ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_operatorFieldApplication_eq_add

theorem tensorL2Inner_operatorFieldApplication_covGrad_covGrad_eq_neg (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Φ : SmoothCcTensor g s s) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (operatorFieldApply (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s Φ) S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s
            (operatorFieldApply (I := I) (M := M) g s s Φ S)).toFun S.toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (operatorFieldApply (I := I) (M := M) g (s + 1) (s + 1)
            (slotExtend (I := I) (M := M) g s s Φ)
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hsplit := tensorL2Inner_covGrad_operatorFieldApplication_eq_add (I := I) (M := M) g s s Φ S
    (covGrad (I := I) (M := M) g 0 s S)
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g s s Φ S) S
  rw [hgreen] at hsplit
  linarith [hsplit]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldApplication_covGrad_covGrad_eq_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldApplication_covGrad_covGrad_eq_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldApplication_covGrad_covGrad_eq_neg ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldApplication_covGrad_covGrad_eq_neg

theorem tensorL2Inner_operatorFieldApplication_slotExtend_input_covGrad_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (X : SmoothCcTensor g 0 r) (V : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)
          (covGrad (I := I) (M := M) g 0 r X)).toFun
        (covGrad (I := I) (M := M) g 0 s V).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s
            (operatorFieldApply (I := I) (M := M) g r s Φ X)).toFun V.toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (operatorFieldApply (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s Φ) X).toFun
          (covGrad (I := I) (M := M) g 0 s V).toFun := by
  classical
  have hsplit := tensorL2Inner_covGrad_operatorFieldApplication_eq_add (I := I) (M := M) g r s Φ X
    (covGrad (I := I) (M := M) g 0 s V)
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ X) V
  rw [hgreen] at hsplit
  linarith [hsplit]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldApplication_slotExtend_input_covGrad_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldApplication_slotExtend_input_covGrad_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldApplication_slotExtend_input_covGrad_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldApplication_slotExtend_input_covGrad_eq

theorem tensorL2Inner_rawConnLap_operatorFieldApplication_eq_neg_covGrad_split (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (A : SmoothCcTensor g 0 s) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    tensorL2Inner (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s A).toFun
        (operatorFieldApply (I := I) (M := M) g r s Φ W).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s A).toFun
          (operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ)
            (covGrad (I := I) (M := M) g 0 r W)).toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s A).toFun
          (operatorFieldApply (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s Φ) W).toFun := by
  classical
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g 0 s A (operatorFieldApply (I := I) (M := M) g r s Φ W)
  have hsplit := tensorL2Inner_covGrad_operatorFieldApplication_eq_add (I := I) (M := M) g r s Φ W
    (covGrad (I := I) (M := M) g 0 s A)
  have hsymm0 := tensorL2Inner_symm (I := I) (M := M) g 0 (s + 1)
    (covGrad (I := I) (M := M) g 0 s A).toFun
    (covGrad (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ W)).toFun
  have hsymm1 := tensorL2Inner_symm (I := I) (M := M) g 0 (s + 1)
    (operatorFieldApply (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W).toFun
    (covGrad (I := I) (M := M) g 0 s A).toFun
  have hsymm2 := tensorL2Inner_symm (I := I) (M := M) g 0 (s + 1)
    (operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
      (slotExtend (I := I) (M := M) g r s Φ)
      (covGrad (I := I) (M := M) g 0 r W)).toFun
    (covGrad (I := I) (M := M) g 0 s A).toFun
  linarith [hgreen, hsplit, hsymm0, hsymm1, hsymm2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_rawConnLap_operatorFieldApplication_eq_neg_covGrad_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_rawConnLap_operatorFieldApplication_eq_neg_covGrad_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_rawConnLap_operatorFieldApplication_eq_neg_covGrad_split ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_rawConnLap_operatorFieldApplication_eq_neg_covGrad_split

end Elliptic
end Analysis
end DifferentialGeometry

end
