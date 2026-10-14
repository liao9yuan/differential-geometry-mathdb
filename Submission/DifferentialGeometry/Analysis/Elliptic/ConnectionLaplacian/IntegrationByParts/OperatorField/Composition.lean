import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.TensorRS
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
theorem tensorL2Inner_covGrad_operatorFieldComposition_eq_add (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (T : SmoothCcTensor g a (c + 1)) :
    tensorL2Inner (I := I) (M := M) g a (c + 1)
        (covGrad (I := I) (M := M) g a c
          (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W)).toFun T.toFun =
      tensorL2Inner (I := I) (M := M) g a (c + 1)
          (ccOperatorFieldComp (I := I) (M := M) g a b (c + 1)
            (covGrad (I := I) (M := M) g b c Φ) W).toFun T.toFun +
        tensorL2Inner (I := I) (M := M) g a (c + 1)
          (ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1)
            (slotExtend (I := I) (M := M) g b c Φ)
            (covGrad (I := I) (M := M) g a b W)).toFun T.toFun := by
  classical
  set A1 : SmoothCcTensor g a (c + 1) :=
    ccOperatorFieldComp (I := I) (M := M) g a b (c + 1) (covGrad (I := I) (M := M) g b c Φ) W with
      hA1
  set A2 : SmoothCcTensor g a (c + 1) :=
    ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1) (slotExtend (I := I) (M := M) g b c Φ)
      (covGrad (I := I) (M := M) g a b W) with hA2
  have hB : covGrad (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) = A1
    + A2 :=
    covGrad_operatorFieldComposition_eq (I := I) (M := M) g a b c Φ W
  have hstep := congrArg
    (fun Z : SmoothCcTensor g a (c + 1) =>
      tensorL2Inner (I := I) (M := M) g a (c + 1) Z.toFun T.toFun) hB
  rw [hstep, SmoothCcTensor.toFun_add]
  exact tensorL2Inner_add_left (I := I) (M := M) g a (c + 1)
    A1.toFun A2.toFun T.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A1 T)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A2 T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_operatorFieldComposition_eq_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_operatorFieldComposition_eq_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_operatorFieldComposition_eq_add ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_operatorFieldComposition_eq_add

theorem tensorL2Inner_operatorFieldComposition_covGrad_covGrad_eq_neg (g : SmoothRiemannianMetric I M)
    (a c : ℕ) (Φ : SmoothCcTensor g c c) (S : SmoothCcTensor g a c) :
    tensorL2Inner (I := I) (M := M) g a (c + 1)
        (ccOperatorFieldComp (I := I) (M := M) g a c (c + 1)
          (covGrad (I := I) (M := M) g c c Φ) S).toFun
        (covGrad (I := I) (M := M) g a c S).toFun =
      - tensorL2Inner (I := I) (M := M) g a c
          (rawTensorConnLapSmooth (I := I) g a c
            (ccOperatorFieldComp (I := I) (M := M) g a c c Φ S)).toFun S.toFun -
        tensorL2Inner (I := I) (M := M) g a (c + 1)
          (ccOperatorFieldComp (I := I) (M := M) g a (c + 1) (c + 1)
            (slotExtend (I := I) (M := M) g c c Φ)
            (covGrad (I := I) (M := M) g a c S)).toFun
          (covGrad (I := I) (M := M) g a c S).toFun := by
  classical
  have hsplit := tensorL2Inner_covGrad_operatorFieldComposition_eq_add (I := I) (M := M) g a c c Φ S
    (covGrad (I := I) (M := M) g a c S)
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a c c Φ S) S
  rw [hgreen] at hsplit
  linarith [hsplit]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldComposition_covGrad_covGrad_eq_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldComposition_covGrad_covGrad_eq_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldComposition_covGrad_covGrad_eq_neg ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldComposition_covGrad_covGrad_eq_neg

theorem tensorL2Inner_operatorFieldComposition_slotExtend_input_covGrad_eq (g : SmoothRiemannianMetric I M)
    (a b c : ℕ) (Φ : SmoothCcTensor g b c) (X : SmoothCcTensor g a b)
    (V : SmoothCcTensor g a c) :
    tensorL2Inner (I := I) (M := M) g a (c + 1)
        (ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1)
          (slotExtend (I := I) (M := M) g b c Φ)
          (covGrad (I := I) (M := M) g a b X)).toFun
        (covGrad (I := I) (M := M) g a c V).toFun =
      - tensorL2Inner (I := I) (M := M) g a c
          (rawTensorConnLapSmooth (I := I) g a c
            (ccOperatorFieldComp (I := I) (M := M) g a b c Φ X)).toFun V.toFun -
        tensorL2Inner (I := I) (M := M) g a (c + 1)
          (ccOperatorFieldComp (I := I) (M := M) g a b (c + 1)
            (covGrad (I := I) (M := M) g b c Φ) X).toFun
          (covGrad (I := I) (M := M) g a c V).toFun := by
  classical
  have hsplit := tensorL2Inner_covGrad_operatorFieldComposition_eq_add (I := I) (M := M) g a b c Φ X
    (covGrad (I := I) (M := M) g a c V)
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a b c Φ X) V
  rw [hgreen] at hsplit
  linarith [hsplit]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldComposition_slotExtend_input_covGrad_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldComposition_slotExtend_input_covGrad_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldComposition_slotExtend_input_covGrad_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_operatorFieldComposition_slotExtend_input_covGrad_eq

theorem tensorL2Inner_rawConnLap_operatorFieldComposition_eq_neg_covGrad_split (g : SmoothRiemannianMetric I M)
    (a b c : ℕ) (A : SmoothCcTensor g a c) (Φ : SmoothCcTensor g b c)
    (W : SmoothCcTensor g a b) :
    tensorL2Inner (I := I) (M := M) g a c
        (rawTensorConnLapSmooth (I := I) g a c A).toFun
        (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toFun =
      - tensorL2Inner (I := I) (M := M) g a (c + 1)
          (covGrad (I := I) (M := M) g a c A).toFun
          (ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1)
            (slotExtend (I := I) (M := M) g b c Φ)
            (covGrad (I := I) (M := M) g a b W)).toFun -
        tensorL2Inner (I := I) (M := M) g a (c + 1)
          (covGrad (I := I) (M := M) g a c A).toFun
          (ccOperatorFieldComp (I := I) (M := M) g a b (c + 1)
            (covGrad (I := I) (M := M) g b c Φ) W).toFun := by
  classical
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g a c A (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W)
  have hsplit := tensorL2Inner_covGrad_operatorFieldComposition_eq_add (I := I) (M := M) g a b c Φ W
    (covGrad (I := I) (M := M) g a c A)
  have hsymm0 := tensorL2Inner_symm (I := I) (M := M) g a (c + 1)
    (covGrad (I := I) (M := M) g a c A).toFun
    (covGrad (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W)).toFun
  have hsymm1 := tensorL2Inner_symm (I := I) (M := M) g a (c + 1)
    (ccOperatorFieldComp (I := I) (M := M) g a b (c + 1) (covGrad (I := I) (M := M) g b c Φ)
      W).toFun
    (covGrad (I := I) (M := M) g a c A).toFun
  have hsymm2 := tensorL2Inner_symm (I := I) (M := M) g a (c + 1)
    (ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1)
      (slotExtend (I := I) (M := M) g b c Φ)
      (covGrad (I := I) (M := M) g a b W)).toFun
    (covGrad (I := I) (M := M) g a c A).toFun
  linarith [hgreen, hsplit, hsymm0, hsymm1, hsymm2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_rawConnLap_operatorFieldComposition_eq_neg_covGrad_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_rawConnLap_operatorFieldComposition_eq_neg_covGrad_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_rawConnLap_operatorFieldComposition_eq_neg_covGrad_split ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_rawConnLap_operatorFieldComposition_eq_neg_covGrad_split

end Elliptic
end Analysis
end DifferentialGeometry

end
