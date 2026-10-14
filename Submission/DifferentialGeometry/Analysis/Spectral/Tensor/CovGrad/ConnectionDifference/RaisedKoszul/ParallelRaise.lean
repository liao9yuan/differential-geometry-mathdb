import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Algebra.IteratedApplication
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.JetTower

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.Submission.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem operatorFieldComposition_zero_right (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) :
    ccOperatorFieldComp (I := I) (M := M) g a b c Φ (0 : SmoothCcTensor g a b) = 0 := by
  have h := operatorFieldComposition_add_right (I := I) (M := M) g a b c Φ 0 0
  rw [add_zero] at h
  have h0 : ccOperatorFieldComp (I := I) (M := M) g a b c Φ 0 + (0 : SmoothCcTensor g a c) =
      ccOperatorFieldComp (I := I) (M := M) g a b c Φ 0 +
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ 0 := by
    rw [add_zero]; exact h
  exact (add_left_cancel h0).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.operatorFieldComposition_zero_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.operatorFieldComposition_zero_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.operatorFieldComposition_zero_right ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.operatorFieldComposition_zero_right

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem iteratedCovGrad_eq_zero_of_covGrad_eq_zero (g : SmoothRiemannianMetric I M) (a b : ℕ)
    (W : SmoothCcTensor g a b)
    (hW : covGrad (I := I) (M := M) g a b W = 0) :
    ∀ k : ℕ, iteratedCovGrad (I := I) g a b (k + 1) W = 0 := by
  intro k
  induction k with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact hW
  | succ k ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_eq_zero_of_covGrad_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_eq_zero_of_covGrad_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_eq_zero_of_covGrad_eq_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_eq_zero_of_covGrad_eq_zero

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma operatorFieldApplicationLeibnizPsi_order_zero (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i : ℕ) :
    operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i 0 =
      iteratedCovGrad (I := I) g b c i Φ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      change covGrad (I := I) (M := M) g b (c + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i 0) =
          iteratedCovGrad (I := I) g b c (i + 1) Φ
      rw [ih, iteratedCovGrad_succ]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.operatorFieldApplicationLeibnizPsi_order_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.operatorFieldApplicationLeibnizPsi_order_zero target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem iteratedCovGrad_operatorFieldCompose_of_covGrad_right_eq_zero
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b)
    (hW : covGrad (I := I) (M := M) g a b W = 0) (i : ℕ) :
    iteratedCovGrad (I := I) g a c i
        (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) =
      ccOperatorFieldComp (I := I) (M := M) g a b (c + i)
        (iteratedCovGrad (I := I) g b c i Φ) W := by
  classical
  rw [iteratedCovGrad_operatorFieldComposition_eq (I := I) (M := M) g a b c Φ W i]
  rw [Finset.sum_eq_single 0]
  · rw [iteratedCovGrad_zero, operatorFieldApplicationLeibnizPsi_order_zero]
    rfl
  · intro k _ hk0
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    rw [iteratedCovGrad_eq_zero_of_covGrad_eq_zero (I := I) (M := M) g a b W hW k',
      operatorFieldComposition_zero_right]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos i)) h0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_operatorFieldCompose_of_covGrad_right_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_operatorFieldCompose_of_covGrad_right_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_operatorFieldCompose_of_covGrad_right_eq_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_operatorFieldCompose_of_covGrad_right_eq_zero

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
