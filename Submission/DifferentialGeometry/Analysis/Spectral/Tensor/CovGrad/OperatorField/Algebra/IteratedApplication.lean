import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.ApplicationJets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

def operatorFieldApplicationLeibnizPsi (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) :
    ∀ (i k : ℕ), SmoothCcTensor g (b + k) (c + i)
  | 0, k => match k with
      | 0 => Φ
      | (_ + 1) => 0
  | (i + 1), k => match k with
      | 0 => covGrad (I := I) (M := M) g (b + 0) (c + i) (operatorFieldApplicationLeibnizPsi g b c Φ i 0)
      | (j + 1) =>
          (if j + 1 < i + 1 then
              covGrad (I := I) (M := M) g (b + (j + 1)) (c + i) (operatorFieldApplicationLeibnizPsi g b c Φ i (j + 1))
            else 0) +
            castCcTensorSourceRank g (c + (i + 1)) (by omega : (b + j) + 1 = b + (j + 1))
              (castCcTensorRank g ((b + j) + 1) (by omega : (c + i) + 1 = c + (i + 1))
                (slotExtend (I := I) (M := M) g (b + j) (c + i) (operatorFieldApplicationLeibnizPsi g b c Φ i j)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplicationLeibnizPsi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplicationLeibnizPsi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplicationLeibnizPsi ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplicationLeibnizPsi


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem covGrad_operatorFieldApplicationLeibniz_sum (g : SmoothRiemannianMetric I M) (a b c i : ℕ)
    (Ψ : (k : ℕ) → SmoothCcTensor g (b + k) (c + i)) (W : SmoothCcTensor g a b) :
    covGrad (I := I) (M := M) g a (c + i)
        (∑ k ∈ Finset.range (i + 1),
          ccOperatorFieldComp (I := I) (M := M) g a (b + k) (c + i) (Ψ k)
            (iteratedCovGrad g a b k W)) =
      ∑ k ∈ Finset.range (i + 1),
        (ccOperatorFieldComp (I := I) (M := M) g a (b + k) (c + (i + 1))
            (covGrad (I := I) (M := M) g (b + k) (c + i) (Ψ k)) (iteratedCovGrad g a b k W) +
          ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
            (slotExtend (I := I) (M := M) g (b + k) (c + i) (Ψ k))
            (iteratedCovGrad g a b (k + 1) W)) := by
  rw [covGrad_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covGrad_operatorFieldComposition_eq (I := I) (M := M) g a (b + k) (c + i) (Ψ k) (iteratedCovGrad g a b k W)]
  rw [show covGrad (I := I) (M := M) g a (b + k) (iteratedCovGrad g a b k W) =
      iteratedCovGrad g a b (k + 1) W from (iteratedCovGrad_succ g a b k W).symm]
  congr 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.covGrad_operatorFieldApplicationLeibniz_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.covGrad_operatorFieldApplicationLeibniz_sum target :: scope.openDecls } }


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem operatorFieldApplicationLeibnizPsi_succ_zero (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i : ℕ) :
    operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) 0 =
      covGrad (I := I) (M := M) g (b + 0) (c + i) (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i 0) :=
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplicationLeibnizPsi_succ_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.operatorFieldApplicationLeibnizPsi_succ_zero target :: scope.openDecls } }


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem operatorFieldApplicationLeibnizPsi_succ_succ (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i j : ℕ) :
    operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
      (if j + 1 < i + 1 then
          covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
        else 0) +
        castCcTensorSourceRank g (c + (i + 1)) (by omega : (b + j) + 1 = b + (j + 1))
          (castCcTensorRank g ((b + j) + 1) (by omega : (c + i) + 1 = c + (i + 1))
            (slotExtend (I := I) (M := M) g (b + j) (c + i)
              (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i j))) :=
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplicationLeibnizPsi_succ_succ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.operatorFieldApplicationLeibnizPsi_succ_succ target :: scope.openDecls } }


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem iteratedCovGrad_operatorFieldComposition_eq (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (i : ℕ) :
    iteratedCovGrad (I := I) g a c i (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) =
      ∑ k ∈ Finset.range (i + 1),
        ccOperatorFieldComp (I := I) (M := M) g a (b + k) (c + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i k)
          (iteratedCovGrad (I := I) g a b k W) := by
  classical
  induction i with
  | zero =>
      rw [iteratedCovGrad_zero, Finset.sum_range_one, iteratedCovGrad_zero]
      rfl
  | succ i ih =>
      rw [iteratedCovGrad_succ, ih]
      rw [covGrad_operatorFieldApplicationLeibniz_sum (I := I) (M := M) g a b c i
        (fun k => operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i k) W]
      rw [show (∑ k ∈ Finset.range (i + 1),
            (ccOperatorFieldComp (I := I) (M := M) g a (b + k) (c + (i + 1))
                (covGrad (I := I) (M := M) g (b + k) (c + i)
                  (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i k))
                (iteratedCovGrad g a b k W) +
              ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
                (slotExtend (I := I) (M := M) g (b + k) (c + i)
                  (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i k))
                (iteratedCovGrad g a b (k + 1) W))) =
          (∑ k ∈ Finset.range (i + 1),
            ccOperatorFieldComp (I := I) (M := M) g a (b + k) (c + (i + 1))
              (covGrad (I := I) (M := M) g (b + k) (c + i)
                (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i k))
              (iteratedCovGrad g a b k W)) +
          (∑ k ∈ Finset.range (i + 1),
            ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
              (slotExtend (I := I) (M := M) g (b + k) (c + i)
                (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i k))
              (iteratedCovGrad g a b (k + 1) W)) from Finset.sum_add_distrib]
      rw [Finset.sum_range_succ' (fun j =>
        ccOperatorFieldComp (I := I) (M := M) g a (b + j) (c + (i + 1))
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) j)
          (iteratedCovGrad g a b j W)) (i + 1)]
      rw [show (∑ k ∈ Finset.range (i + 1),
            ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
              (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (k + 1))
              (iteratedCovGrad g a b (k + 1) W)) =
          (∑ k ∈ Finset.range (i + 1),
            ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
              (if k + 1 < i + 1 then
                  covGrad (I := I) (M := M) g (b + (k + 1)) (c + i)
                    (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i (k + 1))
                else 0)
              (iteratedCovGrad g a b (k + 1) W)) +
          (∑ k ∈ Finset.range (i + 1),
            ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
              (slotExtend (I := I) (M := M) g (b + k) (c + i)
                (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i k))
              (iteratedCovGrad g a b (k + 1) W)) from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [operatorFieldApplicationLeibnizPsi_succ_succ]
        rw [show castCcTensorSourceRank g (c + (i + 1)) (by omega : (b + k) + 1 = b + (k + 1))
              (castCcTensorRank g ((b + k) + 1) (by omega : (c + i) + 1 = c + (i + 1))
                (slotExtend (I := I) (M := M) g (b + k) (c + i)
                  (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i k))) =
            slotExtend (I := I) (M := M) g (b + k) (c + i)
              (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i k) from by
          rw [castCcTensorRank, castCcTensorSourceRank]]
        rw [operatorFieldComposition_add_left]]
      rw [show (∑ k ∈ Finset.range (i + 1),
            ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
              (if k + 1 < i + 1 then
                  covGrad (I := I) (M := M) g (b + (k + 1)) (c + i)
                    (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i (k + 1))
                else 0)
              (iteratedCovGrad g a b (k + 1) W)) =
          ∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
              (covGrad (I := I) (M := M) g (b + (k + 1)) (c + i)
                (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i (k + 1)))
              (iteratedCovGrad g a b (k + 1) W) from by
        rw [Finset.sum_range_succ]
        rw [if_neg (by omega : ¬ (i + 1 < i + 1)), operatorFieldComposition_zero_left, add_zero]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [if_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < i + 1)]]
      rw [Finset.sum_range_succ' (fun k =>
        ccOperatorFieldComp (I := I) (M := M) g a (b + k) (c + (i + 1))
          (covGrad (I := I) (M := M) g (b + k) (c + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b c Φ i k))
          (iteratedCovGrad g a b k W)) i]
      rw [operatorFieldApplicationLeibnizPsi_succ_zero]
      abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_operatorFieldComposition_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_operatorFieldComposition_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_operatorFieldComposition_eq ``Submission.DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_operatorFieldComposition_eq


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem iteratedCovGrad_operatorFieldApply_eq (g : SmoothRiemannianMetric I M) (b s : ℕ)
    (Φ : SmoothCcTensor g b s) (W : SmoothCcTensor g 0 b) (i : ℕ) :
    iteratedCovGrad (I := I) g 0 s i (operatorFieldApply (I := I) (M := M) g b s Φ W) =
      ∑ k ∈ Finset.range (i + 1),
        ccOperatorFieldComp (I := I) (M := M) g 0 (b + k) (s + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g b s Φ i k)
          (iteratedCovGrad (I := I) g 0 b k W) := by
  rw [← operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g b s Φ W]
  exact iteratedCovGrad_operatorFieldComposition_eq (I := I) (M := M) g 0 b s Φ W i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_operatorFieldApply_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_operatorFieldApply_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_operatorFieldApply_eq ``Submission.DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_operatorFieldApply_eq

end Spectral
end Analysis
end DifferentialGeometry

end
