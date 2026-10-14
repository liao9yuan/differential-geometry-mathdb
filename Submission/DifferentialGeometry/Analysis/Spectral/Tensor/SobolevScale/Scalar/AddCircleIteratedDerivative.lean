import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleFiniteRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.ContDiff
namespace AddCircle
open _root_.AddCircle
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

open _root_.AddCircle in
def iteratedParameterDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (n : ℕ) : (k : ℕ) →
      TensorHs g 0 0 ((n + k : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 (n : ℝ)
  | 0 => ContinuousLinearMap.id ℝ _
  | k + 1 => (iteratedParameterDerivativeHs g n k).comp
      ((parameterDerivativeHs g (n + k)).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith :
            ((n + k : ℕ) : ℝ) + 1 ≤ ((n + (k + 1) : ℕ) : ℝ))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.iteratedParameterDerivativeHs then
    throwError "Refusing to shadow existing declaration AddCircle.iteratedParameterDerivativeHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.iteratedParameterDerivativeHs ``Submission.AddCircle.iteratedParameterDerivativeHs

open _root_.AddCircle in
@[simp] theorem iteratedParameterDerivativeHs_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    iteratedParameterDerivativeHs g n 0 = ContinuousLinearMap.id ℝ _ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.iteratedParameterDerivativeHs_zero then
    throwError "Refusing to shadow existing declaration AddCircle.iteratedParameterDerivativeHs_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.iteratedParameterDerivativeHs_zero ``Submission.AddCircle.iteratedParameterDerivativeHs_zero

open _root_.AddCircle in
theorem iteratedParameterDerivativeHs_succ_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n k : ℕ)
    (u : TensorHs g 0 0 ((n + (k + 1) : ℕ) : ℝ)) :
    iteratedParameterDerivativeHs g n (k + 1) u =
      iteratedParameterDerivativeHs g n k
        (parameterDerivativeHs g (n + k)
          (tensorHsInclusion (by push_cast; linarith :
            ((n + k : ℕ) : ℝ) + 1 ≤ ((n + (k + 1) : ℕ) : ℝ)) u)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.iteratedParameterDerivativeHs_succ_apply then
    throwError "Refusing to shadow existing declaration AddCircle.iteratedParameterDerivativeHs_succ_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.iteratedParameterDerivativeHs_succ_apply ``Submission.AddCircle.iteratedParameterDerivativeHs_succ_apply

open _root_.AddCircle in
theorem iteratedParameterDerivativeHs_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n k : ℕ)
    (S : SmoothCcTensor g 0 0) :
    iteratedParameterDerivativeHs g n k (ccTensorToHs g 0 ((n + k : ℕ) : ℝ) S) =
      ccTensorToHs g 0 (n : ℝ) ((parameterDerivativeCcTensor g)^[k] S) := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
      simp only [iteratedParameterDerivativeHs_succ_apply,
        tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
        ih, Function.iterate_succ_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.iteratedParameterDerivativeHs_apply_ccTensorToHs then
    throwError "Refusing to shadow existing declaration AddCircle.iteratedParameterDerivativeHs_apply_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.iteratedParameterDerivativeHs_apply_ccTensorToHs ``Submission.AddCircle.iteratedParameterDerivativeHs_apply_ccTensorToHs

open _root_.AddCircle in
theorem iteratedParameterDerivativeHs_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) (k : ℕ)
    (u : TensorHs g 0 0 ((m + k : ℕ) : ℝ)) :
    iteratedParameterDerivativeHs g n k
        (tensorHsInclusion (by exact_mod_cast Nat.add_le_add_right h k :
          ((n + k : ℕ) : ℝ) ≤ ((m + k : ℕ) : ℝ)) u) =
      tensorHsInclusion (by exact_mod_cast h : (n : ℝ) ≤ (m : ℝ))
        (iteratedParameterDerivativeHs g m k u) := by
  let L := (iteratedParameterDerivativeHs g n k).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast Nat.add_le_add_right h k :
        ((n + k : ℕ) : ℝ) ≤ ((m + k : ℕ) : ℝ)))
  let R := (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by exact_mod_cast h : (n : ℝ) ≤ (m : ℝ))).comp
      (iteratedParameterDerivativeHs g m k)
  have heq : (L : _ → _) = R :=
    (ccToHsLin_dense g 0 (by positivity : (0 : ℝ) ≤ ((m + k : ℕ) : ℝ))).equalizer
      L.continuous R.continuous (by
        funext S
        simp only [L, R, Function.comp_apply, ContinuousLinearMap.comp_apply,
          ccToHsLin_apply, tensorHsInclusion_ccTensorToHs,
          iteratedParameterDerivativeHs_apply_ccTensorToHs])
  exact congrFun heq u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.iteratedParameterDerivativeHs_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration AddCircle.iteratedParameterDerivativeHs_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.iteratedParameterDerivativeHs_tensorHsInclusion ``Submission.AddCircle.iteratedParameterDerivativeHs_tensorHsInclusion

open _root_.AddCircle in
theorem parameterDerivativeHs_iteratedParameterDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n k : ℕ)
    (u : TensorHs g 0 0 ((n + (k + 1) : ℕ) : ℝ)) :
    parameterDerivativeHs g n
        (tensorHsInclusion (by push_cast; rfl : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ))
          (iteratedParameterDerivativeHs g (n + 1) k
            (tensorHsInclusion (by push_cast; linarith :
              ((n + 1 + k : ℕ) : ℝ) ≤ ((n + (k + 1) : ℕ) : ℝ)) u))) =
      iteratedParameterDerivativeHs g n (k + 1) u := by
  let L := (parameterDerivativeHs g n).comp
    ((tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; rfl : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ))).comp
        ((iteratedParameterDerivativeHs g (n + 1) k).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith :
              ((n + 1 + k : ℕ) : ℝ) ≤ ((n + (k + 1) : ℕ) : ℝ)))))
  let R := iteratedParameterDerivativeHs g n (k + 1)
  have heq : (L : _ → _) = R :=
    (ccToHsLin_dense g 0 (by positivity :
      (0 : ℝ) ≤ ((n + (k + 1) : ℕ) : ℝ))).equalizer L.continuous R.continuous (by
        funext S
        simp only [L, R, Function.comp_apply, ContinuousLinearMap.comp_apply,
          ccToHsLin_apply, tensorHsInclusion_ccTensorToHs,
          iteratedParameterDerivativeHs_apply_ccTensorToHs,
          parameterDerivativeHs_apply_ccTensorToHs, Function.iterate_succ_apply'])
  exact congrFun heq u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeHs_iteratedParameterDerivativeHs then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeHs_iteratedParameterDerivativeHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeHs_iteratedParameterDerivativeHs ``Submission.AddCircle.parameterDerivativeHs_iteratedParameterDerivativeHs

open _root_.AddCircle in
theorem parameterSecondDerivativeHs_iteratedParameterDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n k : ℕ)
    (u : TensorHs g 0 0 ((n + (k + 2) : ℕ) : ℝ)) :
    parameterSecondDerivativeHs g n
        (tensorHsInclusion (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ))
          (iteratedParameterDerivativeHs g (n + 2) k
            (tensorHsInclusion (by push_cast; linarith :
              ((n + 2 + k : ℕ) : ℝ) ≤ ((n + (k + 2) : ℕ) : ℝ)) u))) =
      iteratedParameterDerivativeHs g n (k + 2) u := by
  let L := (parameterSecondDerivativeHs g n).comp
    ((tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ))).comp
        ((iteratedParameterDerivativeHs g (n + 2) k).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith :
              ((n + 2 + k : ℕ) : ℝ) ≤ ((n + (k + 2) : ℕ) : ℝ)))))
  let R := iteratedParameterDerivativeHs g n (k + 2)
  have heq : (L : _ → _) = R :=
    (ccToHsLin_dense g 0 (by positivity :
      (0 : ℝ) ≤ ((n + (k + 2) : ℕ) : ℝ))).equalizer L.continuous R.continuous (by
        funext S
        simp only [L, R, Function.comp_apply, ContinuousLinearMap.comp_apply,
          ccToHsLin_apply, tensorHsInclusion_ccTensorToHs,
          iteratedParameterDerivativeHs_apply_ccTensorToHs,
          parameterSecondDerivativeHs_apply_ccTensorToHs, Function.iterate_succ_apply'])
  exact congrFun heq u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterSecondDerivativeHs_iteratedParameterDerivativeHs then
    throwError "Refusing to shadow existing declaration AddCircle.parameterSecondDerivativeHs_iteratedParameterDerivativeHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterSecondDerivativeHs_iteratedParameterDerivativeHs ``Submission.AddCircle.parameterSecondDerivativeHs_iteratedParameterDerivativeHs

open _root_.AddCircle in
theorem scalarH1ToContinuous_iteratedParameterDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (u : TensorHs g 0 0 ((n + k : ℕ) : ℝ)) :
    (fun x : ℝ => scalarH1ToContinuous g
      (tensorHsInclusion (by exact_mod_cast hn : (1 : ℝ) ≤ (n : ℝ))
        (iteratedParameterDerivativeHs g n k u)) (x : AddCircle (1 : ℝ))) =
      iteratedDeriv k (fun x : ℝ => scalarH1ToContinuous g
        (tensorHsInclusion (by exact_mod_cast (show 1 ≤ n + k by omega) :
          (1 : ℝ) ≤ ((n + k : ℕ) : ℝ)) u) (x : AddCircle (1 : ℝ))) := by
  induction k with
  | zero =>
      simp only [iteratedDeriv_zero, iteratedParameterDerivativeHs_zero,
        ContinuousLinearMap.id_apply]
  | succ k ih =>
      let U := tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((n + k : ℕ) : ℝ) + 1 ≤ ((n + (k + 1) : ℕ) : ℝ)) u
      let v := parameterDerivativeHs g (n + k) U
      have hder := deriv_scalarH1ToContinuous g (show 1 ≤ n + k by omega) U
      have hrec := ih v
      rw [iteratedDeriv_succ']
      rw [show (fun x : ℝ => scalarH1ToContinuous g
          (tensorHsInclusion (by exact_mod_cast (show 1 ≤ n + (k + 1) by omega) :
            (1 : ℝ) ≤ ((n + (k + 1) : ℕ) : ℝ)) u) (x : AddCircle (1 : ℝ))) =
          (fun x : ℝ => scalarH1ToContinuous g
            (tensorHsInclusion (by
              have hn0 : (0 : ℝ) ≤ ((n + k : ℕ) : ℝ) := Nat.cast_nonneg _
              linarith : (1 : ℝ) ≤ ((n + k : ℕ) : ℝ) + 1) U)
              (x : AddCircle (1 : ℝ))) by
            simp only [U, ← tensorHsInclusion_trans_apply]]
      rw [hder]
      exact hrec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.scalarH1ToContinuous_iteratedParameterDerivativeHs then
    throwError "Refusing to shadow existing declaration AddCircle.scalarH1ToContinuous_iteratedParameterDerivativeHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.scalarH1ToContinuous_iteratedParameterDerivativeHs ``Submission.AddCircle.scalarH1ToContinuous_iteratedParameterDerivativeHs


end AddCircle

end

noncomputable section
open scoped _root_.Manifold _root_.ContDiff
namespace AddCircle
open _root_.AddCircle
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_1 : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry_1 target :: scope.openDecls } }

open _root_.AddCircle in
theorem iteratedParameterDerivativeHs_parameterSecondDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n k : ℕ)
    (u : TensorHs g 0 0 (((n + k : ℕ) : ℝ) + 2)) :
    iteratedParameterDerivativeHs g n k (parameterSecondDerivativeHs g (n + k) u) =
      parameterSecondDerivativeHs g n
        (tensorHsInclusion (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ))
          (iteratedParameterDerivativeHs g (n + 2) k
            (tensorHsInclusion (by push_cast; linarith :
              ((n + 2 + k : ℕ) : ℝ) ≤ ((n + k : ℕ) : ℝ) + 2) u))) := by
  let L := (iteratedParameterDerivativeHs g n k).comp
    (parameterSecondDerivativeHs g (n + k))
  let R := (parameterSecondDerivativeHs g n).comp
    ((tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ))).comp
        ((iteratedParameterDerivativeHs g (n + 2) k).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith :
              ((n + 2 + k : ℕ) : ℝ) ≤ ((n + k : ℕ) : ℝ) + 2))))
  have heq : (L : _ → _) = R :=
    (ccToHsLin_dense g 0 (by positivity :
      (0 : ℝ) ≤ ((n + k : ℕ) : ℝ) + 2)).equalizer L.continuous R.continuous (by
        funext S
        simp only [L, R, Function.comp_apply, ContinuousLinearMap.comp_apply,
          ccToHsLin_apply, tensorHsInclusion_ccTensorToHs,
          iteratedParameterDerivativeHs_apply_ccTensorToHs,
          parameterSecondDerivativeHs_apply_ccTensorToHs]
        apply congrArg (ccTensorToHs g 0 (n : ℝ))
        calc
          _ = (parameterDerivativeCcTensor g)^[k + 2] S := by
            simp only [Function.iterate_succ_apply]
          _ = _ := by simp only [Function.iterate_succ_apply']
    )
  exact congrFun heq u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.iteratedParameterDerivativeHs_parameterSecondDerivativeHs then
    throwError "Refusing to shadow existing declaration AddCircle.iteratedParameterDerivativeHs_parameterSecondDerivativeHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.iteratedParameterDerivativeHs_parameterSecondDerivativeHs ``Submission.AddCircle.iteratedParameterDerivativeHs_parameterSecondDerivativeHs

end AddCircle
end
