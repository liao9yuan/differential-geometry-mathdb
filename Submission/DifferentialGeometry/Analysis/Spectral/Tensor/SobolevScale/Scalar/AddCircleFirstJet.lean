import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleClassicalDerivative

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
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {ι : Type*}
open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

open _root_.AddCircle in
def firstJetHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι ⊕ ι => TensorHs g 0 0 (n : ℝ)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ⊕ ι => TensorHs g 0 0 (n : ℝ))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => match j with
      | .inl i =>
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)).comp
              (PiLp.proj 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1)) i)
      | .inr i =>
          (parameterDerivativeHs g n).comp
            (PiLp.proj 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1)) i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.firstJetHs then
    throwError "Refusing to shadow existing declaration AddCircle.firstJetHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.firstJetHs ``Submission.AddCircle.firstJetHs

open _root_.AddCircle in
@[simp] theorem firstJetHs_inl
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))) (i : ι) :
    firstJetHs g n u (.inl i) =
      tensorHsInclusion (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith) (u i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.firstJetHs_inl then
    throwError "Refusing to shadow existing declaration AddCircle.firstJetHs_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.firstJetHs_inl ``Submission.AddCircle.firstJetHs_inl

open _root_.AddCircle in
@[simp] theorem firstJetHs_inr
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))) (i : ι) :
    firstJetHs g n u (.inr i) = parameterDerivativeHs g n (u i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.firstJetHs_inr then
    throwError "Refusing to shadow existing declaration AddCircle.firstJetHs_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.firstJetHs_inr ``Submission.AddCircle.firstJetHs_inr

open _root_.AddCircle in
theorem firstJetHs_injective
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    Function.Injective (firstJetHs (ι := ι) g n) := by
  intro u v huv
  apply PiLp.ext
  intro i
  exact tensorHsInclusion_injective (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
    (congrArg (fun w => w (.inl i)) huv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.firstJetHs_injective then
    throwError "Refusing to shadow existing declaration AddCircle.firstJetHs_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.firstJetHs_injective ``Submission.AddCircle.firstJetHs_injective

open _root_.AddCircle in
theorem firstJetHs_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (S : ι → SmoothCcTensor g 0 0) :
    firstJetHs g n (WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((n : ℝ) + 1) (S i))) =
      WithLp.toLp 2 (fun j => ccTensorToHs g 0 (n : ℝ)
        (Sum.elim S (fun i => parameterDerivativeCcTensor g (S i)) j)) := by
  apply PiLp.ext
  intro j
  cases j with
  | inl i =>
    change tensorHsInclusion (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
      (ccTensorToHs g 0 ((n : ℝ) + 1) (S i)) = ccTensorToHs g 0 (n : ℝ) (S i)
    rw [tensorHsInclusion_ccTensorToHs]
  | inr i => exact parameterDerivativeHs_apply_ccTensorToHs g n (S i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.firstJetHs_apply_ccTensorToHs then
    throwError "Refusing to shadow existing declaration AddCircle.firstJetHs_apply_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.firstJetHs_apply_ccTensorToHs ``Submission.AddCircle.firstJetHs_apply_ccTensorToHs

open _root_.AddCircle in
theorem firstJetHs_comp_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {n m : ℕ} (h : n ≤ m) :
    (firstJetHs (ι := ι) g n).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 1 ≤ (m : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right h 1))) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h))).comp
            (firstJetHs g m) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro j
  cases j with
  | inl i =>
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.piLpMap_apply,
      firstJetHs_inl]
    apply TensorHs.ext
    rfl
  | inr i => exact parameterDerivativeHs_tensorHsInclusion g h (u i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.firstJetHs_comp_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration AddCircle.firstJetHs_comp_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.firstJetHs_comp_tensorHsInclusion ``Submission.AddCircle.firstJetHs_comp_tensorHsInclusion

end AddCircle
