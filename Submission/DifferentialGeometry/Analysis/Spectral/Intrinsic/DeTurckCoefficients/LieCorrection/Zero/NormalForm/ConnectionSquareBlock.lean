import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.Zero.NormalForm.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open scoped _root_.BigOperators

namespace DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm

private lemma p2_h1 {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (ga1 : Fin n → Fin n → Fin n → ℝ) (hfs : ∀ a b, f a b = f b a)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3,
      (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) =
      (2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d,
        f a b * ga1 i j a * ga1 c d b * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs b a]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.p2_h1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.p2_h1 target :: scope.openDecls } }

private lemma p2_h2 {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (ga0 ga1 : Fin n → Fin n → Fin n → ℝ) (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3,
      (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) =
      (2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d,
        f a b * ga0 c d a * ga1 i j b * ig c d) := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.p2_h2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.p2_h2 target :: scope.openDecls } }

private lemma p2_h3 {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (ga0 ga1 : Fin n → Fin n → Fin n → ℝ) (hfs : ∀ a b, f a b = f b a)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3,
      (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga0 i j b1 * f b0 b1))) =
      (2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d,
        f a b * ga0 i j a * ga1 c d b * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs b a]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.p2_h3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.p2_h3 target :: scope.openDecls } }

private lemma p2_h4 {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (ga0 : Fin n → Fin n → Fin n → ℝ) (hfs : ∀ a b, f a b = f b a)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3,
      (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga0 i j b1 * f b0 b1))) =
      (2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d,
        f a b * ga0 i j a * ga0 c d b * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs b a]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.p2_h4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.p2_h4 target :: scope.openDecls } }


theorem connection_square_block_normal_form {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (ga0 ga1 : Fin n → Fin n → Fin n → ℝ)
    (hfs : ∀ a b, f a b = f b a) (i j : Fin n) :
    connectionSquareBlock ig ga1 ga0 f i j =
      ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga1 c d b * ig c d))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j b * ig c d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga1 i j a * ga1 c d b * ig c d)) := by
  have h1 : connectionSquareBlock ig ga1 ga0 f i j =
      (∑ b0, ∑ b1, ∑ b2, ∑ b3,
        (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) -
      (∑ b0, ∑ b1, ∑ b2, ∑ b3,
        (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) -
      ((∑ b0, ∑ b1, ∑ b2, ∑ b3,
        (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga0 i j b1 * f b0 b1))) -
      (∑ b0, ∑ b1, ∑ b2, ∑ b3,
        (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga0 i j b1 * f b0 b1)))) := by
    simp only [connectionSquareBlock]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul,
      mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [h1, p2_h1 ig f ga1 hfs i j, p2_h2 ig f ga0 ga1 i j,
    p2_h3 ig f ga0 ga1 hfs i j, p2_h4 ig f ga0 hfs i j]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connection_square_block_normal_form then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connection_square_block_normal_form"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connection_square_block_normal_form ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connection_square_block_normal_form

end DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm
