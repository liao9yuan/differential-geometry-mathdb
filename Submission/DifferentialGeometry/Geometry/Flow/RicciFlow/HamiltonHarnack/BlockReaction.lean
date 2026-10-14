import Submission.DifferentialGeometry.Analysis.Spectral.HamiltonGramReaction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.BlockEvolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped _root_.BigOperators

variable {Idx : Type*} [Fintype Idx]

def hamiltonBlockJ
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) : Real :=
  2 * (∑ a, ∑ b, ∑ c, ∑ d,
    K a c b d * M c d * W a * W b) -
  2 * (∑ a, ∑ b, ∑ c, ∑ d,
    P a c d * P b d c * W a * W b) +
  8 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    K a d c e * P d b e * U a b * W c) +
  4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    K a e c f * K b e d f * U a b * U c d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ

def hamiltonBlockPreSquare
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) : Real :=
  hamiltonBlockJ K P M U W +
    hamiltonBlockSigmaSquareExpanded K P U W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquare ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquare

def hamiltonBlockPreSquareK
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) : Real :=
  4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    K a e c f * K b e d f * U a b * U c d) +
    ∑ a, ∑ b, (∑ c, ∑ d, K a b c d * U c d) ^ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquareK then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquareK"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquareK ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquareK

def hamiltonBlockPreSquareP
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) : Real :=
  8 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    K a d c e * P d b e * U a b * W c) +
    2 * (∑ a, ∑ b,
      (∑ c, P a b c * W c) * (∑ d, ∑ e, K a b d e * U d e))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquareP then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquareP"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquareP ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquareP

def hamiltonBlockPreSquareM
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (W : Idx -> Real) : Real :=
  2 * (∑ a, ∑ b, ∑ c, ∑ d,
    K a c b d * M c d * W a * W b) -
  2 * (∑ a, ∑ b, ∑ c, ∑ d,
    P a c d * P b d c * W a * W b) +
  ∑ a, ∑ b, (∑ c, P a b c * W c) ^ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquareM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquareM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquareM ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquareM

theorem hamiltonBlockJ_add_blocks
    (K dK : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M dM : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) :
    hamiltonBlockJ (fun a b c d => K a b c d + dK a b c d) P
        (fun a b => M a b + dM a b) U W =
      hamiltonBlockJ K P M U W +
        2 * (∑ a, ∑ b, ∑ c, ∑ d,
          K a c b d * dM c d * W a * W b) +
        2 * (∑ a, ∑ b, ∑ c, ∑ d,
          dK a c b d * M c d * W a * W b) +
        2 * (∑ a, ∑ b, ∑ c, ∑ d,
          dK a c b d * dM c d * W a * W b) +
        8 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          dK a d c e * P d b e * U a b * W c) +
        4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
          K a e c f * dK b e d f * U a b * U c d) +
        4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
          dK a e c f * K b e d f * U a b * U c d) +
        4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
          dK a e c f * dK b e d f * U a b * U c d) := by
  unfold hamiltonBlockJ
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ_add_blocks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ_add_blocks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ_add_blocks ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ_add_blocks

theorem hamiltonBlockPreSquare_eq_split
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) :
    hamiltonBlockPreSquare K P M U W =
      hamiltonBlockPreSquareK K U +
        hamiltonBlockPreSquareP K P U W +
        hamiltonBlockPreSquareM K P M W := by
  unfold hamiltonBlockPreSquare hamiltonBlockJ
    hamiltonBlockSigmaSquareExpanded hamiltonBlockPreSquareK
    hamiltonBlockPreSquareP hamiltonBlockPreSquareM
  simp only [Finset.sum_add_distrib]
  have hmix :
      (∑ a, ∑ b,
        (2 * ∑ c, P a b c * W c) *
            (∑ d, ∑ e, K a b d e * U d e)) =
        2 * (∑ a, ∑ b,
          (∑ c, P a b c * W c) *
            (∑ d, ∑ e, K a b d e * U d e)) := by
    calc
      (∑ a, ∑ b,
          (2 * ∑ c, P a b c * W c) *
              (∑ d, ∑ e, K a b d e * U d e)) =
          ∑ a, ∑ b, 2 *
            ((∑ c, P a b c * W c) *
              (∑ d, ∑ e, K a b d e * U d e)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      _ = 2 * (∑ a, ∑ b,
          (∑ c, P a b c * W c) *
            (∑ d, ∑ e, K a b d e * U d e)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
  rw [hmix]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquare_eq_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquare_eq_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquare_eq_split ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockPreSquare_eq_split

theorem hamiltonBlock_pre_square_eq_j_add_sigma_square
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) :
    hamiltonBlockPreSquare K P M U W =
      hamiltonBlockJ K P M U W + hamiltonBlockSigmaSquare K P U W := by
  unfold hamiltonBlockPreSquare
  rw [hamiltonBlock_sigma_square_expand]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_pre_square_eq_j_add_sigma_square then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_pre_square_eq_j_add_sigma_square"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_pre_square_eq_j_add_sigma_square ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_pre_square_eq_j_add_sigma_square

theorem hamiltonBlockJ_eq_reaction_polynomial_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real) :
    hamiltonBlockJ
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W =
      DifferentialGeometry.Analysis.Spectral.hamiltonReactionPolynomial
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ_eq_reaction_polynomial_of_gram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ_eq_reaction_polynomial_of_gram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ_eq_reaction_polynomial_of_gram ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ_eq_reaction_polynomial_of_gram

theorem hamiltonBlockJ_nonneg_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real)
    (hY : ∀ r a b, Y r a b = -Y r b a)
    (hU : ∀ a b, U a b = -U b a) :
    0 ≤ hamiltonBlockJ
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W := by
  rw [hamiltonBlockJ_eq_reaction_polynomial_of_gram]
  exact DifferentialGeometry.Analysis.Spectral.hamiltonReactionPolynomial_nonneg_of_gram
    Y X U W hY hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ_nonneg_of_gram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ_nonneg_of_gram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ_nonneg_of_gram ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockJ_nonneg_of_gram

theorem hamiltonBlock_pre_square_nonneg_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real)
    (hY : ∀ r a b, Y r a b = -Y r b a)
    (hU : ∀ a b, U a b = -U b a) :
    0 ≤ hamiltonBlockPreSquare
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W := by
  rw [hamiltonBlock_pre_square_eq_j_add_sigma_square]
  exact add_nonneg
    (hamiltonBlockJ_nonneg_of_gram Y X U W hY hU)
    (by
      unfold hamiltonBlockSigmaSquare
      exact Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => sq_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_pre_square_nonneg_of_gram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_pre_square_nonneg_of_gram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_pre_square_nonneg_of_gram ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_pre_square_nonneg_of_gram

end DifferentialGeometry.PDE.RicciFlow
