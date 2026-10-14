import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open scoped _root_.BigOperators

namespace DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm

variable {n : ℕ}


def metricDerivativeBlock (ig : Fin n → Fin n → ℝ)
    (dig ga1 ga0 : Fin n → Fin n → Fin n → ℝ)
    (dga1 dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  (- ∑ ρ, (∑ a, ∑ b, (dig i a b * (ga1 a b ρ - ga0 a b ρ) +
      ig a b * (dga1 i a b ρ - dga0 i a b ρ)) +
    ∑ σ, ga0 i σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ))) * f ρ j) +
  (- ∑ ρ, (∑ a, ∑ b, (dig j a b * (ga1 a b ρ - ga0 a b ρ) +
      ig a b * (dga1 j a b ρ - dga0 j a b ρ)) +
    ∑ σ, ga0 j σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ))) * f i ρ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.metricDerivativeBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.metricDerivativeBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.metricDerivativeBlock ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.metricDerivativeBlock


def connectionSquareBlock (ig : Fin n → Fin n → ℝ) (ga1 ga0 : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  2 * ∑ ρ, ∑ σ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) *
    ((ga1 i j σ - ga0 i j σ) * f ρ σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionSquareBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionSquareBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionSquareBlock ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionSquareBlock


def mixedBackgroundConnectionBlock (ig cg : Fin n → Fin n → ℝ) (ga1 ga0 gbg : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  2 * (∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
      ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
        ((ga1 a b k - gbg a b k) * cg k j)))) +
    ∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
      ig a p * (ig b q * ((ga1 j p ρ - ga0 j p ρ) * (f ρ q *
        ((ga1 a b k - gbg a b k) * cg k i)))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedBackgroundConnectionBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedBackgroundConnectionBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedBackgroundConnectionBlock ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedBackgroundConnectionBlock


def backgroundDeTurckConnectionBlock (ig : Fin n → Fin n → ℝ) (ga1 ga0 gbg : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  (- ∑ m, ∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
      ((ga1 m i ρ - ga0 m i ρ) * f ρ j)) +
  (- ∑ m, ∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
      ((ga1 m j ρ - ga0 m j ρ) * f i ρ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.backgroundDeTurckConnectionBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.backgroundDeTurckConnectionBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.backgroundDeTurckConnectionBlock ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.backgroundDeTurckConnectionBlock


def connectionDifferenceDerivativeDefect (ig : Fin n → Fin n → ℝ) (dig ga1 ga0 gbg :
    Fin n → Fin n → Fin n → ℝ)
    (dga1 dga0 : Fin n → Fin n → Fin n → Fin n → ℝ) (i p : Fin n) : ℝ :=
  ∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - ga0 a b m)) * (ga1 i m p - ga0 i m p) -
    ∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) * (ga1 i m p - ga0 i m p) -
    ((∑ a, ∑ b, (dig i a b * (ga1 a b p - ga0 a b p) +
        ig a b * (dga1 i a b p - dga0 i a b p))) +
      ∑ m, ga1 i m p * (∑ a, ∑ b, ig a b * (ga1 a b m - ga0 a b m)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceDerivativeDefect then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceDerivativeDefect"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceDerivativeDefect ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceDerivativeDefect


def connectionDifferenceInsertion (ig : Fin n → Fin n → ℝ) (dig ga1 ga0 gbg :
    Fin n → Fin n → Fin n → ℝ)
    (dga1 dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  (∑ p, connectionDifferenceDerivativeDefect ig dig ga1 ga0 gbg dga1 dga0 i p * f p j) +
    (∑ p, connectionDifferenceDerivativeDefect ig dig ga1 ga0 gbg dga1 dga0 j p * f i p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceInsertion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceInsertion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceInsertion ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceInsertion

private lemma a1_ga1_symm
    (ig : Fin n → Fin n → ℝ) (dg gb ga1 : Fin n → Fin n → Fin n → ℝ)
    (hgb : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b, dg m a b = dg m b a)
    (hga1 : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (a b k : Fin n) : ga1 a b k = ga1 b a k := by
  rw [hga1, hga1]
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl (fun l _ => ?_))
  rw [hgb, hgb, hdgs a l b, hdgs b l a, hdgs l a b]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.a1_ga1_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.a1_ga1_symm target :: scope.openDecls } }


theorem connectionDifferenceInsertion_decomposition
    (ig : Fin n → Fin n → ℝ) (dg gb dig ga1 ga0 gbg :
      Fin n → Fin n → Fin n → ℝ)
    (dga1 dga0 : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ)
    (hgb : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b, dg m a b = dg m b a)
    (hga1 : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (i j : Fin n) :
    connectionDifferenceInsertion ig dig ga1 ga0 gbg dga1 dga0 f i j =
      metricDerivativeBlock ig dig ga1 ga0 dga1 dga0 f i j + backgroundDeTurckConnectionBlock ig ga1 ga0 gbg f i j := by
  have hga1s : ∀ a b k, ga1 a b k = ga1 b a k :=
    a1_ga1_symm ig dg gb ga1 hgb hdgs hga1
  have hhalf : ∀ (u : Fin n) (F : Fin n → ℝ),
      (∑ p, connectionDifferenceDerivativeDefect ig dig ga1 ga0 gbg dga1 dga0 u p * F p) =
        (- ∑ ρ, (∑ a, ∑ b, (dig u a b * (ga1 a b ρ - ga0 a b ρ) +
            ig a b * (dga1 u a b ρ - dga0 u a b ρ)) +
          ∑ σ, ga0 u σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ))) * F ρ) +
        (- ∑ m, ∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
            ((ga1 m u ρ - ga0 m u ρ) * F ρ)) := by
    intro u F
    have hswap2 : (∑ m, ∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
        ((ga1 m u ρ - ga0 m u ρ) * F ρ)) =
        ∑ ρ, (∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
          (ga1 u m ρ - ga0 u m ρ)) * F ρ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hga1s m u ρ, hga0s m u ρ]
      ring
    have hcomb : (- ∑ ρ, (∑ a, ∑ b, (dig u a b * (ga1 a b ρ - ga0 a b ρ) +
          ig a b * (dga1 u a b ρ - dga0 u a b ρ)) +
        ∑ σ, ga0 u σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ))) * F ρ) +
        (- ∑ ρ, (∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
          (ga1 u m ρ - ga0 u m ρ)) * F ρ) =
      ∑ ρ, (((-((∑ a, ∑ b, (dig u a b * (ga1 a b ρ - ga0 a b ρ) +
          ig a b * (dga1 u a b ρ - dga0 u a b ρ)) +
        ∑ σ, ga0 u σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ)))))
        + (-(∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
          (ga1 u m ρ - ga0 u m ρ)))) * F ρ) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      ring
    rw [hswap2, hcomb]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine congrArg (fun t : ℝ => t * F p) ?_
    rw [connectionDifferenceDerivativeDefect]
    have hkey : (∑ m, ga1 u m p * (∑ a, ∑ b, ig a b * (ga1 a b m - ga0 a b m))) -
        (∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - ga0 a b m)) * (ga1 u m p - ga0 u m p)) =
        ∑ σ, ga0 u σ p * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    linarith [hkey]
  rw [connectionDifferenceInsertion, hhalf i (fun p => f p j), hhalf j (fun p => f i p)]
  rw [metricDerivativeBlock, backgroundDeTurckConnectionBlock]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceInsertion_decomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceInsertion_decomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceInsertion_decomposition ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceInsertion_decomposition


def connectionDifferenceQuadraticBlock (ig cg : Fin n → Fin n → ℝ) (ga1 ga0 : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  2 * ∑ k, ∑ l, ig k l *
    ((∑ c, (ga1 j i c - ga0 j i c) * cg c l) *
      (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceQuadraticBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceQuadraticBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceQuadraticBlock ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceQuadraticBlock

private lemma collapse_sum
    (ig cg : Fin n → Fin n → ℝ)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (higs : ∀ a b, ig a b = ig b a) (hcgs : ∀ a b, cg a b = cg b a)
    (X : Fin n → ℝ) (c : Fin n) :
    (∑ k, (∑ l, ig k l * cg c l) * X k) = X c := by
  have hone : ∀ k, (∑ l, ig k l * cg c l) = if k = c then (1 : ℝ) else 0 := by
    intro k
    rw [show (∑ l, ig k l * cg c l) = ∑ l, cg l c * ig l k from
      Finset.sum_congr rfl (fun l _ => by rw [higs k l, hcgs c l]; ring)]
    exact hcol k c
  rw [Finset.sum_congr rfl (fun k _ => by rw [hone k])]
  rw [Finset.sum_eq_single c]
  · rw [if_pos rfl, one_mul]
  · intro k _ hk
    rw [if_neg hk, _root_.MulZeroClass.zero_mul]
  · intro h
    exact absurd (Finset.mem_univ c) h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.collapse_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.collapse_sum target :: scope.openDecls } }


theorem connectionDifferenceQuadraticBlock_eq
    (ig cg : Fin n → Fin n → ℝ) (dg gb ga1 ga0 : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (higs : ∀ a b, ig a b = ig b a) (hcgs : ∀ a b, cg a b = cg b a)
    (hgb : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b, dg m a b = dg m b a)
    (hga1 : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (i j : Fin n) :
    connectionDifferenceQuadraticBlock ig cg ga1 ga0 f i j = connectionSquareBlock ig ga1 ga0 f i j := by
  have hga1s : ∀ a b k, ga1 a b k = ga1 b a k :=
    a1_ga1_symm ig dg gb ga1 hgb hdgs hga1
  rw [connectionDifferenceQuadraticBlock, connectionSquareBlock]
  refine congrArg (fun t : ℝ => 2 * t) ?_
  have hstep1 : (∑ k, ∑ l, ig k l *
      ((∑ c, (ga1 j i c - ga0 j i c) * cg c l) *
        (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k))) =
    ∑ c, (ga1 j i c - ga0 j i c) *
      ∑ k, (∑ l, ig k l * cg c l) *
        (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k) := by
    have h1 : ∀ k, (∑ l, ig k l *
        ((∑ c, (ga1 j i c - ga0 j i c) * cg c l) *
          (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k))) =
        ∑ c, ∑ l, (ga1 j i c - ga0 j i c) *
          ((ig k l * cg c l) *
            (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) := by
      intro k
      have h2 : ∀ l, ig k l *
          ((∑ c, (ga1 j i c - ga0 j i c) * cg c l) *
            (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) =
          ∑ c, (ga1 j i c - ga0 j i c) *
            ((ig k l * cg c l) *
              (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) := by
        intro l
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        ring
      rw [Finset.sum_congr rfl (fun l _ => h2 l)]
      exact Finset.sum_comm
    rw [Finset.sum_congr rfl (fun k _ => h1 k)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum]
  rw [hstep1]
  have hstep2 : (∑ c, (ga1 j i c - ga0 j i c) *
      ∑ k, (∑ l, ig k l * cg c l) *
        (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) =
      ∑ c, (ga1 j i c - ga0 j i c) *
        (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ c) :=
    Finset.sum_congr rfl (fun c _ => by
      rw [collapse_sum ig cg hcol higs hcgs
        (fun k => (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) c])
  rw [hstep2]
  have hdist : (∑ c, (ga1 j i c - ga0 j i c) *
      (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ c)) =
      ∑ c, ∑ ρ, (ga1 j i c - ga0 j i c) *
        ((∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ c) :=
    Finset.sum_congr rfl (fun c _ => Finset.mul_sum _ _ _)
  rw [hdist, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [hga1s j i σ, hga0s j i σ]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceQuadraticBlock_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceQuadraticBlock_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceQuadraticBlock_eq ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.connectionDifferenceQuadraticBlock_eq


def mixedConnectionHalfBlock (ig cg : Fin n → Fin n → ℝ) (ga1 ga0 gbg : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ m, ∑ ml, ig m ml *
    (∑ a, ∑ al, ig a al *
      ((∑ k, ∑ kl, ig k kl *
        (f k ml * (∑ c, (ga1 al i c - ga0 al i c) * cg c kl))) *
        (∑ d, (ga1 m a d - gbg m a d) * cg d j)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedConnectionHalfBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedConnectionHalfBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedConnectionHalfBlock ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedConnectionHalfBlock


def mixedBackgroundHalfBlock (ig cg : Fin n → Fin n → ℝ) (ga1 ga0 gbg : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
    ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
      ((ga1 a b k - gbg a b k) * cg k j))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedBackgroundHalfBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedBackgroundHalfBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedBackgroundHalfBlock ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedBackgroundHalfBlock


theorem mixedBackgroundHalfBlock_eq
    (ig cg : Fin n → Fin n → ℝ) (dg gb ga1 ga0 gbg : Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → ℝ)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (higs : ∀ a b, ig a b = ig b a) (hcgs : ∀ a b, cg a b = cg b a)
    (hgb : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b, dg m a b = dg m b a)
    (hga1 : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (i j : Fin n) :
    mixedConnectionHalfBlock ig cg ga1 ga0 gbg f i j = mixedBackgroundHalfBlock ig cg ga1 ga0 gbg f i j := by
  have hga1s : ∀ a b k, ga1 a b k = ga1 b a k :=
    a1_ga1_symm ig dg gb ga1 hgb hdgs hga1
  have hinner : ∀ ml al : Fin n,
      (∑ k, ∑ kl, ig k kl *
        (f k ml * (∑ c, (ga1 al i c - ga0 al i c) * cg c kl))) =
      ∑ c, (ga1 al i c - ga0 al i c) * f c ml := by
    intro ml al
    have h1 : ∀ k, (∑ kl, ig k kl *
        (f k ml * (∑ c, (ga1 al i c - ga0 al i c) * cg c kl))) =
        ∑ c, (ga1 al i c - ga0 al i c) * ((∑ kl, ig k kl * cg c kl) * f k ml) := by
      intro k
      have h2 : ∀ kl, ig k kl *
          (f k ml * (∑ c, (ga1 al i c - ga0 al i c) * cg c kl)) =
          ∑ c, (ga1 al i c - ga0 al i c) * ((ig k kl * cg c kl) * f k ml) := by
        intro kl
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        ring
      rw [Finset.sum_congr rfl (fun kl _ => h2 kl), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← Finset.mul_sum]
    refine congrArg (fun t : ℝ => (ga1 al i c - ga0 al i c) * t) ?_
    exact collapse_sum ig cg hcol higs hcgs (fun k => f k ml) c
  have hmid : mixedConnectionHalfBlock ig cg ga1 ga0 gbg f i j =
      ∑ m, ∑ ml, ig m ml *
        (∑ a, ∑ al, ig a al *
          ((∑ c, (ga1 al i c - ga0 al i c) * f c ml) *
            (∑ d, (ga1 m a d - gbg m a d) * cg d j))) := by
    rw [mixedConnectionHalfBlock]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
    refine congrArg (fun t : ℝ => ig m ml * t) ?_
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun al _ => ?_))
    refine congrArg (fun t : ℝ => ig a al * t) ?_
    rw [hinner ml al]
  rw [hmid, mixedBackgroundHalfBlock]
  have hL : (∑ m, ∑ ml, ig m ml *
      (∑ a, ∑ al, ig a al *
        ((∑ c, (ga1 al i c - ga0 al i c) * f c ml) *
          (∑ d, (ga1 m a d - gbg m a d) * cg d j)))) =
      ∑ m, ∑ ml, ∑ a, ∑ al, ∑ c, ∑ d,
        ig m ml * (ig a al * (((ga1 al i c - ga0 al i c) * f c ml) *
          ((ga1 m a d - gbg m a d) * cg d j))) := by
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun al _ => ?_)
    have hprod : (∑ c, (ga1 al i c - ga0 al i c) * f c ml) *
        (∑ d, (ga1 m a d - gbg m a d) * cg d j) =
        ∑ c, ∑ d, ((ga1 al i c - ga0 al i c) * f c ml) *
          ((ga1 m a d - gbg m a d) * cg d j) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.mul_sum]
    rw [hprod, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
  have hR : (∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
      ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
        ((ga1 a b k - gbg a b k) * cg k j))))) =
      ∑ b, ∑ q, ∑ a, ∑ p, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j)))) := by
    rw [show (∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j))))) =
      ∑ a, ∑ b, ∑ p, ∑ q, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j)))) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [show (∑ a, ∑ p, ∑ q, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j))))) =
      ∑ a, ∑ q, ∑ p, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j)))) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
  rw [hL, hR]
  rw [show (∑ m, ∑ ml, ∑ a, ∑ al, ∑ c, ∑ d,
      ig m ml * (ig a al * (((ga1 al i c - ga0 al i c) * f c ml) *
        ((ga1 m a d - gbg m a d) * cg d j)))) =
    ∑ m, ∑ ml, ∑ a, ∑ al, ∑ c, ∑ d,
      ig a al * (ig m ml * ((ga1 i al c - ga0 i al c) * (f c ml *
        ((ga1 a m d - gbg a m d) * cg d j)))) from by
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun al _ => ?_))
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    rw [hga1s al i c, hga0s al i c, hga1s m a d, hgbgs m a d]
    ring]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedBackgroundHalfBlock_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedBackgroundHalfBlock_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedBackgroundHalfBlock_eq ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.mixedBackgroundHalfBlock_eq

end DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm
