import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open scoped _root_.BigOperators

namespace DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm


lemma inverse_metric_contraction {n : ℕ} (ig cg : Fin n → Fin n → ℝ)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (X : Fin n → ℝ) (e : Fin n) :
    (∑ u, ∑ d, cg d e * ig d u * X u) = X e := by
  have h1 : ∀ u : Fin n, (∑ d, cg d e * ig d u * X u) =
      (if u = e then (1 : ℝ) else 0) * X u := by
    intro u
    rw [← Finset.sum_mul, hcol u e]
  rw [Finset.sum_congr rfl (fun u _ => h1 u)]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl, one_mul]
  · intro b _ hb
    rw [if_neg hb, _root_.MulZeroClass.zero_mul]
  · intro h
    exact absurd (Finset.mem_univ e) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.inverse_metric_contraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.inverse_metric_contraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.inverse_metric_contraction ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.inverse_metric_contraction


lemma inverse_metric_contraction_rev {n : ℕ} (ig cg : Fin n → Fin n → ℝ)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (X : Fin n → ℝ) (e : Fin n) :
    (∑ w, ∑ d, cg d w * ig d e * X w) = X e := by
  have h1 : ∀ w : Fin n, (∑ d, cg d w * ig d e * X w) =
      (if e = w then (1 : ℝ) else 0) * X w := by
    intro w
    rw [← Finset.sum_mul, hcol e w]
  rw [Finset.sum_congr rfl (fun w _ => h1 w)]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl, one_mul]
  · intro b _ hb
    rw [if_neg (fun h => hb h.symm), _root_.MulZeroClass.zero_mul]
  · intro h
    exact absurd (Finset.mem_univ e) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.inverse_metric_contraction_rev then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.inverse_metric_contraction_rev"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.inverse_metric_contraction_rev ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.inverse_metric_contraction_rev


def r3B {n : ℕ} (f : Fin n → Fin n → ℝ)
    (ga0 : Fin n → Fin n → Fin n → ℝ)
    (a b c : Fin n) : ℝ :=
  -(∑ r, ga0 a b r * f r c) + (-(∑ r, ga0 a c r * f b r))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.r3B then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.r3B"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.r3B ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.r3B


def christoffelCorrection {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (gb : Fin n → Fin n → Fin n → ℝ)
    (a b k : Fin n) : ℝ :=
  (1 / 2 : ℝ) * (∑ l, (-(∑ q, ∑ p, ig k p * f p q * ig q l)) * gb a b l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.christoffelCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.christoffelCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.christoffelCorrection ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.christoffelCorrection


def deTurckVectorCorrection {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (ga1 gbg gb : Fin n → Fin n → Fin n → ℝ)
    (k : Fin n) : ℝ :=
  ∑ a, ∑ b, ((-(∑ q, ∑ p, ig a p * f p q * ig q b)) * (ga1 a b k - gbg a b k) +
    ig a b * christoffelCorrection ig f gb a b k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorCorrection ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorCorrection


def deTurckVectorFieldDerivative {n : ℕ} (ig : Fin n → Fin n → ℝ)
    (dig ga1 gbg : Fin n → Fin n → Fin n → ℝ)
    (dga1 dgbg : Fin n → Fin n → Fin n → Fin n → ℝ)
    (m k : Fin n) : ℝ :=
  ∑ a, ∑ b, (dig m a b * (ga1 a b k - gbg a b k) +
    ig a b * (dga1 m a b k - dgbg m a b k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDerivative ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDerivative


def zeroOrderDerivativeCorrection {n : ℕ} (ig f : Fin n → Fin n → ℝ)
    (dig ga1 gbg gb : Fin n → Fin n → Fin n → ℝ)
    (dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (m k : Fin n) : ℝ :=
  ∑ a, ∑ b, ((-(∑ q, ∑ p, (dig m a p * f p q * ig q b + ig a p * f p q * dig m q b))) *
    (ga1 a b k - gbg a b k) + (-(∑ q, ∑ p, ig a p * f p q * ig q b)) * (dga1 m a b k - dgbg m a b k)
    + dig m a b * christoffelCorrection ig f gb a b k + ig a b *
    ((1 / 2 : ℝ) * (∑ l, ((-(∑ q, ∑ p, (dig m k p * f p q * ig q l + ig k p * f p q * dig m q l))) *
    gb a b l + (-(∑ q, ∑ p, ig k p * f p q * ig q l)) * dgb m a b l))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderDerivativeCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderDerivativeCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderDerivativeCorrection ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderDerivativeCorrection


def zeroOrderCorrection {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga1 gbg gb : Fin n → Fin n → Fin n → ℝ)
    (dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  (∑ k, deTurckVectorCorrection ig f ga1 gbg gb k * dg k i j) +
    (∑ k, f k j * deTurckVectorFieldDerivative ig dig ga1 gbg dga1 dgbg i k) +
    (∑ k, f i k * deTurckVectorFieldDerivative ig dig ga1 gbg dga1 dgbg j k) +
    (∑ k, cg k j * zeroOrderDerivativeCorrection ig f dig ga1 gbg gb dga1 dgbg dgb i k) +
    (∑ k, cg i k * zeroOrderDerivativeCorrection ig f dig ga1 gbg gb dga1 dgbg dgb j k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderCorrection ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderCorrection


def deTurckVectorFieldDifference {n : ℕ} (ig : Fin n → Fin n → ℝ)
    (ga1 gbg : Fin n → Fin n → Fin n → ℝ)
    (k : Fin n) : ℝ :=
  ∑ a, ∑ b, ig a b * (ga1 a b k - gbg a b k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDifference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDifference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDifference ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.deTurckVectorFieldDifference


def covariantDerivativeConnectionDifference {n : ℕ}
    (ga1 gbg : Fin n → Fin n → Fin n → ℝ)
    (dga1 dgbg : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a m k p : Fin n) : ℝ :=
  dga1 a k m p - dgbg a k m p +
    (∑ c, ga1 a c p * (ga1 k m c - gbg k m c)) -
    (∑ c, ga1 a m c * (ga1 k c p - gbg k c p)) -
    (∑ c, ga1 a k c * (ga1 c m p - gbg c m p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.covariantDerivativeConnectionDifference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.covariantDerivativeConnectionDifference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.covariantDerivativeConnectionDifference ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.covariantDerivativeConnectionDifference


def covariantDerivativeDeTurckVectorDifference {n : ℕ} (ig : Fin n → Fin n → ℝ)
    (dig ga1 gbg : Fin n → Fin n → Fin n → ℝ)
    (dga1 dgbg : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a p : Fin n) : ℝ :=
  deTurckVectorFieldDerivative ig dig ga1 gbg dga1 dgbg a p +
    ∑ c, ga1 a c p * deTurckVectorFieldDifference ig ga1 gbg c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.covariantDerivativeDeTurckVectorDifference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.covariantDerivativeDeTurckVectorDifference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.covariantDerivativeDeTurckVectorDifference ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.covariantDerivativeDeTurckVectorDifference


def zeroOrderVectorCorrection {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dig ga1 gbg : Fin n → Fin n → Fin n → ℝ)
    (dga1 dgbg : Fin n → Fin n → Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  -(∑ m, ∑ ml, ig m ml * (∑ k, ∑ kl, ig k kl *
      (((∑ p, covariantDerivativeConnectionDifference ga1 gbg dga1 dgbg i m k p * cg p j) +
        (∑ p, covariantDerivativeConnectionDifference ga1 gbg dga1 dgbg j m k p * cg p i)) *
        f ml kl))) +
    ((∑ p, covariantDerivativeDeTurckVectorDifference ig dig ga1 gbg dga1 dgbg i p * f p j) +
      (∑ p, covariantDerivativeDeTurckVectorDifference ig dig ga1 gbg dga1 dgbg j p * f i p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderVectorCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderVectorCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderVectorCorrection ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.zeroOrderVectorCorrection


def firstDerivativeRemainder {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (ga0 ga1 gbg : Fin n → Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  (∑ w, deTurckVectorFieldDifference ig ga1 gbg w *
      r3B f ga0 w i j) +
  ((∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B f ga0 i m p *
        (∑ q, (ga1 l1 j q - ga0 l1 j q) * cg q k1)))) -
    (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B f ga0 i m p *
        (∑ q, (ga1 k1 l1 q - gbg k1 l1 q) * cg q j)))) -
    (∑ w, (∑ a, ∑ b, ig a b * (ga1 a b w - ga0 a b w)) *
      r3B f ga0 i j w) -
    (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B f ga0 m j p *
        (∑ q, (ga1 k1 i q - ga0 k1 i q) * cg q l1)))) -
    (∑ k1, ∑ p, ig k1 p * (∑ q, (ga1 j i q - ga0 j i q) *
      r3B f ga0 p q k1)) -
    (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B f ga0 m j p *
        (∑ q, (ga1 l1 i q - ga0 l1 i q) * cg q k1))))) +
  ((∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B f ga0 j m p *
        (∑ q, (ga1 l1 i q - ga0 l1 i q) * cg q k1)))) -
    (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B f ga0 j m p *
        (∑ q, (ga1 k1 l1 q - gbg k1 l1 q) * cg q i)))) -
    (∑ w, (∑ a, ∑ b, ig a b * (ga1 a b w - ga0 a b w)) *
      r3B f ga0 j i w) -
    (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B f ga0 m i p *
        (∑ q, (ga1 k1 j q - ga0 k1 j q) * cg q l1)))) -
    (∑ k1, ∑ p, ig k1 p * (∑ q, (ga1 i j q - ga0 i j q) *
      r3B f ga0 p q k1)) -
    (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m *
      (r3B f ga0 m i p *
        (∑ q, (ga1 l1 j q - ga0 l1 j q) * cg q k1))))) +
  (∑ k1, ∑ p, ig k1 p * (∑ q, (ga1 j i q - ga0 j i q) *
    r3B f ga0 q p k1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.firstDerivativeRemainder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.firstDerivativeRemainder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.firstDerivativeRemainder ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm.firstDerivativeRemainder

end DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.LieCorrectionZeroNormalForm
