import Submission.DifferentialGeometry.Geometry.Metric.CurveEnergy
import Mathlib.Analysis.Real.Sqrt

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry.Geometry.Riemannian

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem riemannianEDistOf_le_sum_curve_energy_sqrt
    (g : SmoothRiemannianMetric I M) (n : ℕ)
    (t : ℕ → ℝ) (β : ℕ → ℝ → M)
    (ht : ∀ k < n, t k ≤ t (k + 1))
    (hβ : ∀ k < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β k) (_root_.Set.Icc (t k) (t (k + 1))))
    (hnode : ∀ k, k + 1 < n → β k (t (k + 1)) = β (k + 1) (t (k + 1))) :
    riemannianEDistOf g (β 0 (t 0)) (β (n - 1) (t n)) ≤
      ENNReal.ofReal (∑ k ∈ Finset.range n,
        Real.sqrt (t (k + 1) - t k) * Real.sqrt (curveEnergy g (β k) (t k) (t (k + 1)))) := by
  induction n with
  | zero => simp only [Finset.sum_range_zero, riemannianEDistOf_self, ENNReal.ofReal_zero, le_refl]
  | succ n ih =>
    have hlast := edistOf_le_energy g (ht n (Nat.lt_succ_self n)) (hβ n (Nat.lt_succ_self n))
      (integrableOn_inner_mfderiv_self_of_contMDiffOn g (hβ n (Nat.lt_succ_self n)))
    by_cases hn0 : n = 0
    · subst n
      simpa only [Nat.zero_add, Nat.add_sub_cancel_right, Finset.sum_range_one] using hlast
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hprefix := ih (fun k hk => ht k (Nat.lt_succ_of_lt hk))
      (fun k hk => hβ k (Nat.lt_succ_of_lt hk)) (fun k hk => hnode k (Nat.lt_succ_of_lt hk))
    have hmatch := hnode (n - 1) (by omega)
    rw [Nat.sub_add_cancel hnpos] at hmatch
    rw [hmatch] at hprefix
    rw [Nat.add_sub_cancel_right, Finset.sum_range_succ]
    have hnonneg : 0 ≤ ∑ k ∈ Finset.range n,
        Real.sqrt (t (k + 1) - t k) * Real.sqrt (curveEnergy g (β k) (t k) (t (k + 1))) :=
      Finset.sum_nonneg (fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    rw [ENNReal.ofReal_add hnonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact (riemannianEDistOf_triangle g (β 0 (t 0)) (β n (t n)) (β n (t (n + 1)))).trans
      (add_le_add hprefix hlast)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_le_sum_curve_energy_sqrt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_le_sum_curve_energy_sqrt target :: scope.openDecls } }

theorem riemannianEDistOf_le_sqrt_sum_curveEnergy
    (g : SmoothRiemannianMetric I M) (n : ℕ)
    (t : ℕ → ℝ) (β : ℕ → ℝ → M)
    (ht : ∀ k < n, t k ≤ t (k + 1))
    (hβ : ∀ k < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β k) (_root_.Set.Icc (t k) (t (k + 1))))
    (hnode : ∀ k, k + 1 < n → β k (t (k + 1)) = β (k + 1) (t (k + 1))) :
    riemannianEDistOf g (β 0 (t 0)) (β (n - 1) (t n)) ≤
      ENNReal.ofReal (Real.sqrt (t n - t 0) *
        Real.sqrt (∑ k ∈ Finset.range n, curveEnergy g (β k) (t k) (t (k + 1)))) := by
  have hcauchy := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range n)
    (fun k => Real.sqrt (t (k + 1) - t k))
    (fun k => Real.sqrt (curveEnergy g (β k) (t k) (t (k + 1))))
  have hlength : (∑ k ∈ Finset.range n, Real.sqrt (t (k + 1) - t k) ^ 2) = t n - t 0 := by
    calc
      _ = ∑ k ∈ Finset.range n, (t (k + 1) - t k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact Real.sq_sqrt (sub_nonneg.mpr (ht k (Finset.mem_range.mp hk)))
      _ = _ := Finset.sum_range_sub t n
  have henergy : (∑ k ∈ Finset.range n, Real.sqrt (curveEnergy g (β k) (t k) (t (k + 1))) ^ 2) =
      ∑ k ∈ Finset.range n, curveEnergy g (β k) (t k) (t (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact Real.sq_sqrt (curveEnergy_nonneg g (ht k (Finset.mem_range.mp hk)))
  rw [hlength, henergy] at hcauchy
  exact (riemannianEDistOf_le_sum_curve_energy_sqrt g n t β ht hβ hnode).trans
    (ENNReal.ofReal_le_ofReal hcauchy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_le_sqrt_sum_curveEnergy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_le_sqrt_sum_curveEnergy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_le_sqrt_sum_curveEnergy ``Submission.DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_le_sqrt_sum_curveEnergy

theorem riemannianEDistOf_ne_top_of_curve_chain
    (g : SmoothRiemannianMetric I M) (n : ℕ)
    (t : ℕ → ℝ) (β : ℕ → ℝ → M)
    (ht : ∀ k < n, t k ≤ t (k + 1))
    (hβ : ∀ k < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β k) (_root_.Set.Icc (t k) (t (k + 1))))
    (hnode : ∀ k, k + 1 < n → β k (t (k + 1)) = β (k + 1) (t (k + 1))) :
    riemannianEDistOf g (β 0 (t 0)) (β (n - 1) (t n)) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (riemannianEDistOf_le_sqrt_sum_curveEnergy g n t β ht hβ hnode)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_ne_top_of_curve_chain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_ne_top_of_curve_chain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_ne_top_of_curve_chain ``Submission.DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_ne_top_of_curve_chain

theorem riemannianEDistOf_toReal_sq_le_sum_curveEnergy
    (g : SmoothRiemannianMetric I M) (n : ℕ)
    (t : ℕ → ℝ) (β : ℕ → ℝ → M)
    (ht : ∀ k < n, t k ≤ t (k + 1))
    (hβ : ∀ k < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β k) (_root_.Set.Icc (t k) (t (k + 1))))
    (hnode : ∀ k, k + 1 < n → β k (t (k + 1)) = β (k + 1) (t (k + 1))) :
    (riemannianEDistOf g (β 0 (t 0)) (β (n - 1) (t n))).toReal ^ 2 ≤
      (t n - t 0) * ∑ k ∈ Finset.range n, curveEnergy g (β k) (t k) (t (k + 1)) := by
  have hdist := riemannianEDistOf_le_sqrt_sum_curveEnergy g n t β ht hβ hnode
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at hreal
  have hsum : 0 ≤ ∑ k ∈ Finset.range n, curveEnergy g (β k) (t k) (t (k + 1)) :=
    Finset.sum_nonneg (fun k hk => curveEnergy_nonneg g (ht k (Finset.mem_range.mp hk)))
  have htime : 0 ≤ t n - t 0 := by
    rw [← Finset.sum_range_sub t n]
    exact Finset.sum_nonneg (fun k hk => sub_nonneg.mpr (ht k (Finset.mem_range.mp hk)))
  have hsquare := (sq_le_sq₀ ENNReal.toReal_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hreal
  simpa only [mul_pow, Real.sq_sqrt htime, Real.sq_sqrt hsum] using hsquare

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_toReal_sq_le_sum_curveEnergy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_toReal_sq_le_sum_curveEnergy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_toReal_sq_le_sum_curveEnergy ``Submission.DifferentialGeometry.Geometry.Riemannian.riemannianEDistOf_toReal_sq_le_sum_curveEnergy

end DifferentialGeometry.Geometry.Riemannian
