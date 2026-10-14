import Submission.DifferentialGeometry.Analysis.Calculus.TimeJet.Commutation
import Submission.DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import Mathlib.Data.Fin.Tuple.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Analysis

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace (ℝ × E)] [OpensMeasurableSpace (ℝ × E)]

theorem exists_spatial_derivative_tree_of_contDiffOn
    {I : Set ℝ} {Ω : Set E} (hI : UniqueDiffOn ℝ I) (hΩ : IsOpen Ω)
    {f : ℝ × E → F} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (I ×ˢ Ω))
    {K : Set (ℝ × E)} (hK : IsCompact K) (hKI : K ⊆ I ×ˢ Ω)
    (μ : _root_.MeasureTheory.Measure (ℝ × E)) (v : ι → E) :
    ∃ A : ∀ n : ℕ, (Fin n → ι) → ℝ × E → F,
      A 0 (fun i => Fin.elim0 i) = f ∧
      (∀ n α, ContDiffOn ℝ (⊤ : ℕ∞) (A n α) (I ×ˢ Ω)) ∧
      (∀ n α, _root_.MeasureTheory.MemLp (A n α) ∞ (μ.restrict K)) ∧
      ∀ n α i, A (n + 1) (Fin.cons i α) =
        fun p => fderiv ℝ (fun x => A n α (p.1, x)) p.2 (v i) := by
  let A : ∀ n : ℕ, (Fin n → ι) → ℝ × E → F := fun n =>
    Nat.rec (motive := fun n => (Fin n → ι) → ℝ × E → F) (fun _ => f)
      (fun _ B α p => fderiv ℝ (fun x => B (Fin.tail α) (p.1, x)) p.2 (v (α 0))) n
  have hA : ∀ n α, ContDiffOn ℝ (⊤ : ℕ∞) (A n α) (I ×ˢ Ω) := by
    intro n
    induction n with
    | zero => intro α; simpa only [A, Nat.rec_zero] using hf
    | succ n ih =>
        intro α
        simpa only [A, Nat.rec_add_one, Function.uncurry] using
          (spatialFDeriv_contDiffOn (G := fun t x => A n (Fin.tail α) (t, x))
          hI hΩ (ih (Fin.tail α))).clm_apply (contDiffOn_const (c := v (α 0)))
  refine ⟨A, ?_, hA, ?_, ?_⟩
  · simp only [A, Nat.rec_zero]
  · intro n α
    exact ((hA n α).continuousOn.mono hKI).memLp_top_of_isCompact hK hK.measurableSet
  · intro n α i
    simp only [A, Fin.tail_cons, Fin.cons_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_spatial_derivative_tree_of_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_spatial_derivative_tree_of_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_spatial_derivative_tree_of_contDiffOn ``Submission.DifferentialGeometry.Analysis.exists_spatial_derivative_tree_of_contDiffOn

end DifferentialGeometry.Analysis
