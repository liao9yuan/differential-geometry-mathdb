import Mathlib.Analysis.SpecificLimits.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open scoped _root_.Topology

namespace Filter
open _root_.Filter

open _root_.Filter in
theorem exists_eventually_of_monotone_of_subsequence
    (P : ℕ → ℕ → Prop) (hmono : ∀ i, Monotone (P i))
    (hsub : ∀ f : ℕ → ℕ, StrictMono f → ∃ m, ∃ᶠ i in _root_.Filter.atTop, P (f i) m) :
    ∃ m, ∀ᶠ i in _root_.Filter.atTop, P i m := by
  by_contra hnot
  have hbad (m : ℕ) : ∃ᶠ i in _root_.Filter.atTop, ¬ P i m :=
    _root_.Filter.not_eventually.mp fun h => hnot ⟨m, h⟩
  obtain ⟨f, hf, hfail⟩ := _root_.Filter.extraction_forall_of_frequently hbad
  obtain ⟨m, hm⟩ := hsub f hf
  obtain ⟨i, hPi, hmi⟩ := (hm.and_eventually (_root_.Filter.eventually_ge_atTop m)).exists
  exact hfail i (hmono (f i) hmi hPi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Filter.exists_eventually_of_monotone_of_subsequence then
    throwError "Refusing to shadow existing declaration Filter.exists_eventually_of_monotone_of_subsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `Filter.exists_eventually_of_monotone_of_subsequence ``Submission.Filter.exists_eventually_of_monotone_of_subsequence

open _root_.Filter in
theorem exists_pos_eventually_of_antitone_of_subsequence
    (P : ℕ → ℝ → Prop)
    (hmono : ∀ i ε δ, 0 < ε → ε ≤ δ → P i δ → P i ε)
    (hsub : ∀ f : ℕ → ℕ, StrictMono f →
      ∃ δ : ℝ, 0 < δ ∧ ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ i, P (f (g i)) δ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in _root_.Filter.atTop, P i δ := by
  let width : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hpos (n : ℕ) : 0 < width n := by dsimp [width]; positivity
  have hwidth : Antitone width := by
    intro m n hmn
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hlimit : _root_.Filter.Tendsto width _root_.Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨m, hm⟩ := exists_eventually_of_monotone_of_subsequence
    (fun i n => P i (width n)) (fun i m n hmn => hmono i _ _ (hpos n) (hwidth hmn)) (by
      intro f hf
      obtain ⟨δ, hδ, g, hg, hgood⟩ := hsub f hf
      obtain ⟨m, hm⟩ := (hlimit.eventually (Iio_mem_nhds hδ)).exists
      refine ⟨m, _root_.Filter.frequently_atTop.2 fun N => ⟨g N, hg.id_le N, ?_⟩⟩
      exact hmono (f (g N)) _ _ (hpos m) hm.le (hgood N))
  exact ⟨width m, hpos m, hm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Filter.exists_pos_eventually_of_antitone_of_subsequence then
    throwError "Refusing to shadow existing declaration Filter.exists_pos_eventually_of_antitone_of_subsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `Filter.exists_pos_eventually_of_antitone_of_subsequence ``Submission.Filter.exists_pos_eventually_of_antitone_of_subsequence

end Filter
