import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.Descent
import Submission.DifferentialGeometry.Topology.Manifold.IntervalExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace AddCircle
open _root_.AddCircle

open _root_.AddCircle in
theorem exists_contMDiff_extension_of_periodic
    {a b : ℝ} {β : ℝ → ℝ → ℝ}
    (hβ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => β p.1 p.2)
      (_root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set ℝ)))
    (hper : ∀ t ∈ _root_.Set.Icc a b, Function.Periodic (β t) 1) :
    ∃ γ : ℝ × AddCircle (1 : ℝ) → ℝ,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ γ ∧
        ∀ t ∈ _root_.Set.Icc a b, ∀ x : ℝ, γ (t, (x : AddCircle (1 : ℝ))) = β t x := by
  classical
  let β₀ : ℝ → ℝ → ℝ := fun t x => if t ∈ _root_.Set.Icc a b then β t x else 0
  have hp₀ : ∀ t, Function.Periodic (β₀ t) 1 := by
    intro t x
    dsimp only [β₀]
    by_cases ht : t ∈ _root_.Set.Icc a b
    · simp only [if_pos ht]
      exact hper t ht x
    · simp only [if_neg ht]
  let f : ℝ × AddCircle (1 : ℝ) → ℝ := fun p => (hp₀ p.1).lift p.2
  have hcoe (t x : ℝ) : f (t, (x : AddCircle (1 : ℝ))) = β₀ t x := rfl
  have hf : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f
      (_root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set (AddCircle (1 : ℝ)))) := by
    apply contMDiffOn_of_comp_coe
    have heq : _root_.Set.EqOn (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle (1 : ℝ))))
        (fun p => β p.1 p.2) (_root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set ℝ)) := by
      intro p hp
      change f (p.1, (p.2 : AddCircle (1 : ℝ))) = β p.1 p.2
      rw [hcoe]
      exact if_pos hp.1
    have hh : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle (1 : ℝ))))
        (_root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set ℝ)) := hβ.congr heq
    rw [← contMDiffOn_iff_contDiffOn, ← chartedSpaceSelf_prod,
      modelWithCornersSelf_prod] at hh
    exact hh
  obtain ⟨γ, hγ, hγf⟩ := Manifold.exists_contMDiff_extension_Icc hf
  refine ⟨γ, hγ, ?_⟩
  intro t ht x
  rw [hγf ⟨ht, _root_.Set.mem_univ _⟩, hcoe]
  exact if_pos ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_contMDiff_extension_of_periodic then
    throwError "Refusing to shadow existing declaration AddCircle.exists_contMDiff_extension_of_periodic"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_contMDiff_extension_of_periodic ``Submission.AddCircle.exists_contMDiff_extension_of_periodic

end AddCircle
