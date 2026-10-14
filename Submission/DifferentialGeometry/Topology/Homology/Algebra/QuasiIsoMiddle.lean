import Mathlib.Algebra.Homology.HomologySequenceLemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.ComposableArrows _root_.CategoryTheory.Abelian
open _root_.HomologicalComplex _root_.HomologicalComplex.HomologySequence
noncomputable section
namespace DifferentialGeometry.HomologicalComplex
variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (_root_.HomologicalComplex C c)}
  (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

include hS₁ hS₂

theorem mono_homologyMap_middle (i : ι)
    (h₁ : _root_.CategoryTheory.Mono (_root_.HomologicalComplex.homologyMap φ.τ₁ i)) (h₃ : _root_.CategoryTheory.Mono (_root_.HomologicalComplex.homologyMap φ.τ₃ i))
    (hprev : ∀ j, c.Rel j i → _root_.CategoryTheory.Epi (_root_.HomologicalComplex.homologyMap φ.τ₃ j)) :
    Mono (_root_.HomologicalComplex.homologyMap φ.τ₂ i) := by
  by_cases hi : ∃ j, c.Rel j i
  · obtain ⟨j, hji⟩ := hi
    apply _root_.CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono
      ((_root_.CategoryTheory.ComposableArrows.δ₀Functor ⋙ _root_.CategoryTheory.ComposableArrows.δ₀Functor).map (_root_.HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ j i hji))
    · exact (_root_.HomologicalComplex.HomologySequence.composableArrows₅_exact hS₁ j i hji).δ₀.δ₀
    · exact (_root_.HomologicalComplex.HomologySequence.composableArrows₅_exact hS₂ j i hji).δ₀.δ₀
    · exact hprev j hji
    · exact h₁
    · exact h₃
  · apply _root_.CategoryTheory.Abelian.mono_of_mono_of_mono_of_mono (_root_.HomologicalComplex.HomologySequence.mapComposableArrows₂ φ i)
      (_root_.HomologicalComplex.HomologySequence.composableArrows₂_exact hS₁ i) _ h₁ h₃
    have := hS₂.mono_f
    apply _root_.HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
    simpa using hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.mono_homologyMap_middle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.mono_homologyMap_middle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.mono_homologyMap_middle ``Submission.DifferentialGeometry.HomologicalComplex.mono_homologyMap_middle

theorem epi_homologyMap_middle (i : ι)
    (h₁ : _root_.CategoryTheory.Epi (_root_.HomologicalComplex.homologyMap φ.τ₁ i)) (h₃ : _root_.CategoryTheory.Epi (_root_.HomologicalComplex.homologyMap φ.τ₃ i))
    (hnext : ∀ j, c.Rel i j → _root_.CategoryTheory.Mono (_root_.HomologicalComplex.homologyMap φ.τ₁ j)) :
    Epi (_root_.HomologicalComplex.homologyMap φ.τ₂ i) := by
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    apply _root_.CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono
      ((_root_.CategoryTheory.ComposableArrows.δlastFunctor ⋙ _root_.CategoryTheory.ComposableArrows.δlastFunctor).map (_root_.HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (_root_.HomologicalComplex.HomologySequence.composableArrows₅_exact hS₁ i j hij).δlast.δlast
    · exact (_root_.HomologicalComplex.HomologySequence.composableArrows₅_exact hS₂ i j hij).δlast.δlast
    · exact h₁
    · exact h₃
    · exact hnext j hij
  · apply _root_.CategoryTheory.Abelian.epi_of_epi_of_epi_of_epi (_root_.HomologicalComplex.HomologySequence.mapComposableArrows₂ φ i)
      (_root_.HomologicalComplex.HomologySequence.composableArrows₂_exact hS₂ i) _ h₁ h₃
    have := hS₁.epi_g
    apply _root_.HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
    simpa using hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.epi_homologyMap_middle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.epi_homologyMap_middle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.epi_homologyMap_middle ``Submission.DifferentialGeometry.HomologicalComplex.epi_homologyMap_middle

theorem isIso_homologyMap_middle (i : ι)
    (h₁ : _root_.CategoryTheory.IsIso (_root_.HomologicalComplex.homologyMap φ.τ₁ i)) (h₃ : _root_.CategoryTheory.IsIso (_root_.HomologicalComplex.homologyMap φ.τ₃ i))
    (hprev : ∀ j, c.Rel j i → _root_.CategoryTheory.Epi (_root_.HomologicalComplex.homologyMap φ.τ₃ j))
    (hnext : ∀ j, c.Rel i j → _root_.CategoryTheory.Mono (_root_.HomologicalComplex.homologyMap φ.τ₁ j)) :
    IsIso (_root_.HomologicalComplex.homologyMap φ.τ₂ i) := by
  have := mono_homologyMap_middle φ hS₁ hS₂ i inferInstance inferInstance hprev
  have := epi_homologyMap_middle φ hS₁ hS₂ i inferInstance inferInstance hnext
  exact _root_.CategoryTheory.isIso_of_mono_of_epi _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.isIso_homologyMap_middle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.isIso_homologyMap_middle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.isIso_homologyMap_middle ``Submission.DifferentialGeometry.HomologicalComplex.isIso_homologyMap_middle

theorem quasiIso_middle (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_homologyMap_middle φ hS₁ hS₂ i
  all_goals infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.quasiIso_middle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.quasiIso_middle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.quasiIso_middle ``Submission.DifferentialGeometry.HomologicalComplex.quasiIso_middle

end DifferentialGeometry.HomologicalComplex
