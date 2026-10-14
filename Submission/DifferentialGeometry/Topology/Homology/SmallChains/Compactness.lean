import Submission.DifferentialGeometry.Topology.Homology.SmallChains
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.Opposite _root_.Simplicial

universe u v

namespace DifferentialGeometry.Homology

variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)
  (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)

include hopen hcover

theorem exists_small_precomp_radius {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (m : ℕ)
      (τ : C(stdSimplex ℝ (Fin (m + 1)), stdSimplex ℝ (Fin (n + 1)))),
      (∀ a b, _root_.Dist.dist (τ a) (τ b) < δ) →
        ((X.toSSetObjEquiv (_root_.Opposite.op ⦋m⦌)).symm
          ((X.toSSetObjEquiv (_root_.Opposite.op ⦋n⦌) σ).comp τ)) ∈
            (smallSingularSimplices X U).obj (_root_.Opposite.op ⦋m⦌) := by
  let f : C(stdSimplex ℝ (Fin (n + 1)), X) := X.toSSetObjEquiv (_root_.Opposite.op ⦋n⦌) σ
  have hUopen : ∀ i, IsOpen (f ⁻¹' U i) := fun i ↦ (hopen i).preimage f.continuous
  have hUcover : Set.univ ⊆ ⋃ i, f ⁻¹' U i := by
    intro x _
    exact Set.mem_iUnion.mpr (hcover (f x))
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_univ : IsCompact (Set.univ : Set (stdSimplex ℝ (Fin (n + 1)))))
    hUopen hUcover
  refine ⟨δ, hδ, ?_⟩
  intro m τ hτ
  let a : stdSimplex ℝ (Fin (m + 1)) :=
    ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩
  obtain ⟨i, hi⟩ := hball (τ a) (Set.mem_univ _)
  refine ⟨i, ?_⟩
  rintro _ ⟨b, rfl⟩
  exact hi (hτ b a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.exists_small_precomp_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.exists_small_precomp_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.exists_small_precomp_radius ``Submission.DifferentialGeometry.Homology.exists_small_precomp_radius

theorem exists_uniform_small_precomp_radius {n : ℕ}
    (F : Finset (TopCat.toSSet.obj X _⦋n⦌)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ F, ∀ (m : ℕ)
      (τ : C(stdSimplex ℝ (Fin (m + 1)), stdSimplex ℝ (Fin (n + 1)))),
      (∀ a b, _root_.Dist.dist (τ a) (τ b) < δ) →
        ((X.toSSetObjEquiv (_root_.Opposite.op ⦋m⦌)).symm
          ((X.toSSetObjEquiv (_root_.Opposite.op ⦋n⦌) σ).comp τ)) ∈
            (smallSingularSimplices X U).obj (_root_.Opposite.op ⦋m⦌) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert σ F hσ hF =>
    obtain ⟨δ, hδ, hδF⟩ := hF
    obtain ⟨ε, hε, hεσ⟩ := exists_small_precomp_radius X U hopen hcover σ
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro ρ hρ m τ hτ
    obtain rfl | hρ := Finset.mem_insert.mp hρ
    · exact hεσ m τ (fun a b ↦ (hτ a b).trans_le (min_le_right _ _))
    · exact hδF ρ hρ m τ (fun a b ↦ (hτ a b).trans_le (min_le_left _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.exists_uniform_small_precomp_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.exists_uniform_small_precomp_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.exists_uniform_small_precomp_radius ``Submission.DifferentialGeometry.Homology.exists_uniform_small_precomp_radius

end DifferentialGeometry.Homology
