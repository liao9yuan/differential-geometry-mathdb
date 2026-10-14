import Submission.DifferentialGeometry.Topology.Homology.Subdivision.AffineSimplex
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem affineCone_boundary_generator {n : ℕ} (p : E) (v : Fin (n + 2) → E) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (Fin.cons p v)) ≫
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 2) (n + 1) =
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (affineSingularSimplex v) -
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
          (affineSingularSimplex (Fin.cons p (v ∘ i.succAbove))) := by
  rw [SSet.ιChainComplex_d, Fin.sum_univ_succ]
  simp only [δ_affineSingularSimplex, Fin.val_zero, pow_zero, one_zsmul,
    Fin.succAbove_zero, Fin.cons_comp_succ, Fin.cons_comp_succ_succAbove,
    Fin.val_succ, pow_succ, mul_neg_one, neg_zsmul, Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineCone_boundary_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineCone_boundary_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineCone_boundary_generator ``Submission.DifferentialGeometry.Homology.affineCone_boundary_generator


theorem affineCone_boundary_generator_zero (p q : E) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (Fin.cons p (fun _ : Fin 1 ↦ q))) ≫
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d 1 0 =
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (fun _ : Fin 1 ↦ q)) -
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (fun _ : Fin 1 ↦ p)) := by
  rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
  simp only [δ_affineSingularSimplex]
  have h₀ : Fin.cons p (fun _ : Fin 1 ↦ q) ∘ (0 : Fin 2).succAbove =
      (fun _ : Fin 1 ↦ q) := rfl
  have h₁ : Fin.cons p (fun _ : Fin 1 ↦ q) ∘ (1 : Fin 2).succAbove =
      (fun _ : Fin 1 ↦ p) := by
    funext i
    fin_cases i
    rfl
  rw [h₀, h₁]
  simp [sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineCone_boundary_generator_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineCone_boundary_generator_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineCone_boundary_generator_zero ``Submission.DifferentialGeometry.Homology.affineCone_boundary_generator_zero

def affineCone (p : E) (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X n ⟶
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X (n + 1) :=
  Sigma.desc (fun σ ↦ (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
    (affineSingularSimplex (Fin.cons p (singularSimplexVertices σ))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineCone ``Submission.DifferentialGeometry.Homology.affineCone


@[reassoc (attr := simp)]
theorem ι_affineCone (p : E) {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ affineCone R p n =
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (Fin.cons p (singularSimplexVertices σ))) :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_affineCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_affineCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_affineCone ``Submission.DifferentialGeometry.Homology.ι_affineCone

theorem affineCone_boundary (p : E) (n : ℕ) :
    affineCone R p (n + 1) ≫
        ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 2) (n + 1) +
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n ≫ affineCone R p n =
        (SSet.chainComplexMap (affineStraightening (E := E)) R).f (n + 1) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [Preadditive.comp_add, ← Category.assoc, ι_affineCone,
    affineCone_boundary_generator, ← Category.assoc, SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, ι_affineCone,
    SSet.ι_chainComplexMap_f, singularSimplexVertices_δ]
  apply sub_add_cancel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineCone_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineCone_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineCone_boundary ``Submission.DifferentialGeometry.Homology.affineCone_boundary


def singularChainAugmentation :
    ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X 0 ⟶ R :=
  Sigma.desc (fun _ : TopCat.toSSet.obj (TopCat.of E) _⦋0⦌ ↦ 𝟙 R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularChainAugmentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularChainAugmentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularChainAugmentation ``Submission.DifferentialGeometry.Homology.singularChainAugmentation

omit [NormedSpace ℝ E] in
@[reassoc (attr := simp)]
theorem ι_singularChainAugmentation (σ : TopCat.toSSet.obj (TopCat.of E) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫
      singularChainAugmentation (E := E) R = 𝟙 R :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_singularChainAugmentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_singularChainAugmentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_singularChainAugmentation ``Submission.DifferentialGeometry.Homology.ι_singularChainAugmentation

omit [NormedSpace ℝ E] in
theorem d_singularChainAugmentation :
    ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d 1 0 ≫
      singularChainAugmentation (E := E) R = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_d, Fin.sum_univ_two]
  simp only [Preadditive.add_comp, Preadditive.neg_comp,
    ι_singularChainAugmentation, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_zsmul, neg_one_zsmul, add_neg_cancel, _root_.CategoryTheory.Limits.comp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.d_singularChainAugmentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.d_singularChainAugmentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.d_singularChainAugmentation ``Submission.DifferentialGeometry.Homology.d_singularChainAugmentation


theorem affineCone_boundary_zero (p : E) :
    affineCone R p 0 ≫ ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d 1 0 =
      𝟙 _ - singularChainAugmentation (E := E) R ≫
          (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
            (affineSingularSimplex (fun _ : Fin 1 ↦ p)) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_affineCone, Preadditive.comp_sub, Category.comp_id]
  have hσ : singularSimplexVertices σ = (fun _ : Fin 1 ↦ singularSimplexVertices σ 0) := by
    funext i
    fin_cases i
    rfl
  rw [hσ, affineCone_boundary_generator_zero]
  have hpoint : affineSingularSimplex (fun _ : Fin 1 ↦ singularSimplexVertices σ 0) = σ := by
    rw [← hσ]
    exact affineSingularSimplex_vertices_zero σ
  rw [hpoint]
  rw [← Category.assoc, ι_singularChainAugmentation, Category.id_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineCone_boundary_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineCone_boundary_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineCone_boundary_zero ``Submission.DifferentialGeometry.Homology.affineCone_boundary_zero


theorem affineStraightening_f_zero :
    (SSet.chainComplexMap (affineStraightening (E := E)) R).f 0 = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [SSet.ι_chainComplexMap_f, Category.comp_id]
  change (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
      (affineSingularSimplex (singularSimplexVertices σ)) = _
  rw [affineSingularSimplex_vertices_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineStraightening_f_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineStraightening_f_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineStraightening_f_zero ``Submission.DifferentialGeometry.Homology.affineStraightening_f_zero


theorem affineCone_straightening (p : E) (n : ℕ) :
    affineCone R p n ≫ (SSet.chainComplexMap (affineStraightening (E := E)) R).f (n + 1) =
      affineCone R p n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_affineCone, SSet.ι_chainComplexMap_f,
    affineStraightening_affineSingularSimplex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineCone_straightening then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineCone_straightening"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineCone_straightening ``Submission.DifferentialGeometry.Homology.affineCone_straightening


theorem straightening_affineCone (p : E) (n : ℕ) :
    (SSet.chainComplexMap (affineStraightening (E := E)) R).f n ≫ affineCone R p n =
      affineCone R p n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, ι_affineCone, ι_affineCone]
  change (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
      (affineSingularSimplex (Fin.cons p
        (singularSimplexVertices (affineSingularSimplex (singularSimplexVertices σ))))) = _
  rw [singularSimplexVertices_affineSingularSimplex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.straightening_affineCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.straightening_affineCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.straightening_affineCone ``Submission.DifferentialGeometry.Homology.straightening_affineCone

end DifferentialGeometry.Homology
