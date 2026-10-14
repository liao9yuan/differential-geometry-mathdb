import Submission.DifferentialGeometry.Topology.Homology.Local.LocalHomology
import Submission.DifferentialGeometry.Topology.Homology.Support

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

def localGood (X : TopCat.{u}) (n : ℕ) (A : Set X) : Prop :=
  (∀ i, n < i → _root_.CategoryTheory.Limits.IsZero (relativeHomology R X Aᶜ i)) ∧
    ∀ α : relativeHomology R X Aᶜ n, (∀ x (hx : x ∈ A), relativeHomologyMap R (𝟙 X) (compl_mapsTo hx) n α = 0) → α = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood ``Submission.DifferentialGeometry.Topology.SingularPair.localGood

variable {R}

lemma eq_zero_of_isZero {M : ModuleCat.{u} ℤ} (h : _root_.CategoryTheory.Limits.IsZero M) (m : M) : m = 0 :=
  (ModuleCat.isZero_iff_subsingleton.1 h).elim m 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.eq_zero_of_isZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.eq_zero_of_isZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.eq_zero_of_isZero ``Submission.DifferentialGeometry.Topology.SingularPair.eq_zero_of_isZero

namespace localGood

variable {X : TopCat.{u}} {n : ℕ} {A : Set X}

theorem isZero (h : localGood R X n A) {i : ℕ} (hi : n < i) : _root_.CategoryTheory.Limits.IsZero (relativeHomology R X Aᶜ i) :=
  h.1 i hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood.isZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood.isZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood.isZero ``Submission.DifferentialGeometry.Topology.SingularPair.localGood.isZero

theorem eq_zero (h : localGood R X n A) {α : relativeHomology R X Aᶜ n}
    (hα : ∀ x (hx : x ∈ A), relativeHomologyMap R (𝟙 X) (compl_mapsTo hx) n α = 0) : α = 0 :=
  h.2 α hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood.eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood.eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood.eq_zero ``Submission.DifferentialGeometry.Topology.SingularPair.localGood.eq_zero

theorem of_eq (h : localGood R X n A) {A' : Set X} (e : A = A') : localGood R X n A' :=
  e ▸ h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood.of_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood.of_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood.of_eq ``Submission.DifferentialGeometry.Topology.SingularPair.localGood.of_eq

theorem empty (X : TopCat.{u}) (n : ℕ) : localGood R X n (∅ : Set X) := by
  refine ⟨fun i _ => ?_, fun α _ => eq_zero_of_isZero ?_ α⟩ <;>
  · rw [Set.compl_empty]
    exact isZero_relativeHomology_univ R X _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood.empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood.empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood.empty ``Submission.DifferentialGeometry.Topology.SingularPair.localGood.empty

theorem of_mono_ptRes (hvan : ∀ i, n < i → _root_.CategoryTheory.Limits.IsZero (relativeHomology R X Aᶜ i)) {x : X} (hx : x ∈ A)
    (hmono : _root_.CategoryTheory.Mono (relativeHomologyMap R (𝟙 X) (compl_mapsTo hx) n)) : localGood R X n A := by
  refine ⟨hvan, fun α hα => ?_⟩
  apply (ModuleCat.mono_iff_injective _).1 hmono
  rw [hα x hx, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood.of_mono_ptRes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood.of_mono_ptRes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood.of_mono_ptRes ``Submission.DifferentialGeometry.Topology.SingularPair.localGood.of_mono_ptRes

theorem of_iso {Y : TopCat.{u}} {B : Set Y} (i : ∀ k, relativeHomology R X Aᶜ k ≅ relativeHomology R Y Bᶜ k)
    (hpt : ∀ y (hy : y ∈ B), ∃ x, ∃ hx : x ∈ A, ∃ j : relativeHomology R X {x}ᶜ n ⟶ relativeHomology R Y {y}ᶜ n,
      (i n).hom ≫ relativeHomologyMap R (𝟙 Y) (compl_mapsTo hy) n =
        relativeHomologyMap R (𝟙 X) (compl_mapsTo hx) n ≫ j)
    (hB : localGood R Y n B) : localGood R X n A := by
  refine ⟨fun k hk => (hB.1 k hk).of_iso (i k), fun α hα => ?_⟩
  have hβ : (i n).hom α = 0 := by
    refine hB.2 _ fun y hy => ?_
    obtain ⟨x, hx, j, hj⟩ := hpt y hy
    rw [← ModuleCat.comp_apply, hj, ModuleCat.comp_apply, hα x hx, map_zero]
  apply (ModuleCat.mono_iff_injective (i n).hom).1 inferInstance
  rw [hβ, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood.of_iso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood.of_iso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood.of_iso ``Submission.DifferentialGeometry.Topology.SingularPair.localGood.of_iso

theorem of_iso_map {Y : TopCat.{u}} {B : Set Y} (f : X → Y) (hf : ∀ x ∈ A, f x ∈ B)
    (hsurj : ∀ y ∈ B, ∃ x ∈ A, f x = y) (i : ∀ k, relativeHomology R X Aᶜ k ≅ relativeHomology R Y Bᶜ k)
    (j : ∀ x, x ∈ A → (relativeHomology R X {x}ᶜ n ⟶ relativeHomology R Y {f x}ᶜ n))
    (hj : ∀ x (hx : x ∈ A), (i n).hom ≫ relativeHomologyMap R (𝟙 Y) (compl_mapsTo (hf x hx)) n =
      relativeHomologyMap R (𝟙 X) (compl_mapsTo hx) n ≫ j x hx)
    (hB : localGood R Y n B) : localGood R X n A := by
  refine of_iso i (fun y hy => ?_) hB
  obtain ⟨x, hx, rfl⟩ := hsurj y hy
  exact ⟨x, hx, j x hx, hj x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood.of_iso_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood.of_iso_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood.of_iso_map ``Submission.DifferentialGeometry.Topology.SingularPair.localGood.of_iso_map

theorem iff_of_iso {Y : TopCat.{u}} {B : Set Y} (i : ∀ k, relativeHomology R X Aᶜ k ≅ relativeHomology R Y Bᶜ k)
    (hpt : ∀ y (hy : y ∈ B), ∃ x, ∃ hx : x ∈ A, ∃ j : relativeHomology R X {x}ᶜ n ≅ relativeHomology R Y {y}ᶜ n,
      (i n).hom ≫ relativeHomologyMap R (𝟙 Y) (compl_mapsTo hy) n =
        relativeHomologyMap R (𝟙 X) (compl_mapsTo hx) n ≫ j.hom)
    (hpt' : ∀ x (hx : x ∈ A), ∃ y, ∃ hy : y ∈ B, ∃ j : relativeHomology R X {x}ᶜ n ≅ relativeHomology R Y {y}ᶜ n,
      (i n).hom ≫ relativeHomologyMap R (𝟙 Y) (compl_mapsTo hy) n =
        relativeHomologyMap R (𝟙 X) (compl_mapsTo hx) n ≫ j.hom) :
    localGood R X n A ↔ localGood R Y n B := by
  constructor
  · refine fun hA => of_iso (fun k => (i k).symm) (fun x hx => ?_) hA
    obtain ⟨y, hy, j, hj⟩ := hpt' x hx
    refine ⟨y, hy, j.inv, ?_⟩
    rw [Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hj, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  · exact fun hB => of_iso i (fun y hy => by
      obtain ⟨x, hx, j, hj⟩ := hpt y hy
      exact ⟨x, hx, j.hom, hj⟩) hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood.iff_of_iso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood.iff_of_iso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood.iff_of_iso ``Submission.DifferentialGeometry.Topology.SingularPair.localGood.iff_of_iso

theorem of_convex {n : ℕ} (hn : 1 ≤ n) {C : Set (EU.{u} n)} (hC : Convex ℝ C)
    (hCc : IsCompact C) : localGood R (TopCat.of (EU n)) n C := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact empty _ _
  · exact of_mono_ptRes (fun i hi => isZero_relativeHomology_compl_convex R hC hCc ⟨x, hx⟩ hi) hx
      (have := isIso_ptRes_of_convex R hn hC hCc hx n; inferInstance)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood.of_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood.of_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood.of_convex ``Submission.DifferentialGeometry.Topology.SingularPair.localGood.of_convex

theorem singleton {n : ℕ} (hn : 1 ≤ n) (x : EU.{u} n) :
    localGood R (TopCat.of (EU n)) n {x} :=
  of_convex hn (convex_singleton x) isCompact_singleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood.singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood.singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood.singleton ``Submission.DifferentialGeometry.Topology.SingularPair.localGood.singleton

end localGood

end DifferentialGeometry.Topology.SingularPair

end
