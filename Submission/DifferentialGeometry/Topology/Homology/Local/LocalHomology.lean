import Submission.DifferentialGeometry.Topology.Homology.Local.Radial
import Submission.DifferentialGeometry.Topology.Homology.Relative.DeltaIso

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.Metric
open scoped _root_.ContinuousMap

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

theorem isZero_singularHomology_EU (n k : ℕ) (hk : k ≠ 0) : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of (EU.{u} n)) k) :=
  isZero_of_contractible R (EU n) k hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isZero_singularHomology_EU then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isZero_singularHomology_EU"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isZero_singularHomology_EU ``Submission.DifferentialGeometry.Topology.SingularPair.isZero_singularHomology_EU

theorem isZero_reducedHomologyZero_EU (n : ℕ) : _root_.CategoryTheory.Limits.IsZero (reducedHomologyZero R (TopCat.of (EU.{u} n))) :=
  isZero_reducedHomologyZero_of_contractible R (EU n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isZero_reducedHomologyZero_EU then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isZero_reducedHomologyZero_EU"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isZero_reducedHomologyZero_EU ``Submission.DifferentialGeometry.Topology.SingularPair.isZero_reducedHomologyZero_EU

lemma compl_mapsTo {X : TopCat.{u}} {A : Set X} {x : X} (hx : x ∈ A) :
    Set.MapsTo (𝟙 X) Aᶜ {x}ᶜ :=
  fun y hy (h : y = x) => hy (h ▸ hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.compl_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.compl_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.compl_mapsTo ``Submission.DifferentialGeometry.Topology.SingularPair.compl_mapsTo

lemma isIso_of_isZero_src_tgt {𝒞 : Type*} [_root_.CategoryTheory.Category 𝒞] {X Y : 𝒞} (hX : _root_.CategoryTheory.Limits.IsZero X)
    (hY : _root_.CategoryTheory.Limits.IsZero Y) (f : X ⟶ Y) : _root_.CategoryTheory.IsIso f :=
  ⟨(hX.iso hY).inv, hX.eq_of_src _ _, hY.eq_of_src _ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_of_isZero_src_tgt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_of_isZero_src_tgt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_of_isZero_src_tgt ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_of_isZero_src_tgt

section Convex

variable {n : ℕ} {C : Set (EU.{u} n)} {x : EU.{u} n}

lemma restr_id_compl_eq (hC : Convex ℝ C) (hCb : Bornology.IsBounded C) (hx : x ∈ C) :
    restr (𝟙 (TopCat.of (EU n))) (compl_mapsTo hx) =
      TopCat.ofHom (homotopyEquivComplConvexSingleton hC hCb hx).toFun := by
  ext y
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.restr_id_compl_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.restr_id_compl_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.restr_id_compl_eq ``Submission.DifferentialGeometry.Topology.SingularPair.restr_id_compl_eq

lemma isIso_singularHomologyMap_restr_id_compl (hC : Convex ℝ C) (hCb : Bornology.IsBounded C) (hx : x ∈ C)
    (k : ℕ) : _root_.CategoryTheory.IsIso (singularHomologyMap R (restr (𝟙 (TopCat.of (EU n))) (compl_mapsTo hx)) k) := by
  rw [restr_id_compl_eq hC hCb hx]
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_singularHomologyMap_restr_id_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_singularHomologyMap_restr_id_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_singularHomologyMap_restr_id_compl ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_singularHomologyMap_restr_id_compl

lemma nonempty_compl_of_isBounded (hn : 1 ≤ n) (hCb : Bornology.IsBounded C) :
    Nonempty (Cᶜ : Set (EU.{u} n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨y, hy⟩ := Set.nonempty_compl.2 fun h =>
    NormedSpace.unbounded_univ ℝ (EU.{u} (m + 1)) (h ▸ hCb)
  exact ⟨⟨y, hy⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.nonempty_compl_of_isBounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.nonempty_compl_of_isBounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.nonempty_compl_of_isBounded ``Submission.DifferentialGeometry.Topology.SingularPair.nonempty_compl_of_isBounded

lemma nonempty_compl_singleton (hn : 1 ≤ n) (x : EU.{u} n) :
    Nonempty (({x}ᶜ : Set (EU.{u} n))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨y, hy⟩ := exists_ne x
  exact ⟨⟨y, Set.mem_compl_singleton_iff.2 hy⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.nonempty_compl_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.nonempty_compl_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.nonempty_compl_singleton ``Submission.DifferentialGeometry.Topology.SingularPair.nonempty_compl_singleton

theorem isIso_ptRes_of_convex (hn : 1 ≤ n) (hC : Convex ℝ C) (hCc : IsCompact C) (hx : x ∈ C)
    (k : ℕ) : _root_.CategoryTheory.IsIso (relativeHomologyMap R (𝟙 (TopCat.of (EU n))) (compl_mapsTo hx) k) := by
  have hCb := hCc.isBounded
  match k with
  | 0 =>
    have := nonempty_compl_of_isBounded hn hCb
    have := nonempty_compl_singleton hn x
    exact isIso_of_isZero_src_tgt (isZero_relativeHomology_zero_of_pathConnected R (TopCat.of (EU n)) Cᶜ)
      (isZero_relativeHomology_zero_of_pathConnected R (TopCat.of (EU n)) {x}ᶜ) _
  | 1 =>
    have hsq := δred_natural R (𝟙 (TopCat.of (EU n))) (compl_mapsTo hx)
    have h₁ : _root_.CategoryTheory.IsIso (δred R (TopCat.of (EU n)) Cᶜ) :=
      isIso_δred_of_isZero R _ _ (isZero_singularHomology_EU R n 1 one_ne_zero) (isZero_reducedHomologyZero_EU R n)
    have h₂ : _root_.CategoryTheory.IsIso (δred R (TopCat.of (EU n)) {x}ᶜ) :=
      isIso_δred_of_isZero R _ _ (isZero_singularHomology_EU R n 1 one_ne_zero) (isZero_reducedHomologyZero_EU R n)
    have h₃ : _root_.CategoryTheory.IsIso (reducedHomologyZeroMap R (restr (𝟙 (TopCat.of (EU n))) (compl_mapsTo hx))) :=
      have := isIso_singularHomologyMap_restr_id_compl R hC hCb hx 0
      isIso_reducedHomologyZeroMap R _
    have : relativeHomologyMap R (𝟙 (TopCat.of (EU n))) (compl_mapsTo hx) 1 =
        δred R (TopCat.of (EU n)) Cᶜ ≫
          reducedHomologyZeroMap R (restr (𝟙 (TopCat.of (EU n))) (compl_mapsTo hx)) ≫
            inv (δred R (TopCat.of (EU n)) {x}ᶜ) := by
      rw [← Category.assoc, hsq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [this]
    infer_instance
  | i + 2 =>
    have hsq := δ_natural R (𝟙 (TopCat.of (EU n))) (compl_mapsTo hx) (i + 1)
    have h₁ : _root_.CategoryTheory.IsIso (δ R (TopCat.of (EU n)) Cᶜ (i + 1)) :=
      isIso_δ_of_isZero R _ _ i (isZero_singularHomology_EU R n (i + 2) (by omega))
        (isZero_singularHomology_EU R n (i + 1) (by omega))
    have h₂ : _root_.CategoryTheory.IsIso (δ R (TopCat.of (EU n)) {x}ᶜ (i + 1)) :=
      isIso_δ_of_isZero R _ _ i (isZero_singularHomology_EU R n (i + 2) (by omega))
        (isZero_singularHomology_EU R n (i + 1) (by omega))
    have h₃ := isIso_singularHomologyMap_restr_id_compl R hC hCb hx (i + 1)
    have : relativeHomologyMap R (𝟙 (TopCat.of (EU n))) (compl_mapsTo hx) (i + 2) =
        δ R (TopCat.of (EU n)) Cᶜ (i + 1) ≫
          singularHomologyMap R (restr (𝟙 (TopCat.of (EU n))) (compl_mapsTo hx)) (i + 1) ≫
            inv (δ R (TopCat.of (EU n)) {x}ᶜ (i + 1)) := by
      rw [← Category.assoc, hsq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [this]
    infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_ptRes_of_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_ptRes_of_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_ptRes_of_convex ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_ptRes_of_convex

end Convex

theorem isZero_relativeHomology_EU_compl_singleton {n : ℕ} (hn : 1 ≤ n) (x : EU.{u} n) {k : ℕ}
    (hk : k ≠ n) : _root_.CategoryTheory.Limits.IsZero (relativeHomology R (TopCat.of (EU n)) {x}ᶜ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e := puncturedEUHomotopyEquivSph m x
  match k, hk with
  | 0, _ =>
    have := nonempty_compl_singleton hn x
    exact isZero_relativeHomology_zero_of_pathConnected R (TopCat.of (EU (m + 1))) {x}ᶜ
  | 1, hk =>
    exact ((Sphere.isZero_reducedHomologyZero_sphere R m (by omega)).of_iso
      (Sphere.reducedHomologyZeroIsoOfHomotopyEquivSphere R e)).of_iso
      (δredIsoOfIsZero R _ _ (isZero_singularHomology_EU R (m + 1) 1 one_ne_zero) (isZero_reducedHomologyZero_EU R (m + 1)))
  | i + 2, hk =>
    exact ((Sphere.isZero_singularHomology_sphere R m (i + 1) (by omega) (by omega)).of_iso
      (Sphere.homologyIsoSphere R e (i + 1))).of_iso
      (δIsoOfIsZero R _ _ i (isZero_singularHomology_EU R (m + 1) (i + 2) (by omega))
        (isZero_singularHomology_EU R (m + 1) (i + 1) (by omega)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_EU_compl_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_EU_compl_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_EU_compl_singleton ``Submission.DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_EU_compl_singleton

def relativeHomologyEuclideanPointIso {n : ℕ} (hn : 1 ≤ n) (x : EU.{u} n) :
    relativeHomology R (TopCat.of (EU n)) {x}ᶜ n ≅ R :=
  match n, hn, x with
  | 0, hn, _ => absurd hn (by decide)
  | 1, _, x =>
    δredIsoOfIsZero R _ _ (isZero_singularHomology_EU R 1 1 one_ne_zero) (isZero_reducedHomologyZero_EU R 1) ≪≫
      Sphere.reducedHomologyZeroIsoOfHomotopyEquivZeroSphere R (puncturedEUHomotopyEquivSph 0 x)
  | j + 2, _, x =>
    δIsoOfIsZero R _ _ j (isZero_singularHomology_EU R (j + 2) (j + 2) (by omega))
        (isZero_singularHomology_EU R (j + 2) (j + 1) (by omega)) ≪≫
      Sphere.homologyIsoSphere R (puncturedEUHomotopyEquivSph (j + 1) x) (j + 1) ≪≫
        Sphere.singularHomologyTopLiftedSphereIso R (j + 1) (by omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyEuclideanPointIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyEuclideanPointIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyEuclideanPointIso ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyEuclideanPointIso

private lemma isIso_relπ_empty_aux (X : TopCat.{u}) (k : ℕ) : _root_.CategoryTheory.IsIso (relπ R X ∅ k) := by
  have : (pair X ∅).left.HasDimensionLT 0 := by
    rw [← SSet.notNonempty_iff_hasDimensionLT_zero]
    rintro ⟨σ⟩
    exact ((TopCat.of (∅ : Set X)).toSSetObjEquiv _ σ (Classical.arbitrary _)).2
  have : _root_.CategoryTheory.IsIso ((pair X ∅).chainComplexπ R) := inferInstance
  exact inferInstanceAs (_root_.CategoryTheory.IsIso (HomologicalComplex.homologyMap ((pair X ∅).chainComplexπ R) k))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_relπ_empty_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SingularPair.isIso_relπ_empty_aux target :: scope.openDecls } }

theorem isZero_relativeHomology_compl_convex {n : ℕ} {C : Set (EU.{u} n)} (hC : Convex ℝ C)
    (hCc : IsCompact C) (hne : C.Nonempty) {k : ℕ} (hk : n < k) :
    IsZero (relativeHomology R (TopCat.of (EU n)) Cᶜ k) := by
  obtain ⟨x, hx⟩ := hne
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hCu : C = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    rw [hCu, Set.compl_univ]
    have := isIso_relπ_empty_aux R (TopCat.of (EU 0)) k
    exact (isZero_singularHomology_EU R 0 k (by omega)).of_iso (_root_.CategoryTheory.asIso (relπ R (TopCat.of (EU 0)) ∅ k)).symm
  · have := isIso_ptRes_of_convex R hn hC hCc hx k
    exact (isZero_relativeHomology_EU_compl_singleton R hn x (by omega)).of_iso
      (_root_.CategoryTheory.asIso (relativeHomologyMap R (𝟙 (TopCat.of (EU n))) (compl_mapsTo hx) k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_compl_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_compl_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_compl_convex ``Submission.DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_compl_convex

end DifferentialGeometry.Topology.SingularPair

end
