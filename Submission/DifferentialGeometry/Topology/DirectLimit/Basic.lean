import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Separation.Hausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u

namespace DifferentialGeometry

open _root_.Set _root_.Topology

structure SeqSystem (A : ℕ → Type u) [∀ k, TopologicalSpace (A k)] where
  map : ∀ {k ℓ : ℕ}, k ≤ ℓ → A k → A ℓ
  map_self : ∀ (k : ℕ) (x : A k), map (le_refl k) x = x
  map_map : ∀ {k ℓ m : ℕ} (h1 : k ≤ ℓ) (h2 : ℓ ≤ m) (x : A k),
    map h2 (map h1 x) = map (h1.trans h2) x
  isOpenEmb : ∀ {k ℓ : ℕ} (h : k ≤ ℓ), _root_.Topology.IsOpenEmbedding (map h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem ``Submission.DifferentialGeometry.SeqSystem

namespace SeqSystem

variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] (S : SeqSystem A)


def succMap (f : ∀ k, A k → A (k + 1)) {k ℓ : ℕ} (h : k ≤ ℓ) : A k → A ℓ :=
  fun x => Nat.leRecOn h (@fun k => f k) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.succMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.succMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.succMap ``Submission.DifferentialGeometry.SeqSystem.succMap


theorem succMap_isOpenEmb (f : ∀ k, A k → A (k + 1))
    (hf : ∀ k, _root_.Topology.IsOpenEmbedding (f k)) {k ℓ : ℕ} (h : k ≤ ℓ) :
    IsOpenEmbedding (succMap f h) := by
  induction ℓ, h using Nat.le_induction with
  | base =>
      have hfun : succMap f (Nat.le_refl k) = id := by
        funext x
        exact Nat.leRecOn_self x
      rw [hfun]
      exact IsOpenEmbedding.id
  | succ ℓ hkℓ ih =>
      have hfun : succMap f (Nat.le.step hkℓ) = f ℓ ∘ succMap f hkℓ := by
        funext x
        exact Nat.leRecOn_succ hkℓ x
      rw [hfun]
      exact (hf ℓ).comp ih

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.succMap_isOpenEmb then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.succMap_isOpenEmb"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.succMap_isOpenEmb ``Submission.DifferentialGeometry.SeqSystem.succMap_isOpenEmb


def ofSucc (f : ∀ k, A k → A (k + 1)) (hf : ∀ k, _root_.Topology.IsOpenEmbedding (f k)) : SeqSystem A where
  map h := succMap f h
  map_self _ x := Nat.leRecOn_self x
  map_map h₁ h₂ x := (Nat.leRecOn_trans h₁ h₂ x).symm
  isOpenEmb h := succMap_isOpenEmb f hf h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.ofSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.ofSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.ofSucc ``Submission.DifferentialGeometry.SeqSystem.ofSucc

theorem map_proof_irrel {k ℓ : ℕ} (h₁ h₂ : k ≤ ℓ) :
    S.map h₁ = S.map h₂ := by
  rw [Subsingleton.elim h₁ h₂]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.map_proof_irrel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.map_proof_irrel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.map_proof_irrel ``Submission.DifferentialGeometry.SeqSystem.map_proof_irrel


theorem map_apply_irrel {k ℓ : ℕ} (h₁ h₂ : k ≤ ℓ) (x : A k) :
    S.map h₁ x = S.map h₂ x := by
  rw [S.map_proof_irrel h₁ h₂]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.map_apply_irrel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.map_apply_irrel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.map_apply_irrel ``Submission.DifferentialGeometry.SeqSystem.map_apply_irrel


def Rel (p q : Σ k, A k) : Prop :=
  ∃ (m : ℕ) (hp : p.1 ≤ m) (hq : q.1 ≤ m), S.map hp p.2 = S.map hq q.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.Rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.Rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.Rel ``Submission.DifferentialGeometry.SeqSystem.Rel

theorem rel_refl (p : Σ k, A k) : S.Rel p p :=
  ⟨p.1, le_refl _, le_refl _, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.rel_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.rel_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.rel_refl ``Submission.DifferentialGeometry.SeqSystem.rel_refl

theorem rel_symm {p q : Σ k, A k} (h : S.Rel p q) : S.Rel q p := by
  obtain ⟨m, hp, hq, he⟩ := h
  exact ⟨m, hq, hp, he.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.rel_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.rel_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.rel_symm ``Submission.DifferentialGeometry.SeqSystem.rel_symm

theorem rel_trans {p q r : Σ k, A k} (h1 : S.Rel p q) (h2 : S.Rel q r) : S.Rel p r := by
  obtain ⟨m1, hp1, hq1, e1⟩ := h1
  obtain ⟨m2, hq2, hr2, e2⟩ := h2
  refine ⟨max m1 m2, hp1.trans (le_max_left _ _), hr2.trans (le_max_right _ _), ?_⟩
  have e1' := congrArg (S.map (le_max_left m1 m2)) e1
  have e2' := congrArg (S.map (le_max_right m1 m2)) e2
  rw [S.map_map, S.map_map] at e1'
  rw [S.map_map, S.map_map] at e2'
  exact e1'.trans e2'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.rel_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.rel_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.rel_trans ``Submission.DifferentialGeometry.SeqSystem.rel_trans


def setoid : Setoid (Σ k, A k) :=
  ⟨S.Rel, fun p => S.rel_refl p, fun h => S.rel_symm h, fun h1 h2 => S.rel_trans h1 h2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.setoid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.setoid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.setoid ``Submission.DifferentialGeometry.SeqSystem.setoid

def Lim : Type u := Quotient S.setoid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.Lim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.Lim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.Lim ``Submission.DifferentialGeometry.SeqSystem.Lim

instance _root_.Submission.DifferentialGeometry.SeqSystem.instTopologicalSpaceLim : TopologicalSpace S.Lim :=
  instTopologicalSpaceQuotient

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.instTopologicalSpaceLim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.instTopologicalSpaceLim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.instTopologicalSpaceLim ``Submission.DifferentialGeometry.SeqSystem.instTopologicalSpaceLim


def incl (ℓ : ℕ) : A ℓ → S.Lim :=
  fun x => Quotient.mk S.setoid ⟨ℓ, x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.incl ``Submission.DifferentialGeometry.SeqSystem.incl


theorem incl_comp {k ℓ : ℕ} (h : k ≤ ℓ) (x : A k) :
    S.incl ℓ (S.map h x) = S.incl k x := by
  refine Quotient.sound ⟨ℓ, le_refl ℓ, h, ?_⟩
  rw [S.map_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.incl_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.incl_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.incl_comp ``Submission.DifferentialGeometry.SeqSystem.incl_comp


theorem incl_injective (ℓ : ℕ) : Function.Injective (S.incl ℓ) := by
  intro x y h
  obtain ⟨m, h1, h2, he⟩ := Quotient.exact h
  have h12 : h1 = h2 := rfl
  rw [h12] at he
  exact (S.isOpenEmb h2).injective he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.incl_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.incl_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.incl_injective ``Submission.DifferentialGeometry.SeqSystem.incl_injective


theorem exists_incl_eq (z : S.Lim) : ∃ (ℓ : ℕ) (x : A ℓ), S.incl ℓ x = z := by
  obtain ⟨⟨ℓ, x⟩, rfl⟩ := Quotient.exists_rep z
  exact ⟨ℓ, x, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.exists_incl_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.exists_incl_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.exists_incl_eq ``Submission.DifferentialGeometry.SeqSystem.exists_incl_eq

theorem continuous_incl (ℓ : ℕ) : Continuous (S.incl ℓ) :=
  continuous_quot_mk.comp continuous_sigmaMk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.continuous_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.continuous_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.continuous_incl ``Submission.DifferentialGeometry.SeqSystem.continuous_incl

theorem incl_isOpenMap (ℓ : ℕ) : IsOpenMap (S.incl ℓ) := by
  intro U hU
  have hsat : IsOpen (Quotient.mk S.setoid ⁻¹' (S.incl ℓ '' U)) := by
    rw [isOpen_sigma_iff]
    intro m
    have hfib : Sigma.mk m ⁻¹' (Quotient.mk S.setoid ⁻¹' (S.incl ℓ '' U)) =
        ⋃ (p : ℕ) (hmp : m ≤ p) (hℓp : ℓ ≤ p), S.map hmp ⁻¹' (S.map hℓp '' U) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
      constructor
      · rintro ⟨x, hxU, heq⟩
        obtain ⟨p, hℓp, hmp, he⟩ := Quotient.exact heq
        exact ⟨p, hmp, hℓp, x, hxU, he⟩
      · rintro ⟨p, hmp, hℓp, x, hxU, he⟩
        exact ⟨x, hxU, Quotient.sound ⟨p, hℓp, hmp, he⟩⟩
    rw [hfib]
    exact isOpen_iUnion fun p => isOpen_iUnion fun hmp => isOpen_iUnion fun hℓp =>
      ((S.isOpenEmb hℓp).isOpenMap U hU).preimage (S.isOpenEmb hmp).continuous
  exact isOpen_coinduced.mpr hsat

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.incl_isOpenMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.incl_isOpenMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.incl_isOpenMap ``Submission.DifferentialGeometry.SeqSystem.incl_isOpenMap


theorem incl_isOpenEmb (ℓ : ℕ) : _root_.Topology.IsOpenEmbedding (S.incl ℓ) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (S.continuous_incl ℓ)
    (S.incl_injective ℓ) (S.incl_isOpenMap ℓ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.incl_isOpenEmb then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.incl_isOpenEmb"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.incl_isOpenEmb ``Submission.DifferentialGeometry.SeqSystem.incl_isOpenEmb


theorem range_incl_mono {k ℓ : ℕ} (h : k ≤ ℓ) :
    Set.range (S.incl k) ⊆ Set.range (S.incl ℓ) := by
  rintro - ⟨x, rfl⟩
  exact ⟨S.map h x, S.incl_comp h x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.range_incl_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.range_incl_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.range_incl_mono ``Submission.DifferentialGeometry.SeqSystem.range_incl_mono


theorem iUnion_range_incl : ⋃ ℓ : ℕ, Set.range (S.incl ℓ) = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨ℓ, x, hx⟩ := S.exists_incl_eq z
  exact ⟨ℓ, x, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.iUnion_range_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.iUnion_range_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.iUnion_range_incl ``Submission.DifferentialGeometry.SeqSystem.iUnion_range_incl


theorem isOpen_iff_incl {U : Set S.Lim} :
    IsOpen U ↔ ∀ k : ℕ, IsOpen (S.incl k ⁻¹' U) := by
  constructor
  · intro hU k
    exact (S.continuous_incl k).isOpen_preimage U hU
  · intro hU
    apply isOpen_coinduced.mpr
    rw [isOpen_sigma_iff]
    intro k
    change IsOpen (S.incl k ⁻¹' U)
    exact hU k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.isOpen_iff_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.isOpen_iff_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.isOpen_iff_incl ``Submission.DifferentialGeometry.SeqSystem.isOpen_iff_incl

theorem exists_compact_stage_representation {K : Set S.Lim} (hK : IsCompact K) :
    ∃ (k : ℕ) (Kk : Set (A k)), IsCompact Kk ∧ K = S.incl k '' Kk := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun ℓ : ℕ => Set.range (S.incl ℓ))
    (fun ℓ => (S.incl_isOpenEmb ℓ).isOpen_range)
    (by rw [S.iUnion_range_incl]; exact Set.subset_univ K)
  have hsub : K ⊆ Set.range (S.incl (t.sup id)) := by
    intro z hz
    obtain ⟨ℓ, hℓt, hzℓ⟩ := Set.mem_iUnion₂.mp (ht hz)
    exact S.range_incl_mono (Finset.le_sup (f := id) hℓt) hzℓ
  refine ⟨t.sup id, S.incl (t.sup id) ⁻¹' K, ?_, (Set.image_preimage_eq_of_subset hsub).symm⟩
  have himg : IsCompact (S.incl (t.sup id) '' (S.incl (t.sup id) ⁻¹' K)) := by
    rwa [Set.image_preimage_eq_of_subset hsub]
  exact ((S.incl_isOpenEmb (t.sup id)).isEmbedding.isCompact_iff).mpr himg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.exists_compact_stage_representation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.exists_compact_stage_representation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.exists_compact_stage_representation ``Submission.DifferentialGeometry.SeqSystem.exists_compact_stage_representation

theorem compact_subset_range {K : Set S.Lim} (hK : IsCompact K) :
    ∃ k : ℕ, K ⊆ Set.range (S.incl k) := by
  obtain ⟨k, Kk, _hKk, hK_eq⟩ := S.exists_compact_stage_representation hK
  refine ⟨k, ?_⟩
  rw [hK_eq]
  rintro z ⟨x, _hx, rfl⟩
  exact ⟨x, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.compact_subset_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.compact_subset_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.compact_subset_range ``Submission.DifferentialGeometry.SeqSystem.compact_subset_range


theorem sigmaCompact [∀ k, SigmaCompactSpace (A k)] : SigmaCompactSpace S.Lim := by
  refine ⟨⟨fun n =>
    S.incl (Nat.unpair n).1 '' compactCovering (A (Nat.unpair n).1) (Nat.unpair n).2,
    fun n => ?_, ?_⟩⟩
  · exact (isCompact_compactCovering _ _).image (S.continuous_incl _)
  · ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨ℓ, x, hx⟩ := S.exists_incl_eq z
    have hxcov : x ∈ ⋃ j, compactCovering (A ℓ) j := by
      rw [iUnion_compactCovering]
      exact Set.mem_univ x
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxcov
    refine ⟨Nat.pair ℓ j, ?_⟩
    rw [Nat.unpair_pair]
    exact ⟨x, hj, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.sigmaCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.sigmaCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.sigmaCompact ``Submission.DifferentialGeometry.SeqSystem.sigmaCompact


theorem t2Space [∀ k, T2Space (A k)] : T2Space S.Lim := by
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨k, a, rfl⟩ := S.exists_incl_eq x
  obtain ⟨ℓ, b, rfl⟩ := S.exists_incl_eq y
  have hax : S.incl (_root_.Max.max k ℓ) (S.map (le_max_left k ℓ) a) = S.incl k a :=
    S.incl_comp (le_max_left k ℓ) a
  have hbx : S.incl (_root_.Max.max k ℓ) (S.map (le_max_right k ℓ) b) = S.incl ℓ b :=
    S.incl_comp (le_max_right k ℓ) b
  have hab : S.map (le_max_left k ℓ) a ≠ S.map (le_max_right k ℓ) b := by
    intro h
    apply hxy
    rw [← hax, ← hbx, h]
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := t2_separation hab
  refine ⟨S.incl (_root_.Max.max k ℓ) '' U, S.incl (_root_.Max.max k ℓ) '' V,
    S.incl_isOpenMap _ U hU, S.incl_isOpenMap _ V hV, ?_, ?_, ?_⟩
  · rw [← hax]
    exact Set.mem_image_of_mem _ haU
  · rw [← hbx]
    exact Set.mem_image_of_mem _ hbV
  · exact (Set.disjoint_image_iff (S.incl_injective _)).mpr hUV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.t2Space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.t2Space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.t2Space ``Submission.DifferentialGeometry.SeqSystem.t2Space


def lift {X : Type*} (ψ : ∀ k, A k → X)
    (hψ : ∀ {k ℓ : ℕ} (h : k ≤ ℓ) (x : A k), ψ ℓ (S.map h x) = ψ k x) : S.Lim → X :=
  Quotient.lift (fun p : Σ k, A k => ψ p.1 p.2) (by
    rintro ⟨k, x⟩ ⟨ℓ, y⟩ ⟨m, h1, h2, he⟩
    have h := congrArg (ψ m) he
    rwa [hψ h1 x, hψ h2 y] at h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.lift ``Submission.DifferentialGeometry.SeqSystem.lift

theorem lift_incl {X : Type*} (ψ : ∀ k, A k → X)
    (hψ : ∀ {k ℓ : ℕ} (h : k ≤ ℓ) (x : A k), ψ ℓ (S.map h x) = ψ k x)
    (ℓ : ℕ) (x : A ℓ) : S.lift ψ hψ (S.incl ℓ x) = ψ ℓ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.lift_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.lift_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.lift_incl ``Submission.DifferentialGeometry.SeqSystem.lift_incl

theorem continuous_lift {X : Type*} [TopologicalSpace X] (ψ : ∀ k, A k → X)
    (hψ : ∀ {k ℓ : ℕ} (h : k ≤ ℓ) (x : A k), ψ ℓ (S.map h x) = ψ k x)
    (hcont : ∀ k, Continuous (ψ k)) : Continuous (S.lift ψ hψ) := by
  apply Continuous.quotient_lift
  exact continuous_sigma fun k => hcont k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.continuous_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.continuous_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.continuous_lift ``Submission.DifferentialGeometry.SeqSystem.continuous_lift

theorem continuous_iff_incl {X : Type*} [TopologicalSpace X] {f : S.Lim → X} :
    Continuous f ↔ ∀ k : ℕ, Continuous (f ∘ S.incl k) := by
  constructor
  · intro hf k
    exact hf.comp (S.continuous_incl k)
  · intro hf
    rw [continuous_def]
    intro U hU
    rw [S.isOpen_iff_incl]
    intro k
    change IsOpen ((f ∘ S.incl k) ⁻¹' U)
    exact (hf k).isOpen_preimage U hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SeqSystem.continuous_iff_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SeqSystem.continuous_iff_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SeqSystem.continuous_iff_incl ``Submission.DifferentialGeometry.SeqSystem.continuous_iff_incl

end SeqSystem

end DifferentialGeometry
