import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Finset

namespace DifferentialGeometry.Topology.SimplicialComplex

variable {ι : Type*}


def link [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Finset ι) :
    PreAbstractSimplicialComplex ι where
  faces := {t | t.Nonempty ∧ Disjoint s t ∧ s ∪ t ∈ K}
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    intro u hut hu
    refine ⟨hu, ht.2.1.mono_right hut, ?_⟩
    exact (K.isRelLowerSet_faces ht.2.2).2 (_root_.Finset.union_subset_union_right hut)
      (hu.mono _root_.Finset.subset_union_right)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.link then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.link"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.link ``Submission.DifferentialGeometry.Topology.SimplicialComplex.link

@[simp]
theorem mem_link [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {s t : Finset ι} :
    t ∈ link K s ↔ t.Nonempty ∧ Disjoint s t ∧ s ∪ t ∈ K := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.mem_link then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.mem_link"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.mem_link ``Submission.DifferentialGeometry.Topology.SimplicialComplex.mem_link

theorem link_le [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Finset ι) :
    link K s ≤ K := by
  intro t ht
  exact (K.isRelLowerSet_faces ht.2.2).2 _root_.Finset.subset_union_right ht.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.link_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.link_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.link_le ``Submission.DifferentialGeometry.Topology.SimplicialComplex.link_le

instance _root_.Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesLink [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) [Finite K.faces]
    (s : Finset ι) : Finite (link K s).faces :=
  Set.Finite.to_subtype ((Set.toFinite K.faces).subset (link_le K s))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesLink then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesLink"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesLink ``Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesLink

instance _root_.Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesBotPreAbstractSimplicialComplex_differentialGeometry : Finite (⊥ : PreAbstractSimplicialComplex ι).faces :=
  Set.finite_empty.to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesBotPreAbstractSimplicialComplex_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesBotPreAbstractSimplicialComplex_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesBotPreAbstractSimplicialComplex_differentialGeometry ``Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesBotPreAbstractSimplicialComplex_differentialGeometry

instance _root_.Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMaxPreAbstractSimplicialComplex_differentialGeometry (K L : PreAbstractSimplicialComplex ι) [Finite K.faces] [Finite L.faces] :
    Finite (K ⊔ L).faces :=
  ((Set.toFinite K.faces).union (Set.toFinite L.faces)).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMaxPreAbstractSimplicialComplex_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMaxPreAbstractSimplicialComplex_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMaxPreAbstractSimplicialComplex_differentialGeometry ``Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMaxPreAbstractSimplicialComplex_differentialGeometry

instance _root_.Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMinPreAbstractSimplicialComplex_differentialGeometry (K : PreAbstractSimplicialComplex ι) [Finite K.faces]
    (L : PreAbstractSimplicialComplex ι) : Finite (K ⊓ L).faces :=
  ((Set.toFinite K.faces).subset Set.inter_subset_left).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMinPreAbstractSimplicialComplex_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMinPreAbstractSimplicialComplex_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMinPreAbstractSimplicialComplex_differentialGeometry ``Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMinPreAbstractSimplicialComplex_differentialGeometry

instance _root_.Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMap_differentialGeometry {κ : Type*} [DecidableEq κ] (K : PreAbstractSimplicialComplex ι) [Finite K.faces]
    (f : ι → κ) : Finite (K.map f).faces :=
  ((Set.toFinite K.faces).image (fun s => s.image f)).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMap_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMap_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMap_differentialGeometry ``Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesMap_differentialGeometry

noncomputable section

variable (K : PreAbstractSimplicialComplex ι) [Finite K.faces]


def facesOfCard (n : ℕ) : Finset (Finset ι) :=
  (Set.toFinite K.faces).toFinset.filter (fun s => s.card = n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.facesOfCard then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.facesOfCard"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.facesOfCard ``Submission.DifferentialGeometry.Topology.SimplicialComplex.facesOfCard

@[simp]
theorem mem_facesOfCard {n : ℕ} {s : Finset ι} :
    s ∈ facesOfCard K n ↔ s ∈ K ∧ s.card = n := by
  classical
  change s ∈ (Set.toFinite K.faces).toFinset.filter (fun s => s.card = n) ↔
    s ∈ K.faces ∧ s.card = n
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.mem_facesOfCard then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.mem_facesOfCard"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.mem_facesOfCard ``Submission.DifferentialGeometry.Topology.SimplicialComplex.mem_facesOfCard

@[simp]
theorem facesOfCard_zero : facesOfCard K 0 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hs, hcard⟩ := (mem_facesOfCard K).mp hs
  exact (K.isRelLowerSet_faces hs).1.ne_empty (card_eq_zero.mp hcard)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_zero ``Submission.DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_zero


def cofaces [DecidableEq ι] (s : Finset ι) (n : ℕ) : Finset (Finset ι) :=
  (facesOfCard K n).filter (s ⊆ ·)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.cofaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.cofaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.cofaces ``Submission.DifferentialGeometry.Topology.SimplicialComplex.cofaces

@[simp]
theorem mem_cofaces [DecidableEq ι] {s t : Finset ι} {n : ℕ} :
    t ∈ cofaces K s n ↔ t ∈ K ∧ t.card = n ∧ s ⊆ t := by
  simp [cofaces, and_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.mem_cofaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.mem_cofaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.mem_cofaces ``Submission.DifferentialGeometry.Topology.SimplicialComplex.mem_cofaces

def linkFaceEquiv [DecidableEq ι] (s : Finset ι) (n : ℕ) (hn : 0 < n) :
    {t // t ∈ facesOfCard (link K s) n} ≃
      {u // u ∈ cofaces K s (s.card + n)} where
  toFun t := ⟨s ∪ t.1, by
    obtain ⟨⟨_, hd, hface⟩, hc⟩ := (mem_facesOfCard (link K s)).mp t.2
    exact (mem_cofaces K).mpr ⟨hface, by rw [_root_.Finset.card_union_of_disjoint hd, hc],
      subset_union_left⟩⟩
  invFun u := ⟨u.1 \ s, by
    obtain ⟨hface, hc, hsu⟩ := (mem_cofaces K).mp u.2
    have hcard : (u.1 \ s).card = n := by
      rw [_root_.Finset.card_sdiff_of_subset hsu, hc, Nat.add_sub_cancel_left]
    apply (mem_facesOfCard (link K s)).mpr
    exact ⟨⟨card_pos.mp (by omega), disjoint_sdiff_self_right,
      by simpa only [_root_.Finset.union_sdiff_of_subset hsu] using hface⟩, hcard⟩⟩
  left_inv t := by
    apply Subtype.ext
    exact _root_.Finset.union_sdiff_cancel_left ((mem_facesOfCard (link K s)).mp t.2).1.2.1
  right_inv u := by
    apply Subtype.ext
    exact _root_.Finset.union_sdiff_of_subset ((mem_cofaces K).mp u.2).2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.linkFaceEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.linkFaceEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.linkFaceEquiv ``Submission.DifferentialGeometry.Topology.SimplicialComplex.linkFaceEquiv

@[simp]
theorem linkFaceEquiv_apply [DecidableEq ι] (s : Finset ι) (n : ℕ) (hn : 0 < n)
    (t : {t // t ∈ facesOfCard (link K s) n}) :
    (linkFaceEquiv K s n hn t).1 = s ∪ t.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.linkFaceEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.linkFaceEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.linkFaceEquiv_apply ``Submission.DifferentialGeometry.Topology.SimplicialComplex.linkFaceEquiv_apply

@[simp]
theorem linkFaceEquiv_symm_apply [DecidableEq ι] (s : Finset ι) (n : ℕ) (hn : 0 < n)
    (u : {u // u ∈ cofaces K s (s.card + n)}) :
    ((linkFaceEquiv K s n hn).symm u).1 = u.1 \ s := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.linkFaceEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.linkFaceEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.linkFaceEquiv_symm_apply ``Submission.DifferentialGeometry.Topology.SimplicialComplex.linkFaceEquiv_symm_apply


theorem card_facesOfCard_link [DecidableEq ι] (s : Finset ι) (n : ℕ) (hn : 0 < n) :
    (facesOfCard (link K s) n).card = (cofaces K s (s.card + n)).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (linkFaceEquiv K s n hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.card_facesOfCard_link then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.card_facesOfCard_link"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.card_facesOfCard_link ``Submission.DifferentialGeometry.Topology.SimplicialComplex.card_facesOfCard_link

theorem sum_card_cofaces [DecidableEq ι] (k n : ℕ) (hk : 0 < k) :
    ∑ s ∈ facesOfCard K k, (cofaces K s n).card =
      n.choose k * (facesOfCard K n).card := by
  classical
  have hcount (t : Finset ι) (ht : t ∈ facesOfCard K n) :
      ((facesOfCard K k).filter (· ⊆ t)) = t.powersetCard k := by
    ext s
    simp only [_root_.Finset.mem_filter, mem_facesOfCard, _root_.Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hs⟩, hst⟩
      exact ⟨hst, hs⟩
    · rintro ⟨hst, hs⟩
      exact ⟨⟨(K.isRelLowerSet_faces ((mem_facesOfCard K).mp ht).1).2 hst
        (card_pos.mp (hs ▸ hk)), hs⟩, hst⟩
  calc
    _ = ∑ t ∈ facesOfCard K n, ((facesOfCard K k).filter (· ⊆ t)).card := by
      exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (fun s t : Finset ι => s ⊆ t)
    _ = ∑ t ∈ facesOfCard K n, n.choose k := by
      apply _root_.Finset.sum_congr rfl
      intro t ht
      rw [hcount t ht, _root_.Finset.card_powersetCard, ((mem_facesOfCard K).mp ht).2]
    _ = _ := by simp [Nat.mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.sum_card_cofaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.sum_card_cofaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.sum_card_cofaces ``Submission.DifferentialGeometry.Topology.SimplicialComplex.sum_card_cofaces


theorem sum_card_facesOfCard_link [DecidableEq ι] (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    ∑ s ∈ facesOfCard K k, (facesOfCard (link K s) n).card =
      (k + n).choose k * (facesOfCard K (k + n)).card := by
  calc
    _ = ∑ s ∈ facesOfCard K k, (cofaces K s (k + n)).card := by
      apply _root_.Finset.sum_congr rfl
      intro s hs
      rw [card_facesOfCard_link K s n hn, ((mem_facesOfCard K).mp hs).2]
    _ = _ := sum_card_cofaces K k (k + n) hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.sum_card_facesOfCard_link then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.sum_card_facesOfCard_link"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.sum_card_facesOfCard_link ``Submission.DifferentialGeometry.Topology.SimplicialComplex.sum_card_facesOfCard_link

end

end DifferentialGeometry.Topology.SimplicialComplex
