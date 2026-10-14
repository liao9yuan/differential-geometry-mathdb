import Submission.DifferentialGeometry.Topology.Attachment.TransitionGluing
import Submission.DifferentialGeometry.Topology.Embedding.SubtypePreimage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Topology _root_.Submission.Topology
universe u
namespace TopCat.GlueData
open _root_.TopCat _root_.TopCat.GlueData
variable {ι E : Type u} [TopologicalSpace E]
    (U : Set E) (hU : IsOpen U) (near : ι → ι → Bool)
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hJ : ∀ a, ContinuousOn (J a) U)
    (hrefl : ∀ i, near i i = true)
    (hsymm : ∀ i j, near i j = true → near j i = true)
    (hself : ∀ i x, x ∈ U → J ⟨(i, i), hrefl i⟩ x = x)
    (hinv : ∀ i j (h : near i j = true) x, x ∈ U → J ⟨(i, j), h⟩ x ∈ U →
      J ⟨(j, i), hsymm i j h⟩ (J ⟨(i, j), h⟩ x) = x)
    (htrans : ∀ i j k (hij : near i j = true) (hjk : near j k = true) x,
      x ∈ U → J ⟨(i, j), hij⟩ x ∈ U → J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x) ∈ U →
      ∃ hik : near i k = true,
        J ⟨(i, k), hik⟩ x = J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x))


open _root_.TopCat _root_.TopCat.GlueData in
theorem ofTransitionMaps_ι_eq_iff_graph (i j : ι) (z w : U) :
    (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι i z =
      (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι j w ↔
      ∃ h : near i j = _root_.Bool.true, J ⟨(i, j), h⟩ z = w :=
  ((ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).ι_eq_iff_rel i j z w).trans
    (rel_iff_graph U hU near J hJ hrefl hsymm hself hinv htrans i j z w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TopCat.GlueData.ofTransitionMaps_ι_eq_iff_graph then
    throwError "Refusing to shadow existing declaration TopCat.GlueData.ofTransitionMaps_ι_eq_iff_graph"
  Lean.modifyEnv fun env => Lean.addAlias env `TopCat.GlueData.ofTransitionMaps_ι_eq_iff_graph ``Submission.TopCat.GlueData.ofTransitionMaps_ι_eq_iff_graph


open _root_.TopCat _root_.TopCat.GlueData in
theorem ofTransitionMaps_near_of_nonempty_inter_range (i j : ι)
    (h : (_root_.Set.range ((ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι i) ∩
      _root_.Set.range ((ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι j)).Nonempty) :
    near i j = true := by
  obtain ⟨p, ⟨z, rfl⟩, w, hw⟩ := h
  exact ((ofTransitionMaps_ι_eq_iff_graph U hU near J hJ hrefl hsymm hself hinv htrans
    i j z w).mp hw.symm).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TopCat.GlueData.ofTransitionMaps_near_of_nonempty_inter_range then
    throwError "Refusing to shadow existing declaration TopCat.GlueData.ofTransitionMaps_near_of_nonempty_inter_range"
  Lean.modifyEnv fun env => Lean.addAlias env `TopCat.GlueData.ofTransitionMaps_near_of_nonempty_inter_range ``Submission.TopCat.GlueData.ofTransitionMaps_near_of_nonempty_inter_range

open _root_.TopCat _root_.TopCat.GlueData in
theorem ofTransitionMaps_mapsTo_of_subset_image (i j : ι) (h : near i j = _root_.Bool.true)
    {L : Set (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.glued}
    {W : Set E}
    (hL : L ⊆ (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι j ''
      {z : U | (z : E) ∈ W}) :
    _root_.Set.MapsTo (J ⟨(i, j), h⟩)
      (Subtype.val '' ((ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι i ⁻¹' L)) W := by
  rintro z ⟨u, hu, rfl⟩
  obtain ⟨v, hv, huv⟩ := hL hu
  obtain ⟨h', heq⟩ := (ofTransitionMaps_ι_eq_iff_graph U hU near J hJ hrefl hsymm hself hinv htrans
    i j u v).mp huv.symm
  exact heq ▸ hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TopCat.GlueData.ofTransitionMaps_mapsTo_of_subset_image then
    throwError "Refusing to shadow existing declaration TopCat.GlueData.ofTransitionMaps_mapsTo_of_subset_image"
  Lean.modifyEnv fun env => Lean.addAlias env `TopCat.GlueData.ofTransitionMaps_mapsTo_of_subset_image ``Submission.TopCat.GlueData.ofTransitionMaps_mapsTo_of_subset_image

end TopCat.GlueData

end

end

section

noncomputable section
open _root_.Set _root_.Topology _root_.Submission.Topology
universe u
namespace TopCat.GlueData
open _root_.TopCat _root_.TopCat.GlueData
variable {ι E : Type u} [TopologicalSpace E]
    (U : Set E) (hU : IsOpen U) (near : ι → ι → Bool)
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hJ : ∀ a, ContinuousOn (J a) U)
    (hrefl : ∀ i, near i i = true)
    (hsymm : ∀ i j, near i j = true → near j i = true)
    (hself : ∀ i x, x ∈ U → J ⟨(i, i), hrefl i⟩ x = x)
    (hinv : ∀ i j (h : near i j = true) x, x ∈ U → J ⟨(i, j), h⟩ x ∈ U →
      J ⟨(j, i), hsymm i j h⟩ (J ⟨(i, j), h⟩ x) = x)
    (htrans : ∀ i j k (hij : near i j = true) (hjk : near j k = true) x,
      x ∈ U → J ⟨(i, j), hij⟩ x ∈ U → J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x) ∈ U →
      ∃ hik : near i k = true,
        J ⟨(i, k), hik⟩ x = J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x))


open _root_.TopCat _root_.TopCat.GlueData in
theorem ofTransitionMaps_compact_overlap (i j : ι)
    {L : Set (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.glued}
    {Wi Wj : Set E} (hL : IsCompact L) (hLn : L.Nonempty)
    (hLi : L ⊆ (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι i ''
      {z : U | (z : E) ∈ Wi})
    (hLj : L ⊆ (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι j ''
      {z : U | (z : E) ∈ Wj}) :
    let K := Subtype.val '' ((ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι i ⁻¹' L)
    IsCompact K ∧ K ⊆ Wi ∧
      ∃ h : near i j = _root_.Bool.true, _root_.Set.MapsTo (J ⟨(i, j), h⟩) K Wj := by
  dsimp only
  let D := ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans
  have hLi' : L ⊆ _root_.Set.range (D.toGlueData.ι i) := hLi.trans (_root_.Set.image_subset_range _ _)
  have hLj' : L ⊆ _root_.Set.range (D.toGlueData.ι j) := hLj.trans (_root_.Set.image_subset_range _ _)
  have hij : near i j = true :=
    ofTransitionMaps_near_of_nonempty_inter_range U hU near J hJ hrefl hsymm hself hinv htrans
      i j (hLn.mono (_root_.Set.subset_inter hLi' hLj'))
  exact ⟨(D.ι_isOpenEmbedding i).isInducing.isCompact_image_subtype_preimage hL hLi',
    (D.ι_isOpenEmbedding i).injective.image_subtype_preimage_subset hLi,
    hij, ofTransitionMaps_mapsTo_of_subset_image U hU near J hJ hrefl hsymm hself hinv htrans i j hij hLj⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TopCat.GlueData.ofTransitionMaps_compact_overlap then
    throwError "Refusing to shadow existing declaration TopCat.GlueData.ofTransitionMaps_compact_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `TopCat.GlueData.ofTransitionMaps_compact_overlap ``Submission.TopCat.GlueData.ofTransitionMaps_compact_overlap

end TopCat.GlueData

end

end
