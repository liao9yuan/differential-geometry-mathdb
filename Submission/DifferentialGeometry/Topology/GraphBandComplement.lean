import Submission.DifferentialGeometry.Topology.GraphBand
import Submission.DifferentialGeometry.Topology.Connected.Frontier
import Submission.DifferentialGeometry.Topology.OpenPartialHomeomorph.Images
import Submission.DifferentialGeometry.Topology.OpenPartialHomeomorph.CollarUnion
import Mathlib.Topology.OpenPartialHomeomorph.Composition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set

section

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X] [TopologicalSpace Y]

theorem graphBand_image_inter_closed_of_frontier_eq_union
    (T : OpenPartialHomeomorph (X × ℝ) Y)
    (a b : X → ℝ) (ha : Continuous a) (hb : Continuous b) (hab : ∀ q, a q < b q)
    (hsource : {z : X × ℝ | a z.1 ≤ z.2 ∧ z.2 ≤ b z.1} ⊆ T.source)
    {W S : Set Y} (hW : IsClosed W)
    (hfront : frontier W =
      (_root_.Set.range (fun q => T (q, a q)) ∪ _root_.Set.range (fun q => T (q, b q))) ∪ S)
    (hdisjoint : Disjoint S
      (T '' {z : X × ℝ | a z.1 ≤ z.2 ∧ z.2 ≤ b z.1}))
    (hout : (T '' {z : X × ℝ | a z.1 < z.2 ∧ z.2 < b z.1} \ W).Nonempty) :
    (T '' {z : X × ℝ | a z.1 < z.2 ∧ z.2 < b z.1} ⊆ Wᶜ) ∧
      (T '' {z : X × ℝ | a z.1 ≤ z.2 ∧ z.2 ≤ b z.1}) ∩ W =
        range (fun q => T (q, a q)) ∪ _root_.Set.range (fun q => T (q, b q)) := by
  let A := T '' {z : X × ℝ | a z.1 < z.2 ∧ z.2 < b z.1}
  have hopen_source : {z : X × ℝ | a z.1 < z.2 ∧ z.2 < b z.1} ⊆ T.source :=
    fun z hz => hsource ⟨hz.1.le, hz.2.le⟩
  have hconn : IsPreconnected A :=
    (isPreconnected_openGraphBand a b ha hb hab).image T (T.continuousOn.mono hopen_source)
  have havoid : Disjoint A (frontier Wᶜ) := by
    rw [frontier_compl, hfront, _root_.Set.disjoint_left]
    rintro y ⟨z, hz, rfl⟩ ((⟨q, hq⟩ | ⟨q, hq⟩) | hyS)
    · have he := T.injOn (hsource ⟨le_rfl, (hab q).le⟩) (hopen_source hz) hq
      obtain rfl : q = z.1 := congrArg Prod.fst he
      exact (ne_of_lt hz.1) (congrArg Prod.snd he)
    · have he := T.injOn (hsource ⟨(hab q).le, le_rfl⟩) (hopen_source hz) hq
      obtain rfl : q = z.1 := congrArg Prod.fst he
      exact (ne_of_lt hz.2) (congrArg Prod.snd he).symm
    · exact disjoint_left.mp hdisjoint hyS ⟨z, ⟨hz.1.le, hz.2.le⟩, rfl⟩
  obtain ⟨y, hy, hyW⟩ := hout
  have hsub : A ⊆ Wᶜ :=
    (subset_interior_of_isPreconnected_of_disjoint_frontier hconn havoid
      ⟨y, hy, hW.isOpen_compl.interior_eq.symm ▸ hyW⟩).trans interior_subset
  refine ⟨hsub, ?_⟩
  apply Subset.antisymm
  · rintro y ⟨⟨z, hz, rfl⟩, hyW⟩
    rcases eq_or_lt_of_le hz.1 with hza | hza
    · exact Or.inl ⟨z.1, congrArg T (Prod.ext rfl hza)⟩
    · rcases eq_or_lt_of_le hz.2 with hzb | hzb
      · exact Or.inr ⟨z.1, congrArg T (Prod.ext rfl hzb.symm)⟩
      · exact (hsub ⟨z, ⟨hza, hzb⟩, rfl⟩ hyW).elim
  · intro y hy
    refine ⟨?_, hW.frontier_subset (hfront.symm ▸ Or.inl hy)⟩
    rcases hy with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · exact ⟨(q, a q), ⟨le_rfl, (hab q).le⟩, rfl⟩
    · exact ⟨(q, b q), ⟨(hab q).le, le_rfl⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.graphBand_image_inter_closed_of_frontier_eq_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.graphBand_image_inter_closed_of_frontier_eq_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.graphBand_image_inter_closed_of_frontier_eq_union ``Submission.DifferentialGeometry.Topology.graphBand_image_inter_closed_of_frontier_eq_union


theorem graphBand_image_inter_closed_of_frontier_eq
    (T : OpenPartialHomeomorph (X × ℝ) Y)
    (a b : X → ℝ) (ha : Continuous a) (hb : Continuous b) (hab : ∀ q, a q < b q)
    (hsource : {z : X × ℝ | a z.1 ≤ z.2 ∧ z.2 ≤ b z.1} ⊆ T.source)
    {W : Set Y} (hW : IsClosed W)
    (hfront : frontier W =
      _root_.Set.range (fun q => T (q, a q)) ∪ _root_.Set.range (fun q => T (q, b q)))
    (hout : (T '' {z : X × ℝ | a z.1 < z.2 ∧ z.2 < b z.1} \ W).Nonempty) :
    (T '' {z : X × ℝ | a z.1 < z.2 ∧ z.2 < b z.1} ⊆ Wᶜ) ∧
      (T '' {z : X × ℝ | a z.1 ≤ z.2 ∧ z.2 ≤ b z.1}) ∩ W =
        range (fun q => T (q, a q)) ∪ _root_.Set.range (fun q => T (q, b q)) := by
  apply graphBand_image_inter_closed_of_frontier_eq_union T a b ha hb hab hsource hW
    (S := ∅)
  · simpa only [_root_.Set.union_empty] using hfront
  · simp only [Set.empty_disjoint]
  · exact hout

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.graphBand_image_inter_closed_of_frontier_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.graphBand_image_inter_closed_of_frontier_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.graphBand_image_inter_closed_of_frontier_eq ``Submission.DifferentialGeometry.Topology.graphBand_image_inter_closed_of_frontier_eq

end DifferentialGeometry.Topology

end

section

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [PreconnectedSpace X]
  [TopologicalSpace Y] [T2Space Y] [PreconnectedSpace Y]

private def reverseUnitHomeomorph : (X × ℝ) ≃ₜ (X × ℝ) where
  toFun p := (p.1, 1 - p.2)
  invFun p := (p.1, 1 - p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := continuous_fst.prodMk (continuous_const.sub continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_const.sub continuous_snd)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.reverseUnitHomeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.reverseUnitHomeomorph target :: scope.openDecls } }

theorem union_cylinder_image_eq_univ_of_frontier_eq
    (A : OpenPartialHomeomorph (X × ℝ) Y)
    (hsource : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ A.source)
    {W : Set Y} (hregular : closure (interior W) = W)
    (hfront : frontier W =
      _root_.Set.range (fun q => A (q, 0)) ∪ _root_.Set.range (fun q => A (q, 1)))
    (hinter : (A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∩ W = frontier W)
    (hne : (W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)).Nonempty) :
    W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = univ := by
  let B := A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)
  let F₀ := _root_.Set.range (fun q : X => A (q, 0))
  let F₁ := _root_.Set.range (fun q : X => A (q, 1))
  have hW : IsClosed W := hregular ▸ isClosed_closure
  have hface (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
      A '' (_root_.Set.univ ×ˢ ({t} : Set ℝ)) = _root_.Set.range (fun q : X => A (q, t)) := by
    ext y
    constructor
    · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
      have : s = t := hs
      subst s
      exact ⟨q, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(q, t), ⟨mem_univ _, rfl⟩, rfl⟩
  have hFclosed (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
      IsClosed (_root_.Set.range (fun q : X => A (q, t))) := by
    apply IsCompact.isClosed
    apply isCompact_range
    exact A.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
      (fun q => hsource ⟨mem_univ _, ht⟩)
  have hdisjoint : Disjoint F₀ F₁ := by
    rw [_root_.Set.disjoint_left]
    rintro y ⟨q, rfl⟩ ⟨r, hr⟩
    have he := A.injOn (hsource ⟨mem_univ _, by norm_num⟩)
      (hsource ⟨mem_univ _, by norm_num⟩) hr
    have hh := congrArg Prod.snd he
    norm_num at hh
  have hdis : Disjoint (interior B) (interior W) := by
    rw [_root_.Set.disjoint_left]
    intro x hxB hxW
    have hxF := hinter ▸ (show x ∈ B ∩ W from ⟨interior_subset hxB, interior_subset hxW⟩)
    exact hxF.2 hxW
  have hFsub₀ : F₀ ⊆ W := fun x hx => hW.frontier_subset (hfront.symm ▸ Or.inl hx)
  have hFsub₁ : F₁ ⊆ W := fun x hx => hW.frontier_subset (hfront.symm ▸ Or.inr hx)
  have hupper : F₁ ⊆ interior (B ∪ W) := by
    have h := A.image_upper_boundary_subset_interior_union (by norm_num : (0 : ℝ) < 1)
      hsource hregular (hFclosed 0 (by norm_num)) hdis
      (by simpa only [hface 1 (by norm_num)] using hFsub₁)
      (by rw [hfront]; simpa only [hface 1 (by norm_num), _root_.Set.union_comm] using
        (subset_refl (F₀ ∪ F₁)))
      (by simpa only [hface 1 (by norm_num)] using hdisjoint.symm)
    simpa only [hface 1 (by norm_num)] using h
  let R : OpenPartialHomeomorph (X × ℝ) Y :=
    OpenPartialHomeomorph.trans
      (reverseUnitHomeomorph (X := X)).toOpenPartialHomeomorph A
  have hR (q : X) (t : ℝ) : R (q, t) = A (q, 1 - t) := rfl
  have hRsource : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ R.source := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    apply hsource
    change True ∧ 0 ≤ 1 - z.2 ∧ 1 - z.2 ≤ 1
    exact ⟨trivial, by linarith [hz.2.2], by linarith [hz.2.1]⟩
  have hRB : R '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = B := by
    ext y
    constructor
    · rintro ⟨⟨q, t⟩, ht, rfl⟩
      exact ⟨(q, 1 - t), ⟨mem_univ _, by constructor <;> linarith [ht.2.1, ht.2.2]⟩, rfl⟩
    · rintro ⟨⟨q, t⟩, ht, rfl⟩
      refine ⟨(q, 1 - t), ⟨mem_univ _, by constructor <;> linarith [ht.2.1, ht.2.2]⟩, ?_⟩
      rw [hR]
      simp
  have hRface : R '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) = F₀ := by
    ext y
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have : t = 1 := ht
      subst t
      exact ⟨q, by simp [hR]⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 1), ⟨mem_univ _, rfl⟩, by simp [hR]⟩
  have hlower : F₀ ⊆ interior (B ∪ W) := by
    have h := R.image_upper_boundary_subset_interior_union (by norm_num : (0 : ℝ) < 1)
      hRsource hregular (hFclosed 1 (by norm_num)) (hRB.symm ▸ hdis)
      (hRface.symm ▸ hFsub₀)
      (by rw [hRface, hfront]) (hRface.symm ▸ hdisjoint)
    simpa only [hRface, hRB] using h
  have hBclosed : IsClosed B :=
    ((isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc).image_of_continuousOn
      (A.continuousOn.mono hsource)).isClosed
  have hBfront : frontier B = F₀ ∪ F₁ := by
    rw [← A.image_frontier_of_subset_source hsource
      (isClosed_univ.prod isClosed_Icc) hBclosed,
      frontier_univ_prod_eq, frontier_Icc zero_le_one,
      show ({0, 1} : Set ℝ) = {0} ∪ {1} from rfl, _root_.Set.prod_union, _root_.Set.image_union,
      hface 0 (by norm_num), hface 1 (by norm_num)]
  have hf : frontier (W ∪ B) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxF : x ∈ F₀ ∪ F₁ := by
      rcases frontier_union_subset W B hx with h | h
      · exact hfront ▸ h.1
      · exact hBfront ▸ h.2
    have hi := hxF.elim (fun h => hlower h) (fun h => hupper h)
    rw [_root_.Set.union_comm B W] at hi
    exact hx.2 hi
  exact (isClopen_iff_frontier_eq_empty.mpr hf).eq_univ hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.union_cylinder_image_eq_univ_of_frontier_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.union_cylinder_image_eq_univ_of_frontier_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.union_cylinder_image_eq_univ_of_frontier_eq ``Submission.DifferentialGeometry.Topology.union_cylinder_image_eq_univ_of_frontier_eq

end DifferentialGeometry.Topology

end
