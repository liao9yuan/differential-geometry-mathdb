import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Submission.DifferentialGeometry.Topology.SphereSeparation.HalfSpaceClosure
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private def absAxialCoordinate : CylinderDiagonalQuotient → ℝ :=
  Quotient.lift (fun p : S × ℝ => |p.2|) (by
    intro p q h
    rcases h with h | h
    · rw [h]
    · rw [h]
      exact (abs_neg p.2).symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.absAxialCoordinate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.absAxialCoordinate target :: scope.openDecls } }

private theorem absAxialCoordinate_proj (p : S × ℝ) :
    absAxialCoordinate (proj p) = |p.2| := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.absAxialCoordinate_proj
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.absAxialCoordinate_proj target :: scope.openDecls } }

private theorem continuous_absAxialCoordinate : Continuous absAxialCoordinate :=
  Continuous.quotient_lift continuous_snd.abs _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.continuous_absAxialCoordinate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.continuous_absAxialCoordinate target :: scope.openDecls } }

private def closedSlab (L : ℝ) : Set CylinderDiagonalQuotient :=
  {q | absAxialCoordinate q ≤ L}

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.closedSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.closedSlab target :: scope.openDecls } }

private theorem preimage_closedSlab (L : ℝ) :
    proj ⁻¹' closedSlab L = _root_.Set.univ ×ˢ _root_.Set.Icc (-L) L := by
  ext p
  simp only [closedSlab, _root_.Set.mem_preimage, _root_.Set.mem_ofPred_eq, absAxialCoordinate_proj,
    _root_.Set.mem_prod, _root_.Set.mem_univ, true_and, _root_.Set.mem_Icc, abs_le]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.preimage_closedSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.preimage_closedSlab target :: scope.openDecls } }

private theorem closedSlab_eq_image (L : ℝ) :
    closedSlab L = proj '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L) := by
  rw [← preimage_closedSlab, surjective_proj.image_preimage]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.closedSlab_eq_image
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.closedSlab_eq_image target :: scope.openDecls } }

private theorem isCompact_closedSlab (L : ℝ) : IsCompact (closedSlab L) := by
  rw [closedSlab_eq_image]
  exact (isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc).image continuous_proj

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.isCompact_closedSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.isCompact_closedSlab target :: scope.openDecls } }

private theorem preimage_interior_closedSlab (L : ℝ) :
    proj ⁻¹' interior (closedSlab L) = _root_.Set.univ ×ˢ _root_.Set.Ioo (-L) L := by
  rw [isOpenMap_proj.preimage_interior_eq_interior_preimage continuous_proj,
    preimage_closedSlab, interior_prod_eq, interior_univ, interior_Icc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.preimage_interior_closedSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.preimage_interior_closedSlab target :: scope.openDecls } }

private theorem closure_interior_closedSlab {L : ℝ} (hL : 0 < L) :
    closure (interior (closedSlab L)) = closedSlab L := by
  apply surjective_proj.preimage_injective
  rw [isOpenMap_proj.preimage_closure_eq_closure_preimage continuous_proj,
    preimage_interior_closedSlab, closure_prod_eq, closure_univ,
    closure_Ioo (by linarith : -L ≠ L), preimage_closedSlab]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.closure_interior_closedSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.closure_interior_closedSlab target :: scope.openDecls } }

private theorem preimage_frontier_closedSlab {L : ℝ} (hL : 0 ≤ L) :
    proj ⁻¹' frontier (closedSlab L) = _root_.Set.univ ×ˢ ({-L, L} : Set ℝ) := by
  rw [isOpenMap_proj.preimage_frontier_eq_frontier_preimage continuous_proj,
    preimage_closedSlab, frontier_univ_prod_eq, frontier_Icc (by linarith : -L ≤ L)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.preimage_frontier_closedSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.preimage_frontier_closedSlab target :: scope.openDecls } }

private theorem frontier_closedSlab_eq_image {L : ℝ} (hL : 0 ≤ L) :
    frontier (closedSlab L) = proj '' (_root_.Set.univ ×ˢ ({L} : Set ℝ)) := by
  ext q
  obtain ⟨⟨y,t⟩, rfl⟩ := surjective_proj q
  constructor
  · intro h
    have ht : t = -L ∨ t = L := by
      have hh : (y,t) ∈ proj ⁻¹' frontier (closedSlab L) := h
      rw [preimage_frontier_closedSlab hL] at hh
      simpa only [_root_.Set.mem_prod, _root_.Set.mem_univ, true_and, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff] using hh
    rcases ht with ht | ht
    · refine ⟨(-y,L), ⟨mem_univ _, _root_.Set.mem_singleton _⟩, ?_⟩
      rw [ht]
      exact (proj_eq_iff _ _).mpr (Or.inr (by simp))
    · exact ⟨(y,L), ⟨mem_univ _, _root_.Set.mem_singleton _⟩, by rw [ht]⟩
  · rintro ⟨⟨z,s⟩, ⟨_,hs⟩, h⟩
    have hsL : s = L := hs
    rw [← h]
    change (z,s) ∈ proj ⁻¹' frontier (closedSlab L)
    rw [preimage_frontier_closedSlab hL]
    simp [hsL]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.frontier_closedSlab_eq_image
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.frontier_closedSlab_eq_image target :: scope.openDecls } }

private theorem injOn_proj_positive : _root_.Set.InjOn proj (_root_.Set.univ ×ˢ _root_.Set.Ioi (0 : ℝ)) := by
  intro p hp q hq heq
  rcases (proj_eq_iff p q).mp heq with h | h
  · exact h.symm
  · have ht := congrArg Prod.snd h
    change q.2 = -p.2 at ht
    have hp0 : 0 < p.2 := hp.2
    have hq0 : 0 < q.2 := hq.2
    linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.injOn_proj_positive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.injOn_proj_positive target :: scope.openDecls } }

private theorem isConnected_closedSlab {L : ℝ} (hL : 0 ≤ L) :
    IsConnected (closedSlab L) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    apply Module.one_lt_rank_of_one_lt_finrank
    norm_num
  let : PreconnectedSpace S := Subtype.preconnectedSpace (isPreconnected_sphere hrank 0 1)
  let y : S := ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
  let : Nonempty S := ⟨y⟩
  let : ConnectedSpace S := ⟨⟨y⟩⟩
  rw [closedSlab_eq_image]
  exact (isConnected_univ.prod (isConnected_Icc (by linarith : -L ≤ L))).image
    proj continuous_proj.continuousOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.isConnected_closedSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.isConnected_closedSlab target :: scope.openDecls } }

private theorem exists_positive_partialDiffeomorph :
    ∃ Φ : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        (S × ℝ) CylinderDiagonalQuotient ∞,
      Φ.source = _root_.Set.univ ×ˢ _root_.Set.Ioi (0 : ℝ) ∧
      Φ.target = proj '' (_root_.Set.univ ×ˢ _root_.Set.Ioi (0 : ℝ)) ∧ (Φ : S × ℝ → CylinderDiagonalQuotient) = proj := by
  have hn : (_root_.Set.univ ×ˢ _root_.Set.Ioi (0 : ℝ) : Set (S × ℝ)).Nonempty := by
    let y : S := ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
    exact ⟨(y,1), _root_.Set.mem_univ _, by norm_num⟩
  exact IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (isLocalDiffeomorph_proj.isLocalDiffeomorphOn _) (isOpen_univ.prod isOpen_Ioi)
    hn injOn_proj_positive

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_positive_partialDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_positive_partialDiffeomorph target :: scope.openDecls } }

private theorem image_positive_Icc {a b : ℝ} (ha : 0 < a) :
    proj '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b) = {q | a ≤ absAxialCoordinate q ∧ absAxialCoordinate q ≤ b} := by
  ext q
  constructor
  · rintro ⟨⟨y,t⟩, ⟨_,ht⟩, rfl⟩
    change a ≤ |t| ∧ |t| ≤ b
    simpa only [_root_.Set.mem_Icc, abs_of_nonneg (ha.le.trans ht.1)] using ht
  · intro h
    obtain ⟨⟨y,t⟩, rfl⟩ := surjective_proj q
    change a ≤ |t| ∧ |t| ≤ b at h
    by_cases ht : 0 ≤ t
    · refine ⟨(y,t), ⟨mem_univ _, ?_⟩, rfl⟩
      simpa only [_root_.Set.mem_Icc, abs_of_nonneg ht] using h
    · refine ⟨(-y,-t), ⟨mem_univ _, ?_⟩, ?_⟩
      · simpa only [_root_.Set.mem_Icc, abs_of_neg (lt_of_not_ge ht)] using h
      · exact (proj_eq_iff _ _).mpr (Or.inr (by simp))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.image_positive_Icc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.image_positive_Icc target :: scope.openDecls } }

private theorem closedSlab_union_positive_tube {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    closedSlab a ∪ proj '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b) = closedSlab b := by
  rw [image_positive_Icc ha]
  ext q
  change (absAxialCoordinate q ≤ a ∨ (a ≤ absAxialCoordinate q ∧ absAxialCoordinate q ≤ b)) ↔
    absAxialCoordinate q ≤ b
  constructor
  · rintro (h | h)
    · exact h.trans hab
    · exact h.2
  · intro h
    rcases le_total (absAxialCoordinate q) a with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h',h⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.closedSlab_union_positive_tube
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.closedSlab_union_positive_tube target :: scope.openDecls } }

private theorem closedSlab_inter_positive_tube {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    closedSlab a ∩ proj '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b) = frontier (closedSlab a) := by
  rw [image_positive_Icc ha, frontier_closedSlab_eq_image ha.le]
  ext q
  constructor
  · rintro ⟨hcore,htube⟩
    have he : absAxialCoordinate q = a := le_antisymm hcore htube.1
    obtain ⟨⟨y,t⟩,rfl⟩ := surjective_proj q
    change |t| = a at he
    by_cases ht : 0 ≤ t
    · have ht' : t = a := (abs_of_nonneg ht).symm.trans he
      exact ⟨(y,a), ⟨mem_univ _, _root_.Set.mem_singleton _⟩, by rw [ht']⟩
    · have ht' : -t = a := (abs_of_neg (lt_of_not_ge ht)).symm.trans he
      refine ⟨(-y,a), ⟨mem_univ _, _root_.Set.mem_singleton _⟩, ?_⟩
      rw [← ht']
      exact (proj_eq_iff _ _).mpr (Or.inr (by simp))
  · rintro ⟨⟨y,t⟩, ⟨_,ht⟩, rfl⟩
    have hta : t = a := ht
    change |t| ≤ a ∧ a ≤ |t| ∧ |t| ≤ b
    rw [hta, abs_of_pos ha]
    exact ⟨le_rfl, le_rfl, hab⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.closedSlab_inter_positive_tube
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.closedSlab_inter_positive_tube target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

end

end

section
noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private theorem frontier_positive_tube {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    frontier (proj '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b)) =
      frontier (closedSlab a) ∪ frontier (closedSlab b) := by
  obtain ⟨Φ, hsource, _, hΦ⟩ := exists_positive_partialDiffeomorph
  let K : Set (S × ℝ) := _root_.Set.univ ×ˢ _root_.Set.Icc a b
  have hKsource : K ⊆ Φ.source := by
    rw [hsource]
    intro p hp
    exact ⟨mem_univ _, ha.trans_le hp.2.1⟩
  have hKclosed : IsClosed K := isClosed_univ.prod isClosed_Icc
  have hKcompact : IsCompact K := isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc
  have hImage : Φ.toOpenPartialHomeomorph.IsImage K (Φ '' K) := by
    intro x hx
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (Φ.toPartialEquiv.injOn (hKsource hy) hx hyx) ▸ hy
    · intro hxK
      exact ⟨x, hxK, rfl⟩
  have hImageClosed : IsClosed (Φ '' K) :=
    (hKcompact.image_of_continuousOn
      (Φ.contMDiffOn_toFun.continuousOn.mono hKsource)).isClosed
  have hfrontSource : frontier K ⊆ Φ.source := by
    intro p hp
    exact hKsource (hKclosed.closure_eq ▸ frontier_subset_closure hp)
  have hfrontTarget : frontier (Φ '' K) ⊆ Φ.target := by
    intro q hq
    have hqImage : q ∈ Φ '' K := hImageClosed.closure_eq ▸ frontier_subset_closure hq
    obtain ⟨p, hp, rfl⟩ := hqImage
    exact Φ.map_source' (hKsource hp)
  have hfront := hImage.frontier.image_eq
  change Φ '' (Φ.source ∩ frontier K) = Φ.target ∩ frontier (Φ '' K) at hfront
  rw [inter_eq_right.mpr hfrontSource, inter_eq_right.mpr hfrontTarget] at hfront
  have hfrontK : frontier K =
      (_root_.Set.univ ×ˢ ({a} : Set ℝ)) ∪ (_root_.Set.univ ×ˢ ({b} : Set ℝ)) := by
    dsimp only [K]
    rw [frontier_univ_prod_eq, frontier_Icc hab]
    ext p
    simp only [_root_.Set.mem_prod, _root_.Set.mem_univ, true_and, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
      _root_.Set.mem_union]
  rw [hΦ, hfrontK, _root_.Set.image_union] at hfront
  rw [frontier_closedSlab_eq_image ha.le,
    frontier_closedSlab_eq_image (ha.le.trans hab)]
  exact hfront.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.frontier_positive_tube
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.frontier_positive_tube target :: scope.openDecls } }

private theorem disjoint_frontier_closedSlab {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Disjoint (frontier (closedSlab a)) (frontier (closedSlab b)) := by
  rw [frontier_closedSlab_eq_image ha.le, frontier_closedSlab_eq_image hb.le]
  apply _root_.Set.disjoint_image_image
  intro p hp q hq heq
  have hpa : p.2 = a := hp.2
  have hqb : q.2 = b := hq.2
  have hppos : p ∈ _root_.Set.univ ×ˢ _root_.Set.Ioi (0 : ℝ) := by
    exact ⟨mem_univ _, hpa.symm ▸ ha⟩
  have hqpos : q ∈ _root_.Set.univ ×ˢ _root_.Set.Ioi (0 : ℝ) := by
    exact ⟨mem_univ _, hqb.symm ▸ hb⟩
  have hpq := injOn_proj_positive hppos hqpos heq
  exact hab (hpa.symm.trans ((congrArg Prod.snd hpq).trans hqb))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.disjoint_frontier_closedSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.disjoint_frontier_closedSlab target :: scope.openDecls } }

private theorem frontier_image_positive_tube
    {M : Type*} [TopologicalSpace M] (d : CylinderDiagonalQuotient ≃ₜ M)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    frontier (d '' (proj '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b))) =
      frontier (d '' closedSlab a) ∪ frontier (d '' closedSlab b) := by
  rw [← d.image_frontier, frontier_positive_tube ha hab, _root_.Set.image_union,
    d.image_frontier, d.image_frontier]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.frontier_image_positive_tube
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.frontier_image_positive_tube target :: scope.openDecls } }

private theorem disjoint_frontier_image_closedSlab
    {M : Type*} [TopologicalSpace M] (d : CylinderDiagonalQuotient ≃ₜ M)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Disjoint (frontier (d '' closedSlab a)) (frontier (d '' closedSlab b)) := by
  rw [← d.image_frontier, ← d.image_frontier]
  exact _root_.Set.disjoint_image_of_injective d.injective (disjoint_frontier_closedSlab ha hb hab)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.disjoint_frontier_image_closedSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.disjoint_frontier_image_closedSlab target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

end

end

section
noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private def axialBoundaryCoordinates (L : ℝ) :
    Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡 3)
      (EuclideanSpace ℝ (Fin 2) × ℝ) (EuclideanSpace ℝ (Fin 3)) ∞ where
  toEquiv := {
    toFun := fun p => NormalOrientation.positive.tangentNormalEquiv (p.1, p.2 - L)
    invFun := fun z => ((NormalOrientation.positive.tangentNormalEquiv.symm z).1,
      (NormalOrientation.positive.tangentNormalEquiv.symm z).2 + L)
    left_inv := by
      intro p
      simp only [ContinuousLinearEquiv.symm_apply_apply, sub_add_cancel]
    right_inv := by
      intro z
      change NormalOrientation.positive.tangentNormalEquiv
        ((NormalOrientation.positive.tangentNormalEquiv.symm z).1,
          (NormalOrientation.positive.tangentNormalEquiv.symm z).2 + L - L) = z
      have heq : ((NormalOrientation.positive.tangentNormalEquiv.symm z).1,
          (NormalOrientation.positive.tangentNormalEquiv.symm z).2 + L - L) =
          NormalOrientation.positive.tangentNormalEquiv.symm z := by
        apply Prod.ext
        · rfl
        · dsimp only
          ring
      rw [heq, ContinuousLinearEquiv.apply_symm_apply] }
  contMDiff_toFun := by
    exact (NormalOrientation.positive.tangentNormalEquiv.contDiff.comp
      (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))).contMDiff
  contMDiff_invFun := by
    exact ((contDiff_fst.comp NormalOrientation.positive.tangentNormalEquiv.symm.contDiff).prodMk
      ((contDiff_snd.comp NormalOrientation.positive.tangentNormalEquiv.symm.contDiff).add
        contDiff_const)).contMDiff

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.axialBoundaryCoordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.axialBoundaryCoordinates target :: scope.openDecls } }

private theorem axialBoundaryCoordinates_zero (L : ℝ) (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    axialBoundaryCoordinates L p 0 = p.2 - L := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.axialBoundaryCoordinates_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.axialBoundaryCoordinates_zero target :: scope.openDecls } }

private theorem exists_boundary_chart_at_positive_slice
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (d : Diffeomorph CI (𝓡 3) CylinderDiagonalQuotient M ∞)
    {L : ℝ} (hL : 0 < L) (z : S) :
    ∃ F : PartialDiffeomorph (𝓡 3) (𝓡 3) M (EuclideanSpace ℝ (Fin 3)) ∞,
      d (proj (z, L)) ∈ F.source ∧ (F (d (proj (z, L)))) 0 = 0 ∧
      ∀ y ∈ F.source, (y ∈ d '' closedSlab L ↔ (F y) 0 ≤ 0) := by
  obtain ⟨Φ, hsource, _, hΦ⟩ := exists_positive_partialDiffeomorph
  let Ψ := Φ.trans d.toPartialDiffeomorph
  have hΨ (p : S × ℝ) : Ψ p = d (proj p) := by
    exact congrArg d (congrFun hΦ p)
  have hbase : (z, L) ∈ Ψ.source := by
    change (z, L) ∈ Φ.source ∧ Φ (z, L) ∈ (_root_.Set.univ : Set CylinderDiagonalQuotient)
    exact ⟨hsource.symm ▸ ⟨mem_univ _, hL⟩, _root_.Set.mem_univ _⟩
  have htarget : d (proj (z, L)) ∈ Ψ.target := by
    rw [← hΨ]
    exact Ψ.map_source' hbase
  have hinverse : Ψ.symm (d (proj (z, L))) = (z, L) := by
    rw [← hΨ]
    exact Ψ.left_inv' hbase
  let χ : PartialDiffeomorph CI 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
      (S × ℝ) (EuclideanSpace ℝ (Fin 2) × ℝ) ∞ :=
    DifferentialGeometry.Topology.PartialDiffeomorph.extendedChart (I := CI) (z, L)
  have hχ : (z, L) ∈ χ.source := by
    exact mem_extChartAt_source (z, L)
  let F : PartialDiffeomorph (𝓡 3) (𝓡 3) M (EuclideanSpace ℝ (Fin 3)) ∞ :=
    (Ψ.symm.trans χ).trans (axialBoundaryCoordinates L).toPartialDiffeomorph
  have hcoord (y : M) : (F y) 0 = (Ψ.symm y).2 - L := by
    change axialBoundaryCoordinates L (χ (Ψ.symm y)) 0 = _
    rw [axialBoundaryCoordinates_zero]
    change (extChartAt CI (z, L) (Ψ.symm y)).2 - L = _
    rw [extChartAt_prod]
    rfl
  refine ⟨F, ?_, ?_, ?_⟩
  · change (d (proj (z, L)) ∈ Ψ.target ∧ Ψ.symm (d (proj (z, L))) ∈ χ.source) ∧ True
    exact ⟨⟨htarget, by simpa only [hinverse] using hχ⟩, trivial⟩
  · rw [hcoord, hinverse]
    exact sub_self L
  · intro y hy
    change (y ∈ Ψ.target ∧ Ψ.symm y ∈ χ.source) ∧ True at hy
    have hqsource : Ψ.symm y ∈ Ψ.source := Ψ.map_target' hy.1.1
    have hpositive : 0 < (Ψ.symm y).2 := by
      change Ψ.symm y ∈ Φ.source ∧ Φ (Ψ.symm y) ∈ (_root_.Set.univ : Set CylinderDiagonalQuotient)
        at hqsource
      have hq := hqsource.1
      rw [hsource] at hq
      exact hq.2
    have hqy : d (proj (Ψ.symm y)) = y :=
      (hΨ (Ψ.symm y)).symm.trans (Ψ.right_inv' hy.1.1)
    rw [hcoord, sub_nonpos]
    constructor
    · rintro ⟨q, hq, hdq⟩
      have heq : q = proj (Ψ.symm y) := d.injective (hdq.trans hqy.symm)
      rw [heq] at hq
      change |(Ψ.symm y).2| ≤ L at hq
      rwa [abs_of_pos hpositive] at hq
    · intro hq
      refine ⟨proj (Ψ.symm y), ?_, hqy⟩
      change |(Ψ.symm y).2| ≤ L
      rwa [abs_of_pos hpositive]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_boundary_chart_at_positive_slice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_boundary_chart_at_positive_slice target :: scope.openDecls } }

private theorem exists_boundary_chart_closedSlab_image
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (d : Diffeomorph CI (𝓡 3) CylinderDiagonalQuotient M ∞)
    {L : ℝ} (hL : 0 < L) (x : M) (hx : x ∈ frontier (d '' closedSlab L)) :
    ∃ F : PartialDiffeomorph (𝓡 3) (𝓡 3) M (EuclideanSpace ℝ (Fin 3)) ∞,
      x ∈ F.source ∧ (F x) 0 = 0 ∧
      ∀ y ∈ F.source, (y ∈ d '' closedSlab L ↔ (F y) 0 ≤ 0) := by
  change x ∈ frontier (d.toHomeomorph '' closedSlab L) at hx
  rw [← d.toHomeomorph.image_frontier, frontier_closedSlab_eq_image hL.le] at hx
  rcases hx with ⟨q, ⟨⟨z, t⟩, ⟨_, ht⟩, hq⟩, rfl⟩
  have htL : t = L := ht
  subst t
  rw [← hq]
  exact exists_boundary_chart_at_positive_slice d hL z

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_boundary_chart_closedSlab_image
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_boundary_chart_closedSlab_image target :: scope.openDecls } }


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

end

end

section
noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private def intervalAffineDiffeomorph (L R : ℝ) (h : L < R) : ℝ ≃ₘ[ℝ] ℝ where
  toEquiv := {
    toFun := fun s => L + (R - L) * s
    invFun := fun t => (t - L) / (R - L)
    left_inv := by
      intro s
      dsimp only
      field_simp [sub_ne_zero.mpr h.ne']
      ring
    right_inv := by
      intro t
      dsimp only
      field_simp [sub_ne_zero.mpr h.ne']
      ring }
  contMDiff_toFun := (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff
  contMDiff_invFun := ((contDiff_id.sub contDiff_const).div_const (R - L)).contMDiff

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.intervalAffineDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.intervalAffineDiffeomorph target :: scope.openDecls } }

private theorem intervalAffineDiffeomorph_image_Icc (L R : ℝ) (h : L < R) :
    (intervalAffineDiffeomorph L R h) '' _root_.Set.Icc (0 : ℝ) 1 = _root_.Set.Icc L R := by
  have hRL : 0 < R - L := sub_pos.mpr h
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    change L ≤ L + (R - L) * s ∧ L + (R - L) * s ≤ R
    constructor <;> nlinarith [hs.1, hs.2]
  · intro ht
    refine ⟨(t - L) / (R - L), ?_, ?_⟩
    · constructor
      · exact div_nonneg (sub_nonneg.mpr ht.1) hRL.le
      · exact (div_le_one hRL).2 (by linarith [ht.2])
    · change L + (R - L) * ((t - L) / (R - L)) = t
      field_simp [hRL.ne']
      ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.intervalAffineDiffeomorph_image_Icc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.intervalAffineDiffeomorph_image_Icc target :: scope.openDecls } }

private theorem exists_normalized_slab_collar
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (d : CylinderDiagonalQuotient ≃ₘ⟮CI, 𝓡 3⟯ M)
    {L R : ℝ} (hL : 0 < L) (hLR : L < R) :
    ∃ tube : PartialDiffeomorph CI (𝓡 3) (S × ℝ) M ∞,
      (∀ p, tube p = d (proj (p.1, L + (R - L) * p.2))) ∧
      _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ tube.source ∧
      tube '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = d '' (proj '' (_root_.Set.univ ×ˢ _root_.Set.Icc L R)) ∧
      tube '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) = frontier (d '' closedSlab L) ∧
      tube '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) = frontier (d '' closedSlab R) ∧
      d '' closedSlab L ∪ tube '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = d '' closedSlab R ∧
      d '' closedSlab L ∩ tube '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
        frontier (d '' closedSlab L) := by
  obtain ⟨Φ, hsource, _, hΦ⟩ := exists_positive_partialDiffeomorph
  let A : (S × ℝ) ≃ₘ⟮CI, CI⟯ (S × ℝ) :=
    (Diffeomorph.refl (𝓡 2) S ∞).prodCongr (intervalAffineDiffeomorph L R hLR)
  let tube := A.toPartialDiffeomorph.trans (Φ.trans d.toPartialDiffeomorph)
  have htube (p : S × ℝ) : tube p = d (proj (p.1, L + (R - L) * p.2)) := by
    exact congrArg d (congrFun hΦ (A p))
  have hdomain : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ tube.source := by
    intro p hp
    change p ∈ (_root_.Set.univ : Set (S × ℝ)) ∧
      A p ∈ Φ.source ∧ Φ (A p) ∈ (_root_.Set.univ : Set CylinderDiagonalQuotient)
    refine ⟨mem_univ _, ?_, _root_.Set.mem_univ _⟩
    rw [hsource]
    refine ⟨mem_univ _, ?_⟩
    change 0 < L + (R - L) * p.2
    have hprod : 0 ≤ (R - L) * p.2 := mul_nonneg (sub_pos.mpr hLR).le hp.2.1
    linarith
  have hAimage : A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = _root_.Set.univ ×ˢ _root_.Set.Icc L R := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨mem_univ _, ?_⟩
      rw [← intervalAffineDiffeomorph_image_Icc L R hLR]
      exact ⟨q.2, hq.2, rfl⟩
    · intro hp
      obtain ⟨s, hs, hsp⟩ := (intervalAffineDiffeomorph_image_Icc L R hLR).symm ▸ hp.2
      exact ⟨(p.1, s), ⟨mem_univ _, hs⟩, Prod.ext rfl hsp⟩
  have himage : tube '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      d '' (proj '' (_root_.Set.univ ×ˢ _root_.Set.Icc L R)) := by
    rw [← hAimage, _root_.Set.image_image, _root_.Set.image_image]
    apply _root_.Set.image_congr
    intro p _
    exact htube p
  have hslices (a : ℝ) : tube '' (_root_.Set.univ ×ˢ ({a} : Set ℝ)) =
      d '' (proj '' (_root_.Set.univ ×ˢ ({L + (R - L) * a} : Set ℝ))) := by
    ext y
    constructor
    · rintro ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
      have hsa : s = a := hs
      exact ⟨proj (z, L + (R - L) * a),
        ⟨(z, L + (R - L) * a), ⟨mem_univ _, rfl⟩, rfl⟩,
        by rw [htube, hsa]⟩
    · rintro ⟨q, ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩, rfl⟩
      have hsa : s = L + (R - L) * a := hs
      exact ⟨(z, a), ⟨mem_univ _, rfl⟩, by rw [htube, hsa]⟩
  have hfront (a : ℝ) (ha : 0 ≤ a) :
      frontier (d '' closedSlab a) = d '' (proj '' (_root_.Set.univ ×ˢ ({a} : Set ℝ))) := by
    change frontier (d.toHomeomorph '' closedSlab a) = _
    rw [← d.toHomeomorph.image_frontier, frontier_closedSlab_eq_image ha]
    rfl
  refine ⟨tube, htube, hdomain, himage, ?_, ?_, ?_, ?_⟩
  · rw [hfront L hL.le, hslices]
    simp only [_root_.MulZeroClass.mul_zero, add_zero]
  · rw [hfront R (hL.trans hLR).le, hslices]
    rw [mul_one, show L + (R - L) = R by ring]
  · rw [himage, ← _root_.Set.image_union, closedSlab_union_positive_tube hL hLR.le]
  · rw [himage]
    have hinj : Function.Injective (d : CylinderDiagonalQuotient → M) := d.injective
    rw [← _root_.Set.image_inter hinj, closedSlab_inter_positive_tube hL hLR.le]
    exact d.toHomeomorph.image_frontier _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_normalized_slab_collar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_normalized_slab_collar target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

end

end
