import Submission.DifferentialGeometry.Topology.SphereSeparation.BicollarCompactBand
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

theorem connectedComponentIn_compl_frontier_eq
    {M : Type*} [TopologicalSpace M] {D : Set M}
    (hD : IsConnected D) (hDopen : IsOpen D) {x : M} (hx : x ∈ D) :
    connectedComponentIn (frontier D)ᶜ x = D := by
  have hDavoid : D ⊆ (frontier D)ᶜ := by
    intro q hq hqfr
    exact hqfr.2 (hDopen.interior_eq.symm ▸ hq)
  have hsub : D ⊆ connectedComponentIn (frontier D)ᶜ x :=
    hD.isPreconnected.subset_connectedComponentIn hx hDavoid
  apply Subset.antisymm ?_ hsub
  apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hDopen
  · exact ⟨x, mem_connectedComponentIn (hDavoid hx), hx⟩
  · rintro q ⟨hqcl, hqcomp⟩
    by_contra hqnot
    have hqfr : q ∈ frontier D := by
      rw [frontier, hDopen.interior_eq]
      exact ⟨hqcl, hqnot⟩
    exact connectedComponentIn_subset (frontier D)ᶜ x hqcomp hqfr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.connectedComponentIn_compl_frontier_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.connectedComponentIn_compl_frontier_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.connectedComponentIn_compl_frontier_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.connectedComponentIn_compl_frontier_eq

theorem bicollar_band_extends_compact_side
    {A M : Type*} [TopologicalSpace A] [CompactSpace A] [ConnectedSpace A]
    [TopologicalSpace M] [T2Space M]
    (φ : A × ℝ → M) (hφ : _root_.Topology.IsOpenEmbedding φ)
    {s t : ℝ} (hst : s < t) (B : Set M)
    (hBconn : IsConnected B) (hBopen : IsOpen B) (hBc : IsCompact (closure B))
    (hBclosure : closure B = B ∪ _root_.Set.range (fun y => φ (y, s)))
    (hnegative : ∀ y z, z < s → φ (y, z) ∈ B)
    (hpositive : ∀ y z, s < z → φ (y, z) ∉ B) :
    let D := B ∪ φ '' ((_root_.Set.univ : Set A) ×ˢ _root_.Set.Iio t)
    IsConnected D ∧ IsOpen D ∧ IsCompact (closure D) ∧
      closure D = closure B ∪ φ '' ((_root_.Set.univ : Set A) ×ˢ _root_.Set.Icc s t) ∧
      closure B ⊆ D ∧ frontier D = _root_.Set.range (fun y => φ (y, t)) := by
  classical
  let Ht : Set M := φ '' ((_root_.Set.univ : Set A) ×ˢ _root_.Set.Iio t)
  let D : Set M := B ∪ Ht
  let L : Set M := closure B ∪ φ '' ((_root_.Set.univ : Set A) ×ˢ _root_.Set.Icc s t)
  have hHtopen : IsOpen Ht := hφ.isOpenMap _ (isOpen_univ.prod isOpen_Iio)
  have hDopen : IsOpen D := hBopen.union hHtopen
  have hHtconn : IsConnected Ht :=
    (isConnected_univ.prod isConnected_Iio).image φ hφ.continuous.continuousOn
  let a : A := Classical.arbitrary A
  have hDconn : IsConnected D := hBconn.union
    ⟨φ (a, s - 1), hnegative a (s - 1) (by linarith),
      ⟨(a, s - 1), ⟨mem_univ _, by change s - 1 < t; linarith⟩, rfl⟩⟩ hHtconn
  have hLc : IsCompact L := hBc.union (bicollar_band_compact_connected φ hφ hst.le).1
  have hBclsub : closure B ⊆ D := by
    rw [hBclosure]
    rintro q (hqB | ⟨y, rfl⟩)
    · exact Or.inl hqB
    · exact Or.inr ⟨(y, s), ⟨mem_univ _, hst⟩, rfl⟩
  have hDsubL : D ⊆ L := by
    rintro q (hqB | ⟨⟨y, z⟩, ⟨_, hz⟩, rfl⟩)
    · exact Or.inl (subset_closure hqB)
    · by_cases hzs : z < s
      · exact Or.inl (subset_closure (hnegative y z hzs))
      · exact Or.inr ⟨(y, z), ⟨mem_univ _, le_of_not_gt hzs, hz.le⟩, rfl⟩
  have hhalfClosure : φ '' ((_root_.Set.univ : Set A) ×ˢ _root_.Set.Iic t) ⊆ closure Ht := by
    have hc := image_closure_subset_closure_image hφ.continuous
      (s := (_root_.Set.univ : Set A) ×ˢ _root_.Set.Iio t)
    rw [closure_prod_eq, closure_univ, closure_Iio] at hc
    exact hc
  have hLsubDcl : L ⊆ closure D := by
    apply _root_.Set.union_subset (closure_mono _root_.Set.subset_union_left)
    intro q hq
    apply closure_mono (_root_.Set.subset_union_right : Ht ⊆ D)
    apply hhalfClosure
    obtain ⟨⟨y, z⟩, ⟨_, _hzlo, hzhi⟩, rfl⟩ := hq
    exact ⟨(y, z), ⟨mem_univ _, hzhi⟩, rfl⟩
  have hDclosure : closure D = L :=
    Subset.antisymm (closure_minimal hDsubL hLc.isClosed) hLsubDcl
  have hDavoid (y : A) : φ (y, t) ∉ D := by
    rintro (hyB | ⟨⟨y', z⟩, ⟨_, hz⟩, heq⟩)
    · exact hpositive y t hst hyB
    · have hzt := congrArg Prod.snd (hφ.injective heq)
      change z = t at hzt
      exact (ne_of_lt hz) hzt
  have hfront : frontier D = _root_.Set.range (fun y => φ (y, t)) := by
    rw [frontier, hDclosure, hDopen.interior_eq]
    ext q
    constructor
    · rintro ⟨hqL, hqnot⟩
      rcases hqL with hqB | ⟨⟨y, z⟩, ⟨_, _hzlo, hzhi⟩, rfl⟩
      · exact False.elim (hqnot (hBclsub hqB))
      · have hzt : z = t := by
          apply le_antisymm hzhi
          apply le_of_not_gt
          intro hzt
          exact hqnot (Or.inr ⟨(y, z), ⟨mem_univ _, hzt⟩, rfl⟩)
        exact ⟨y, by rw [hzt]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨Or.inr ⟨(y, t), ⟨mem_univ _, hst.le, le_rfl⟩, rfl⟩, hDavoid y⟩
  refine ⟨hDconn, hDopen, ?_, hDclosure, hBclsub, hfront⟩
  rw [hDclosure]
  exact hLc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_band_extends_compact_side then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_band_extends_compact_side"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_band_extends_compact_side ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bicollar_band_extends_compact_side

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
