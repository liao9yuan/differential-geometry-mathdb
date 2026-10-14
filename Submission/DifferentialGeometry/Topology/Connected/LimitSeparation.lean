/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.Connected.Separation
import Mathlib.Topology.Compactness.LocallyFinite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

omit [TopologicalSpace X] in
private theorem eventually_mem_iff_of_locally_eventually_constant
    {C : ℕ → Set X} {U : Set X} {N : ℕ}
    (h : ∀ n ≥ N, ∀ y ∈ U, (y ∈ C n ↔ y ∈ C N)) {y : X} (hy : y ∈ U) :
    (∀ᶠ n : ℕ in _root_.Filter.atTop, y ∈ C n) ↔ y ∈ C N := by
  constructor
  · intro hyC
    obtain ⟨n, hyn, hn⟩ := (hyC.and (_root_.Filter.eventually_ge_atTop N)).exists
    exact (h n hn y hy).mp hyn
  · intro hyC
    filter_upwards [_root_.Filter.eventually_ge_atTop N] with n hn
    exact (h n hn y hy).mpr hyC

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.eventually_mem_iff_of_locally_eventually_constant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.eventually_mem_iff_of_locally_eventually_constant target :: scope.openDecls } }

theorem exists_isClosed_separating_limit_of_locally_eventually_constant
    [LocallyConnectedSpace X]
    (hopenPath : ∀ U : Set X, IsOpen U → IsConnected U → IsPathConnected U)
    (C : ℕ → Set X) {Z H T : Set X} (hC : ∀ n, IsClosed (C n))
    (hZ : IsClosed Z) (hZC : ∀ n, Z ⊆ C n)
    (hstable : ∀ x ∈ Zᶜ, ∃ U ∈ 𝓝 x, ∃ N,
      ∀ n ≥ N, ∀ y ∈ U, (y ∈ C n ↔ y ∈ C N))
    (hH : IsPreconnected H) (hT : IsPreconnected T)
    (hsep : ∀ n, Separates (C n) H T) :
    ∃ Clim : Set X,
      IsClosed Clim ∧ Z ⊆ Clim ∧
      (∀ B : Set X, IsCompact B → B ⊆ Zᶜ →
        ∀ᶠ n : ℕ in _root_.Filter.atTop, C n ∩ B = Clim ∩ B) ∧
      Separates Clim H T := by
  let Clim : Set X := Z ∪ {x | ∀ᶠ n : ℕ in _root_.Filter.atTop, x ∈ C n}
  have hZlim : Z ⊆ Clim := fun _ hx => Or.inl hx
  have hlocal (x : X) (hx : x ∈ Zᶜ) :
      ∀ᶠ p : ℕ × X in _root_.Filter.atTop ×ˢ 𝓝 x, (p.2 ∈ C p.1 ↔ p.2 ∈ Clim) := by
    obtain ⟨U, hU, N, hN⟩ := hstable x hx
    have hZnhds : Zᶜ ∈ 𝓝 x := hZ.isOpen_compl.mem_nhds hx
    filter_upwards [(_root_.Filter.eventually_ge_atTop N).prod_mk (_root_.Filter.inter_mem hU hZnhds)] with p hp
    have hpN : N ≤ p.1 := hp.1
    have hpU : p.2 ∈ U := hp.2.1
    have hpZ : p.2 ∈ Zᶜ := hp.2.2
    have hconst : (∀ᶠ n : ℕ in _root_.Filter.atTop, p.2 ∈ C n) ↔ p.2 ∈ C N :=
      eventually_mem_iff_of_locally_eventually_constant hN hpU
    have hpnotZ : p.2 ∉ Z := hpZ
    simp only [Clim, _root_.Set.mem_union, _root_.Set.mem_ofPred_eq, hpnotZ, false_or]
    exact (hN p.1 hpN p.2 hpU).trans hconst.symm
  have hClim : IsClosed Clim := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hxZ : x ∈ Zᶜ := fun hxZ => hx (hZlim hxZ)
    obtain ⟨n, hn⟩ := (hlocal x hxZ).curry.exists
    have hxCn : x ∉ C n := by
      intro hxCn
      exact hx ((hn.self_of_nhds).mp hxCn)
    filter_upwards [hn, (hC n).isOpen_compl.mem_nhds hxCn] with y hy hny
    exact fun hylim => hny (hy.mpr hylim)
  have hcompact (B : Set X) (hB : IsCompact B) (hBZ : B ⊆ Zᶜ) :
      ∀ᶠ n : ℕ in _root_.Filter.atTop, C n ∩ B = Clim ∩ B := by
    have hprod : ∀ᶠ p : ℕ × X in _root_.Filter.atTop ×ˢ 𝓝ˢ B,
        (p.2 ∈ C p.1 ↔ p.2 ∈ Clim) :=
      hB.mem_prod_nhdsSet_of_forall fun x hx => hlocal x (hBZ hx)
    filter_upwards [hprod.curry] with n hn
    ext y
    simp only [_root_.Set.mem_inter_iff]
    constructor
    · rintro ⟨hyC, hyB⟩
      exact ⟨(hn.self_of_nhdsSet y hyB).mp hyC, hyB⟩
    · rintro ⟨hylim, hyB⟩
      exact ⟨(hn.self_of_nhdsSet y hyB).mpr hylim, hyB⟩
  have hHlim : H ⊆ Climᶜ := by
    intro x hxH hxlim
    rcases hxlim with hxZ | hxeventual
    · exact (hsep 0).left_subset_compl hxH (hZC 0 hxZ)
    · obtain ⟨n, hxn⟩ := hxeventual.exists
      exact (hsep n).left_subset_compl hxH hxn
  have hTlim : T ⊆ Climᶜ := by
    intro x hxT hxlim
    rcases hxlim with hxZ | hxeventual
    · exact (hsep 0).right_subset_compl hxT (hZC 0 hxZ)
    · obtain ⟨n, hxn⟩ := hxeventual.exists
      exact (hsep n).right_subset_compl hxT hxn
  have hseplim : Separates Clim H T := by
    by_cases hHne : H.Nonempty
    · by_cases hTne : T.Nonempty
      · obtain ⟨x, hx⟩ := hHne
        obtain ⟨y, hy⟩ := hTne
        by_contra hnot
        have hjoined := joinedIn_compl_of_not_separates hopenPath hClim hH hT hHlim hTlim
          hnot hx hy
        let B : Set X := _root_.Set.range hjoined.somePath
        have hB : IsCompact B := isCompact_range hjoined.somePath.continuous
        have hBZ : B ⊆ Zᶜ := by
          intro z hz hzZ
          obtain ⟨t, rfl⟩ := hz
          exact hjoined.somePath_mem t (hZlim hzZ)
        obtain ⟨n, hn⟩ := (hcompact B hB hBZ).exists
        have hjoined' : JoinedIn (C n)ᶜ x y := by
          refine ⟨hjoined.somePath, fun t ht => ?_⟩
          have htB : hjoined.somePath t ∈ B := _root_.Set.mem_range_self t
          have htlim : hjoined.somePath t ∈ Clim :=
            (show hjoined.somePath t ∈ Clim ∩ B from hn ▸ ⟨ht, htB⟩).1
          exact hjoined.somePath_mem t htlim
        have hconnected := (isConnected_range hjoined'.somePath.continuous).isPreconnected
        have hcomponent := hconnected.subset_connectedComponentIn
            ⟨0, hjoined'.somePath.source⟩
            (range_subset_iff.mpr hjoined'.somePath_mem)
            ⟨1, hjoined'.somePath.target⟩
        exact (hsep n).not_mem_connectedComponentIn hx hy hcomponent
      · rw [not_nonempty_iff_eq_empty.mp hTne]
        exact (separates_empty_left hClim hHlim).symm
    · rw [not_nonempty_iff_eq_empty.mp hHne]
      exact separates_empty_left hClim hTlim
  exact ⟨Clim, hClim, hZlim, hcompact, hseplim⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_isClosed_separating_limit_of_locally_eventually_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_isClosed_separating_limit_of_locally_eventually_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_isClosed_separating_limit_of_locally_eventually_constant ``Submission.DifferentialGeometry.Topology.exists_isClosed_separating_limit_of_locally_eventually_constant

theorem exists_isClosed_separating_limit_of_locallyFinite_supports
    [LocallyConnectedSpace X]
    (hopenPath : ∀ U : Set X, IsOpen U → IsConnected U → IsPathConnected U)
    (C S : ℕ → Set X) {Z H T : Set X} (hC : ∀ n, IsClosed (C n))
    (hZ : IsClosed Z) (hZC : ∀ n, Z ⊆ C n)
    (hSloc : LocallyFinite fun n =>
      (Subtype.val : ↥(Zᶜ) → X) ⁻¹' S n)
    (hchange : ∀ n, {x | (x ∈ C (n + 1)) ≠ (x ∈ C n)} ⊆ S n)
    (hH : IsPreconnected H) (hT : IsPreconnected T)
    (hsep : ∀ n, Separates (C n) H T) :
    ∃ Clim : Set X,
      IsClosed Clim ∧ Z ⊆ Clim ∧
      (∀ B : Set X, IsCompact B → B ⊆ Zᶜ →
        ∀ᶠ n : ℕ in _root_.Filter.atTop, C n ∩ B = Clim ∩ B) ∧
      Separates Clim H T := by
  let f : ℕ → ↥(Zᶜ) → Prop := fun n x => (x : X) ∈ C n
  have hfloc : LocallyFinite fun n => {x | f (n + 1) x ≠ f n x} := by
    apply hSloc.subset
    intro n x hx
    exact hchange n hx
  obtain ⟨F, hF⟩ := hfloc.exists_forall_eventually_eq_prod
  have hstable : ∀ x ∈ Zᶜ, ∃ U ∈ 𝓝 x, ∃ N,
      ∀ n ≥ N, ∀ y ∈ U, (y ∈ C n ↔ y ∈ C N) := by
    intro x hx
    let x' : ↥(Zᶜ) := ⟨x, hx⟩
    obtain ⟨A, hA, V, hV, hAV⟩ := Filter.mem_prod_iff.mp (hF x')
    obtain ⟨N, hN⟩ := mem_atTop_sets.mp hA
    obtain ⟨U, hU, hUV⟩ := (mem_nhds_subtype Zᶜ x' V).mp hV
    refine ⟨U, hU, N, fun n hn y hy => ?_⟩
    by_cases hyZ : y ∈ Z
    · exact iff_of_true (hZC n hyZ) (hZC N hyZ)
    · let y' : ↥(Zᶜ) := ⟨y, hyZ⟩
      have hyV : y' ∈ V := hUV hy
      have hny : (n, y') ∈ A ×ˢ V := ⟨hN n hn, hyV⟩
      have hNy : (N, y') ∈ A ×ˢ V := ⟨hN N le_rfl, hyV⟩
      have hnF := hAV hny
      have hNF := hAV hNy
      change f n y' ↔ f N y'
      rw [hnF, hNF]
  exact exists_isClosed_separating_limit_of_locally_eventually_constant
    hopenPath C hC hZ hZC hstable hH hT hsep

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_isClosed_separating_limit_of_locallyFinite_supports then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_isClosed_separating_limit_of_locallyFinite_supports"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_isClosed_separating_limit_of_locallyFinite_supports ``Submission.DifferentialGeometry.Topology.exists_isClosed_separating_limit_of_locallyFinite_supports

end DifferentialGeometry.Topology
