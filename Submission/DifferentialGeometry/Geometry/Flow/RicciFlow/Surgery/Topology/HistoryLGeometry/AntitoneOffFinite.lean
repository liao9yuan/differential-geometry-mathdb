import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

private theorem le_of_deriv_nonpos_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ _root_.Set.Ioo a b, ∃ d ≤ 0, HasDerivAt f d x)
    (ha : ContinuousWithinAt f (_root_.Set.Ici a) a) (hb : ContinuousWithinAt f (_root_.Set.Iic b) b) :
    f b ≤ f a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  have hcont : ContinuousOn f (_root_.Set.Icc a b) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hxa
    · exact ha.mono _root_.Set.Icc_subset_Ici_self
    rcases eq_or_lt_of_le hx.2 with rfl | hxb
    · exact hb.mono _root_.Set.Icc_subset_Iic_self
    obtain ⟨d, -, hdx⟩ := hd x ⟨hxa, hxb⟩
    exact hdx.continuousAt.continuousWithinAt
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont (fun x hx => by
    rw [interior_Icc] at hx
    obtain ⟨d, -, hdx⟩ := hd x hx
    exact hdx.differentiableAt.differentiableWithinAt) (fun x hx => by
    rw [interior_Icc] at hx
    obtain ⟨d, hd0, hdx⟩ := hd x hx
    rw [hdx.deriv]
    exact hd0)
  exact hanti (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.le_of_deriv_nonpos_Icc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.le_of_deriv_nonpos_Icc target :: scope.openDecls } }

theorem le_of_hasDerivAt_nonpos_off_finite {f : ℝ → ℝ} {S : Set ℝ} (hS : S.Finite) :
    ∀ (N : ℕ) (a b : ℝ), a ≤ b → (S ∩ _root_.Set.Ioo a b).ncard ≤ N →
      (∀ x ∈ _root_.Set.Ioo a b, x ∉ S → ∃ d ≤ 0, HasDerivAt f d x) →
      (∀ x ∈ _root_.Set.Ioo a b, x ∈ S → ∃ L, _root_.Filter.Tendsto f (𝓝[<] x) (𝓝 L) ∧ _root_.Filter.Tendsto f (𝓝[>] x) (𝓝 L)) →
      ContinuousWithinAt f (_root_.Set.Ici a) a → ContinuousWithinAt f (_root_.Set.Iic b) b → f b ≤ f a := by
  intro N
  induction N with
  | zero =>
    intro a b hab hN hd _ ha hb
    have hempty : S ∩ _root_.Set.Ioo a b = ∅ :=
      (Set.ncard_eq_zero (hS.subset _root_.Set.inter_subset_left)).1 (Nat.le_zero.1 hN)
    refine le_of_deriv_nonpos_Icc hab (fun x hx => hd x hx fun hxS => ?_) ha hb
    exact (Set.eq_empty_iff_forall_notMem.1 hempty x) ⟨hxS, hx⟩
  | succ N ih =>
    intro a b hab hN hd hlim ha hb
    by_cases hne : (S ∩ _root_.Set.Ioo a b).Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      refine le_of_deriv_nonpos_Icc hab (fun x hx => hd x hx fun hxS => ?_) ha hb
      exact (Set.eq_empty_iff_forall_notMem.1 hne x) ⟨hxS, hx⟩
    obtain ⟨s, hsS, hs⟩ := hne
    obtain ⟨L, hL₁, hL₂⟩ := hlim s hs hsS
    have hfin : (S ∩ _root_.Set.Ioo a b).Finite := hS.subset _root_.Set.inter_subset_left
    have hcard : ∀ c d, _root_.Set.Ioo c d ⊆ _root_.Set.Ioo a b → s ∉ _root_.Set.Ioo c d → (S ∩ _root_.Set.Ioo c d).ncard ≤ N := by
      intro c d hsub hsn
      have hlt : (S ∩ _root_.Set.Ioo c d).ncard < (S ∩ _root_.Set.Ioo a b).ncard :=
        Set.ncard_lt_ncard ⟨fun x hx => ⟨hx.1, hsub hx.2⟩, fun h => hsn (h ⟨hsS, hs⟩).2⟩ hfin
      omega
    have hSs : ∀ᶠ x in 𝓝 s, x ≠ s → x ∉ S := by
      have hcl : IsClosed (S \ {s}) := (hS.subset _root_.Set.sdiff_subset).isClosed
      filter_upwards [hcl.isOpen_compl.mem_nhds (by simp)] with x hx hxs hxS
      exact hx ⟨hxS, hxs⟩
    have hleft : L ≤ f a := by
      refine le_of_tendsto hL₁ ?_
      filter_upwards [nhdsWithin_le_nhds hSs, Ioo_mem_nhdsLT hs.1, self_mem_nhdsWithin]
        with x hxS hx hxs
      have hxS' := hxS (ne_of_lt hxs)
      obtain ⟨d, -, hdx⟩ := hd x ⟨hx.1, hx.2.trans hs.2⟩ hxS'
      exact ih a x hx.1.le (hcard a x (_root_.Set.Ioo_subset_Ioo le_rfl (hx.2.trans hs.2).le)
        (fun h => (lt_irrefl s) (h.2.trans hx.2)))
        (fun y hy hyS => hd y ⟨hy.1, hy.2.trans (hx.2.trans hs.2)⟩ hyS)
        (fun y hy hyS => hlim y ⟨hy.1, hy.2.trans (hx.2.trans hs.2)⟩ hyS) ha
        hdx.continuousAt.continuousWithinAt
    have hright : f b ≤ L := by
      refine ge_of_tendsto hL₂ ?_
      filter_upwards [nhdsWithin_le_nhds hSs, Ioo_mem_nhdsGT hs.2, self_mem_nhdsWithin]
        with y hyS hy hys
      have hyS' := hyS (ne_of_gt hys)
      obtain ⟨d, -, hdy⟩ := hd y ⟨hs.1.trans hy.1, hy.2⟩ hyS'
      exact ih y b hy.2.le (hcard y b (_root_.Set.Ioo_subset_Ioo (hs.1.trans hy.1).le le_rfl)
        (fun h => (lt_irrefl s) (hy.1.trans h.1)))
        (fun z hz hzS => hd z ⟨(hs.1.trans hy.1).trans hz.1, hz.2⟩ hzS)
        (fun z hz hzS => hlim z ⟨(hs.1.trans hy.1).trans hz.1, hz.2⟩ hzS)
        hdy.continuousAt.continuousWithinAt hb
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.le_of_hasDerivAt_nonpos_off_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.le_of_hasDerivAt_nonpos_off_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.le_of_hasDerivAt_nonpos_off_finite ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.le_of_hasDerivAt_nonpos_off_finite

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
