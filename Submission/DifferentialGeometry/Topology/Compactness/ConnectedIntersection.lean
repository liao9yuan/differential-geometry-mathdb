import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Connected.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

open _root_.IsCompact in
theorem IsCompact.isPreconnected_iInter_of_directed {X ι : Type*}
    [TopologicalSpace X] [T2Space X] {K : ι → Set X} {i₀ : ι}
    (hcompact : IsCompact (K i₀)) (hclosed : ∀ i, IsClosed (K i))
    (hdir : Directed (· ⊇ ·) K)
    (hconn : ∀ i, IsPreconnected (K i)) : IsPreconnected (⋂ i, K i) := by
  classical
  let S := ⋂ i, K i
  let : Nonempty ι := ⟨i₀⟩
  have hSc : IsCompact S := hcompact.of_isClosed_subset
    (isClosed_iInter hclosed) (_root_.Set.iInter_subset K i₀)
  apply isPreconnected_closed_iff.mpr
  intro F G hF hG hcover hSF hSG
  by_contra hmeet
  have hdisj : Disjoint (S ∩ F) (S ∩ G) := by
    apply disjoint_left.mpr
    intro x hxF hxG
    exact hmeet ⟨x, hxF.1, hxF.2, hxG.2⟩
  obtain ⟨U, V, hU, hV, hSFU, hSGV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hSc.inter_right hF) (hSc.inter_right hG) hdisj
  have hScover : S ⊆ U ∪ V := by
    intro x hx
    rcases hcover hx with hxF | hxG
    · exact Or.inl (hSFU ⟨hx, hxF⟩)
    · exact Or.inr (hSGV ⟨hx, hxG⟩)
  have hex : ∃ i, K i ⊆ U ∪ V := by
    have hempty : (K i₀ ∩ (U ∪ V)ᶜ) ∩ ⋂ i, K i = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxS⟩
      exact hx.2 (hScover hxS)
    obtain ⟨i, hi⟩ :=
      (hcompact.inter_right (hU.union hV).isClosed_compl).elim_directed_family_closed
        K hclosed hempty hdir
    obtain ⟨k, hk₀, hki⟩ := hdir i₀ i
    refine ⟨k, ?_⟩
    intro x hx
    by_contra hxUV
    have hm : x ∈ (K i₀ ∩ (U ∪ V)ᶜ) ∩ K i := ⟨⟨hk₀ hx, hxUV⟩, hki hx⟩
    rw [hi] at hm
    exact hm
  obtain ⟨i, hi⟩ := hex
  obtain ⟨x, hxS, hxF⟩ := hSF
  obtain ⟨y, hyS, hyG⟩ := hSG
  obtain ⟨z, _, hzU, hzV⟩ := hconn i U V hU hV hi
    ⟨x, mem_iInter.mp hxS i, hSFU ⟨hxS, hxF⟩⟩
    ⟨y, mem_iInter.mp hyS i, hSGV ⟨hyS, hyG⟩⟩
  exact disjoint_left.mp hUV hzU hzV

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsCompact
  let env ← Lean.getEnv
  if env.contains `IsCompact.isPreconnected_iInter_of_directed then
    throwError "Refusing to shadow existing declaration IsCompact.isPreconnected_iInter_of_directed"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.isPreconnected_iInter_of_directed ``Submission.IsCompact.isPreconnected_iInter_of_directed

open _root_.IsCompact in
theorem IsCompact.isConnected_iInter_of_directed {X ι : Type*}
    [TopologicalSpace X] [T2Space X] {K : ι → Set X} {i₀ : ι}
    (hcompact : IsCompact (K i₀)) (hclosed : ∀ i, IsClosed (K i))
    (hdir : Directed (· ⊇ ·) K)
    (hconn : ∀ i, IsConnected (K i)) : IsConnected (⋂ i, K i) := by
  let : Nonempty ι := ⟨i₀⟩
  refine ⟨?_, hcompact.isPreconnected_iInter_of_directed hclosed hdir
    (fun i => (hconn i).isPreconnected)⟩
  by_contra h
  have hempty : K i₀ ∩ ⋂ i, K i = ∅ := by rw [not_nonempty_iff_eq_empty.mp h, _root_.Set.inter_empty]
  obtain ⟨i, hi⟩ := hcompact.elim_directed_family_closed K hclosed hempty hdir
  obtain ⟨k, hk₀, hki⟩ := hdir i₀ i
  obtain ⟨x, hx⟩ := (hconn k).nonempty
  have hm : x ∈ K i₀ ∩ K i := ⟨hk₀ hx, hki hx⟩
  rw [hi] at hm
  exact hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.isConnected_iInter_of_directed then
    throwError "Refusing to shadow existing declaration IsCompact.isConnected_iInter_of_directed"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.isConnected_iInter_of_directed ``Submission.IsCompact.isConnected_iInter_of_directed

open _root_.Continuous in
theorem Continuous.isPreconnected_ge_of_isPreconnected_gt {X α : Type*}
    [TopologicalSpace X] [T2Space X] [LinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderClosedTopology α] {f : X → α} (hf : Continuous f)
    {b c : α} (hbc : b < c) (hb : IsCompact {x | b ≤ f x})
    (hc : ∀ t ∈ _root_.Set.Ioo b c, IsPreconnected {x | t < f x}) :
    IsPreconnected {x | c ≤ f x} := by
  let K : _root_.Set.Ioo b c → Set X := fun t => closure {x | t.val < f x}
  obtain ⟨t₀, ht₀b, ht₀c⟩ := exists_between hbc
  have hK (t : _root_.Set.Ioo b c) : IsCompact (K t) := hb.of_isClosed_subset isClosed_closure
    (closure_minimal (fun x hx => le_trans t.property.1.le hx.le)
      (isClosed_le continuous_const hf))
  have hdir : Directed (· ⊇ ·) K := by
    intro u v
    refine ⟨⟨max u.val v.val, lt_max_of_lt_left u.property.1,
      max_lt u.property.2 v.property.2⟩, ?_, ?_⟩
    · exact closure_mono (fun x hx => lt_of_le_of_lt (le_max_left _ _) hx)
    · exact closure_mono (fun x hx => lt_of_le_of_lt (le_max_right _ _) hx)
  have heq : (⋂ t, K t) = {x | c ≤ f x} := by
    ext x
    constructor
    · intro hx
      by_contra hcx
      obtain ⟨t, ht, htc⟩ := exists_between (max_lt hbc (lt_of_not_ge hcx))
      have htb : b < t := lt_of_le_of_lt (le_max_left _ _) ht
      have htfx : t ≤ f x :=
        closure_minimal (fun y hy => hy.le) (isClosed_le continuous_const hf)
          (mem_iInter.mp hx ⟨t, htb, htc⟩)
      exact (lt_of_le_of_lt (le_max_right _ _) ht).not_ge htfx
    · intro hx
      exact mem_iInter.mpr fun t => subset_closure (lt_of_lt_of_le t.property.2 hx)
  rw [← heq]
  exact (hK ⟨t₀, ht₀b, ht₀c⟩).isPreconnected_iInter_of_directed
    (fun _ => isClosed_closure) hdir (fun t => (hc t.val t.property).closure)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Continuous
  let env ← Lean.getEnv
  if env.contains `Continuous.isPreconnected_ge_of_isPreconnected_gt then
    throwError "Refusing to shadow existing declaration Continuous.isPreconnected_ge_of_isPreconnected_gt"
  Lean.modifyEnv fun env => Lean.addAlias env `Continuous.isPreconnected_ge_of_isPreconnected_gt ``Submission.Continuous.isPreconnected_ge_of_isPreconnected_gt

open _root_.Continuous in
theorem Continuous.isPreconnected_le_of_isPreconnected_lt {X α : Type*}
    [TopologicalSpace X] [T2Space X] [LinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderClosedTopology α] {f : X → α} (hf : Continuous f)
    {b c : α} (hcb : c < b) (hb : IsCompact {x | f x ≤ b})
    (hc : ∀ t ∈ _root_.Set.Ioo c b, IsPreconnected {x | f x < t}) :
    IsPreconnected {x | f x ≤ c} := by
  exact Continuous.isPreconnected_ge_of_isPreconnected_gt (α := OrderDual α)
    (f := f) (b := b) (c := c) hf hcb hb (fun t ht => hc t ⟨ht.2, ht.1⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Continuous.isPreconnected_le_of_isPreconnected_lt then
    throwError "Refusing to shadow existing declaration Continuous.isPreconnected_le_of_isPreconnected_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `Continuous.isPreconnected_le_of_isPreconnected_lt ``Submission.Continuous.isPreconnected_le_of_isPreconnected_lt
