import Mathlib.Topology.Homeomorph.Lemmas
import Submission.DifferentialGeometry.Topology.Order.DisjointGraphs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set

namespace DifferentialGeometry.Topology

variable {N : Type*} [TopologicalSpace N]

def graphBandHomeomorph (a b : N → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hab : ∀ p, a p ≠ b p) : N × ℝ ≃ₜ N × ℝ where
  toEquiv := Equiv.prodCongrRight (fun p ↦
    (affineHomeomorph (b p - a p) (a p) (sub_ne_zero.mpr (hab p).symm)).toEquiv)
  continuous_toFun := continuous_fst.prodMk
    ((((hb.sub ha).comp continuous_fst).mul continuous_snd).add (ha.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk
    ((continuous_snd.sub (ha.comp continuous_fst)).div
      ((hb.sub ha).comp continuous_fst)
      (fun x ↦ sub_ne_zero.mpr (hab x.1).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.graphBandHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.graphBandHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.graphBandHomeomorph ``Submission.DifferentialGeometry.Topology.graphBandHomeomorph

@[simp] theorem graphBandHomeomorph_apply (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p ≠ b p) (x : N × ℝ) :
    graphBandHomeomorph a b ha hb hab x = (x.1, a x.1 + (b x.1 - a x.1) * x.2) :=
  Prod.ext rfl (add_comm _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.graphBandHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.graphBandHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.graphBandHomeomorph_apply ``Submission.DifferentialGeometry.Topology.graphBandHomeomorph_apply

@[simp] theorem graphBandHomeomorph_symm_apply (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p ≠ b p) (x : N × ℝ) :
    (graphBandHomeomorph a b ha hb hab).symm x =
      (x.1, (x.2 - a x.1) / (b x.1 - a x.1)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.graphBandHomeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.graphBandHomeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.graphBandHomeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.graphBandHomeomorph_symm_apply

theorem graphBandHomeomorph_image_closed_strip (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p ≠ b p) :
    graphBandHomeomorph a b ha hb hab '' ((_root_.Set.univ : Set N) ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      {x : N × ℝ | x.2 ∈ _root_.Set.uIcc (a x.1) (b x.1)} := by
  rw [(graphBandHomeomorph a b ha hb hab).image_eq_preimage_symm]
  ext ⟨p, t⟩
  change (True ∧ 0 ≤ (t - a p) / (b p - a p) ∧
    (t - a p) / (b p - a p) ≤ 1) ↔ t ∈ _root_.Set.uIcc (a p) (b p)
  rw [true_and]
  rcases lt_or_gt_of_ne (hab p) with h | h
  · rw [_root_.Set.uIcc_of_le h.le, le_div_iff₀ (sub_pos.mpr h), _root_.MulZeroClass.zero_mul,
      div_le_one (sub_pos.mpr h)]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith only [h₀, h₁]
  · rw [_root_.Set.uIcc_of_ge h.le, le_div_iff_of_neg (sub_neg.mpr h), _root_.MulZeroClass.zero_mul,
      div_le_iff_of_neg (sub_neg.mpr h), one_mul]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith only [h₀, h₁]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.graphBandHomeomorph_image_closed_strip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.graphBandHomeomorph_image_closed_strip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.graphBandHomeomorph_image_closed_strip ``Submission.DifferentialGeometry.Topology.graphBandHomeomorph_image_closed_strip

private theorem image_closed_strip (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    graphBandHomeomorph a b ha hb (fun p ↦ ne_of_lt (hab p)) '' ((_root_.Set.univ : Set N) ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1} := by
  rw [graphBandHomeomorph_image_closed_strip]
  ext x
  change x.2 ∈ _root_.Set.uIcc (a x.1) (b x.1) ↔ a x.1 ≤ x.2 ∧ x.2 ≤ b x.1
  rw [_root_.Set.uIcc_of_le (hab x.1).le]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.image_closed_strip
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.image_closed_strip target :: scope.openDecls } }

private theorem image_open_strip (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    graphBandHomeomorph a b ha hb (fun p ↦ ne_of_lt (hab p)) '' ((_root_.Set.univ : Set N) ×ˢ _root_.Set.Ioo (0 : ℝ) 1) =
      {x : N × ℝ | a x.1 < x.2 ∧ x.2 < b x.1} := by
  rw [(graphBandHomeomorph a b ha hb (fun p ↦ ne_of_lt (hab p))).image_eq_preimage_symm]
  ext ⟨p, t⟩
  change (True ∧ 0 < (t - a p) / (b p - a p) ∧
    (t - a p) / (b p - a p) < 1) ↔ a p < t ∧ t < b p
  rw [true_and, lt_div_iff₀ (sub_pos.mpr (hab p)), _root_.MulZeroClass.zero_mul,
    div_lt_one (sub_pos.mpr (hab p))]
  constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith only [h₀, h₁]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.image_open_strip
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.image_open_strip target :: scope.openDecls } }

theorem interior_graphBand (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    interior {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1} =
      {x : N × ℝ | a x.1 < x.2 ∧ x.2 < b x.1} := by
  rw [← image_closed_strip a b ha hb hab,
    ← (graphBandHomeomorph a b ha hb (fun p ↦ ne_of_lt (hab p))).image_interior]
  simpa only [interior_prod_eq, interior_univ, interior_Icc] using
    image_open_strip a b ha hb hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.interior_graphBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.interior_graphBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.interior_graphBand ``Submission.DifferentialGeometry.Topology.interior_graphBand

theorem closure_openGraphBand (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    closure {x : N × ℝ | a x.1 < x.2 ∧ x.2 < b x.1} =
      {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1} := by
  rw [← image_open_strip a b ha hb hab,
    ← (graphBandHomeomorph a b ha hb (fun p ↦ ne_of_lt (hab p))).image_closure]
  simpa only [closure_prod_eq, closure_univ, closure_Ioo zero_ne_one] using
    image_closed_strip a b ha hb hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closure_openGraphBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closure_openGraphBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closure_openGraphBand ``Submission.DifferentialGeometry.Topology.closure_openGraphBand

theorem frontier_graphBand (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    frontier {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1} =
      range (fun p ↦ (p, a p)) ∪ _root_.Set.range (fun p ↦ (p, b p)) := by
  rw [← image_closed_strip a b ha hb hab,
    ← (graphBandHomeomorph a b ha hb (fun p ↦ ne_of_lt (hab p))).image_frontier,
    frontier_univ_prod_eq, frontier_Icc zero_le_one]
  ext y
  constructor
  · rintro ⟨⟨p, t⟩, ⟨_, ht⟩, rfl⟩
    rcases ht with rfl | ht
    · exact Or.inl ⟨p, by simp⟩
    · have ht1 : t = 1 := ht
      subst t
      exact Or.inr ⟨p, by simp⟩
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨(p, 0), ⟨mem_univ _, by simp⟩, by simp⟩
    · exact ⟨(p, 1), ⟨mem_univ _, by simp⟩, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.frontier_graphBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.frontier_graphBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.frontier_graphBand ``Submission.DifferentialGeometry.Topology.frontier_graphBand

theorem isCompact_graphBand [CompactSpace N] (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    IsCompact {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1} := by
  rw [← image_closed_strip a b ha hb hab]
  exact (isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc).image
    (graphBandHomeomorph a b ha hb (fun p ↦ ne_of_lt (hab p))).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isCompact_graphBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isCompact_graphBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isCompact_graphBand ``Submission.DifferentialGeometry.Topology.isCompact_graphBand

theorem isPreconnected_openGraphBand [PreconnectedSpace N] (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    IsPreconnected {x : N × ℝ | a x.1 < x.2 ∧ x.2 < b x.1} := by
  rw [← image_open_strip a b ha hb hab]
  exact (isPreconnected_univ.prod isPreconnected_Ioo).image _
    (graphBandHomeomorph a b ha hb (fun p ↦ ne_of_lt (hab p))).continuous.continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPreconnected_openGraphBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPreconnected_openGraphBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPreconnected_openGraphBand ``Submission.DifferentialGeometry.Topology.isPreconnected_openGraphBand

theorem isPreconnected_graphBand [PreconnectedSpace N] (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    IsPreconnected {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1} := by
  rw [← closure_openGraphBand a b ha hb hab]
  exact (isPreconnected_openGraphBand a b ha hb hab).closure

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPreconnected_graphBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPreconnected_graphBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPreconnected_graphBand ``Submission.DifferentialGeometry.Topology.isPreconnected_graphBand

theorem exists_graph_band_of_affine_height
    {X A : Type*} [TopologicalSpace X]
    (ψ : A → X × ℝ) {s c : ℝ} (hs : s ≠ 0)
    {a b : X → ℝ} (ha : Continuous a) (hb : Continuous b) (hab : ∀ x, a x < b x)
    (hrange : _root_.Set.range (fun x => ((ψ x).1, s * (ψ x).2 + c)) =
      {y : X × ℝ | a y.1 ≤ y.2 ∧ y.2 ≤ b y.1}) :
    ∃ l r : X → ℝ, Continuous l ∧ Continuous r ∧ (∀ x, l x < r x) ∧
      range ψ = {y : X × ℝ | l y.1 ≤ y.2 ∧ y.2 ≤ r y.1} := by
  have hpre : _root_.Set.range ψ = {y : X × ℝ | a y.1 ≤ s * y.2 + c ∧ s * y.2 + c ≤ b y.1} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hh : ((ψ x).1, s * (ψ x).2 + c) ∈ _root_.Set.range
          (fun x => ((ψ x).1, s * (ψ x).2 + c)) := _root_.Set.mem_range_self x
      rw [hrange] at hh
      exact hh
    · intro hy
      obtain ⟨x, hx⟩ := (show (y.1, s * y.2 + c) ∈ _root_.Set.range (fun x => ((ψ x).1, s * (ψ x).2 + c)) from
        hrange.symm ▸ hy)
      have hfirst := congrArg (fun z : X × ℝ => z.1) hx
      refine ⟨x, Prod.ext hfirst ?_⟩
      exact mul_left_cancel₀ hs (add_right_cancel (congrArg Prod.snd hx))
  rcases lt_or_gt_of_ne hs with hs | hs
  · refine ⟨fun x => (b x - c) / s, fun x => (a x - c) / s,
      (hb.sub continuous_const).div_const s, (ha.sub continuous_const).div_const s, ?_, ?_⟩
    · intro x
      exact (div_lt_div_right_of_neg hs).mpr (sub_lt_sub_right (hab x) c)
    · rw [hpre]
      ext y
      simp only [_root_.Set.mem_ofPred_eq, div_le_iff_of_neg hs, le_div_iff_of_neg hs]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  · refine ⟨fun x => (a x - c) / s, fun x => (b x - c) / s,
      (ha.sub continuous_const).div_const s, (hb.sub continuous_const).div_const s, ?_, ?_⟩
    · intro x
      exact (div_lt_div_iff_of_pos_right hs).mpr (sub_lt_sub_right (hab x) c)
    · rw [hpre]
      ext y
      simp only [_root_.Set.mem_ofPred_eq, div_le_iff₀ hs, le_div_iff₀ hs]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_graph_band_of_affine_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_graph_band_of_affine_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_graph_band_of_affine_height ``Submission.DifferentialGeometry.Topology.exists_graph_band_of_affine_height

theorem exists_uniform_gap_between_disjoint_graph_bands
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [PreconnectedSpace X]
    {a b c d : X → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d)
    (hab : ∀ x, a x ≤ b x) (hcd : ∀ x, c x ≤ d x)
    (hdisj : Disjoint {p : X × ℝ | a p.1 ≤ p.2 ∧ p.2 ≤ b p.1}
      {p : X × ℝ | c p.1 ≤ p.2 ∧ p.2 ≤ d p.1}) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ m : C(X, ℝ),
      (∀ x, b x + δ ≤ m x ∧ m x + δ ≤ c x) ∨
      (∀ x, d x + δ ≤ m x ∧ m x + δ ≤ a x) := by
  have hgap {u v : X → ℝ} (hu : Continuous u) (hv : Continuous v) (h : ∀ x, u x < v x) :
      ∃ δ : ℝ, 0 < δ ∧ ∃ m : C(X, ℝ), ∀ x, u x + δ ≤ m x ∧ m x + δ ≤ v x := by
    have hpositive (x : X) (_hx : x ∈ _root_.Set.univ) : (0 : ℝ) < v x - u x := sub_pos.mpr (h x)
    obtain ⟨r, hr, hbound⟩ := isCompact_univ.exists_forall_le'
      (hv.sub hu).continuousOn hpositive
    refine ⟨r / 2, half_pos hr, ⟨fun x => (u x + v x) / 2,
      (hu.add hv).div_const 2⟩, ?_⟩
    intro x
    have hh := hbound x (_root_.Set.mem_univ x)
    change r ≤ v x - u x at hh
    constructor <;> dsimp only [ContinuousMap.coe_mk] <;> linarith
  rcases (disjoint_graph_bands_iff_of_preconnected hb hc hab hcd).mp hdisj with h | h
  · obtain ⟨δ, hδ, m, hm⟩ := hgap hb hc h
    exact ⟨δ, hδ, m, Or.inl hm⟩
  · obtain ⟨δ, hδ, m, hm⟩ := hgap hd ha h
    exact ⟨δ, hδ, m, Or.inr hm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_uniform_gap_between_disjoint_graph_bands then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_uniform_gap_between_disjoint_graph_bands"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_uniform_gap_between_disjoint_graph_bands ``Submission.DifferentialGeometry.Topology.exists_uniform_gap_between_disjoint_graph_bands

end DifferentialGeometry.Topology

end

set_option autoImplicit false
open _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

private theorem isLeast_mem_frontier {s : Set ℝ} {a : ℝ}
    (ha : IsLeast (closure s) a) : a ∈ frontier s := by
  refine ⟨ha.1, ?_⟩
  intro hin
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (mem_interior_iff_mem_nhds.mp hin)
  have hmid : (l + a) / 2 ∈ s := hsub ⟨by linarith [hlu.1], by linarith [hlu.1, hlu.2]⟩
  have hm := ha.2 (subset_closure hmid)
  linarith [hlu.1]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.isLeast_mem_frontier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.isLeast_mem_frontier target :: scope.openDecls } }

private theorem isGreatest_mem_frontier {s : Set ℝ} {b : ℝ}
    (hb : IsGreatest (closure s) b) : b ∈ frontier s := by
  refine ⟨hb.1, ?_⟩
  intro hin
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (mem_interior_iff_mem_nhds.mp hin)
  have hmid : (b + u) / 2 ∈ s := hsub ⟨by linarith [hlu.1, hlu.2], by linarith [hlu.2]⟩
  have hm := hb.2 (subset_closure hmid)
  linarith [hlu.2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.isGreatest_mem_frontier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.isGreatest_mem_frontier target :: scope.openDecls } }

theorem exists_vertical_frontier_bounds_of_mem_interior
    {K : Set (X × ℝ)} (hK : IsCompact K) {x : X} {t : ℝ}
    (ht : (x, t) ∈ interior K) :
    ∃ a b : ℝ, a < t ∧ t < b ∧ (x, a) ∈ frontier K ∧ (x, b) ∈ frontier K := by
  let f : ℝ → X × ℝ := fun s => (x, s)
  have hf : Continuous f := continuous_const.prodMk continuous_id
  let A := f ⁻¹' K
  have hA : IsCompact (closure A) := by
    apply (hK.image continuous_snd).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (hK.image continuous_snd).isClosed
    intro s hs
    exact ⟨(x, s), hs, rfl⟩
  have htA : t ∈ interior A :=
    preimage_interior_subset_interior_preimage hf ht
  have hne : (closure A).Nonempty := ⟨t, subset_closure (interior_subset htA)⟩
  obtain ⟨a, ha⟩ := hA.exists_isLeast hne
  obtain ⟨b, hb⟩ := hA.exists_isGreatest hne
  have haf : a ∈ frontier A := isLeast_mem_frontier ha
  have hbf : b ∈ frontier A := isGreatest_mem_frontier hb
  refine ⟨a, b, ?_, ?_, hf.frontier_preimage_subset K haf, hf.frontier_preimage_subset K hbf⟩
  · have hat : a ≤ t := ha.2 (subset_closure (interior_subset htA))
    exact lt_of_le_of_ne hat (fun he => haf.2 (he.symm ▸ htA))
  · have htb : t ≤ b := hb.2 (subset_closure (interior_subset htA))
    exact lt_of_le_of_ne htb (fun he => hbf.2 (he ▸ htA))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_vertical_frontier_bounds_of_mem_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_vertical_frontier_bounds_of_mem_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_vertical_frontier_bounds_of_mem_interior ``Submission.DifferentialGeometry.Topology.exists_vertical_frontier_bounds_of_mem_interior

theorem interior_eq_empty_of_frontier_subset_graph
    {K : Set (X × ℝ)} (hK : IsCompact K) (f : X → ℝ)
    (hfrontier : frontier K ⊆ _root_.Set.range (fun x => (x, f x))) : interior K = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro ⟨x, t⟩ ht
  obtain ⟨a, b, hat, htb, ha, hb⟩ := exists_vertical_frontier_bounds_of_mem_interior hK ht
  obtain ⟨y, hy⟩ := hfrontier ha
  obtain ⟨z, hz⟩ := hfrontier hb
  have hyx : y = x := congrArg Prod.fst hy
  have hzx : z = x := congrArg Prod.fst hz
  have hay : f y = a := congrArg Prod.snd hy
  have hbz : f z = b := congrArg Prod.snd hz
  rw [hyx] at hay
  rw [hzx] at hbz
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.interior_eq_empty_of_frontier_subset_graph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.interior_eq_empty_of_frontier_subset_graph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.interior_eq_empty_of_frontier_subset_graph ``Submission.DifferentialGeometry.Topology.interior_eq_empty_of_frontier_subset_graph

end DifferentialGeometry.Topology
