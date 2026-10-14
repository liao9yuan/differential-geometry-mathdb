/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PlanarJordan.LocalArcStraightening
import Submission.DifferentialGeometry.Topology.PlanarJordan.ArcFamilyStraightening
import Submission.DifferentialGeometry.Topology.PlanarJordan.ArcNeighborhood
import Submission.DifferentialGeometry.Topology.MetricSpace.Diameter

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter _root_.Topology

namespace DifferentialGeometry.Topology.PlanarJordan

open _root_.Submission.Schoenflies

private theorem exists_polygonal_subarcs_subarc
    {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : _root_.Set.InjOn f unitInterval)
    {l r a b : ℝ} (hl : l ∈ unitInterval) (hr : r ∈ unitInterval) (hlr : l < r)
    (ha : a ∈ unitInterval) (hb : b ∈ unitInterval) (har : a < r) (hlb : l < b)
    (hleft : IsPolygonal (f '' _root_.Set.Icc l b)) (hright : IsPolygonal (f '' _root_.Set.Icc a r)) :
    ∃ u v : ℝ, 0 < u ∧ u < v ∧ v < 1 ∧
      IsPolygonal (subarc f l r '' _root_.Set.Icc 0 u) ∧
      IsPolygonal (subarc f l r '' _root_.Set.Icc v 1) := by
  let p := _root_.Min.min b ((l + r) / 2)
  let q := _root_.Max.max a ((l + r) / 2)
  have hlp : l < p := lt_min hlb (by linarith)
  have hpr : p < r := (min_le_right _ _).trans_lt (by linarith)
  have hlq : l < q := lt_of_lt_of_le (by linarith : l < (l + r) / 2) (le_max_right _ _)
  have hqr : q < r := max_lt har (by linarith)
  have hpI : p ∈ unitInterval := ⟨hl.1.trans hlp.le, hpr.le.trans hr.2⟩
  have hqI : q ∈ unitInterval := ⟨hl.1.trans hlq.le, hqr.le.trans hr.2⟩
  have hP : IsArcBetween (f '' _root_.Set.Icc l p) (f l) (f p) := by
    simpa only [_root_.Set.uIcc_of_le hlp.le] using
      isArcBetween_subarc_of_injOn_I hf hi hl hpI hlp.ne
  have hQ : IsArcBetween (f '' _root_.Set.Icc q r) (f q) (f r) := by
    simpa only [_root_.Set.uIcc_of_le hqr.le] using
      isArcBetween_subarc_of_injOn_I hf hi hqI hr hqr.ne
  have hL : IsArcBetween (f '' _root_.Set.Icc l b) (f l) (f b) := by
    simpa only [_root_.Set.uIcc_of_le hlb.le] using
      isArcBetween_subarc_of_injOn_I hf hi hl hb hlb.ne
  have hR : IsArcBetween (f '' _root_.Set.Icc a r) (f a) (f r) := by
    simpa only [_root_.Set.uIcc_of_le har.le] using
      isArcBetween_subarc_of_injOn_I hf hi ha hr har.ne
  apply exists_polygonal_subarcs_of_polygonal_subsets (continuousOn_subarc hf hl hr)
    (injOn_subarc (hi.mono (uIcc_subset_I hl hr)) hlr.ne)
    (by simpa only [subarc_zero] using hP) (by simpa only [subarc_one] using hQ.reverse)
    (hP.isPolygonal_of_subset_arc hL hleft (_root_.Set.image_mono (_root_.Set.Icc_subset_Icc_right (min_le_left _ _))))
    (hQ.isPolygonal_of_subset_arc hR hright (_root_.Set.image_mono (_root_.Set.Icc_subset_Icc_left (le_max_left _ _))))
  · rw [subarc_image, _root_.Set.uIcc_of_le hlr.le]
    exact _root_.Set.image_mono (_root_.Set.Icc_subset_Icc_right hpr.le)
  · rw [subarc_image, _root_.Set.uIcc_of_le hlr.le]
    exact _root_.Set.image_mono (_root_.Set.Icc_subset_Icc_left hlq.le)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_polygonal_subarcs_subarc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.exists_polygonal_subarcs_subarc target :: scope.openDecls } }

theorem exists_homeomorph_polygonal_intervals_of_strictAnti
    {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : _root_.Set.InjOn f unitInterval)
    {t : ℕ → ℝ} (ht : ∀ n, t n ∈ _root_.Set.Ioo (0 : ℝ) 1) (hanti : StrictAnti t)
    (htlim : _root_.Filter.Tendsto t _root_.Filter.atTop (𝓝 0)) {U : Set Plane} (hU : IsOpen U)
    (hAU : f '' unitInterval ⊆ U) :
    ∃ e : Plane ≃ₜ Plane,
      (∀ n, IsPolygonal (e '' (f '' _root_.Set.Icc (t (n + 1)) (t n))) ∧ e (f (t n)) = f (t n)) ∧
      e (f 0) = f 0 ∧ e (f 1) = f 1 ∧ _root_.Set.EqOn e id Uᶜ := by
  have htI (n : ℕ) : t n ∈ unitInterval := ⟨(ht n).1.le, (ht n).2.le⟩
  have hstep (n : ℕ) : t (n + 1) < t n := hanti (Nat.lt_succ_self n)
  obtain ⟨a, b, e₀, hdata, he₀0, he₀1, he₀fix⟩ :=
    exists_homeomorph_polygonal_subarcs_of_strictAnti hf hi ht hanti
      (N := fun _ => U) (fun n => hU.mem_nhds (hAU (_root_.Set.mem_image_of_mem f (htI n))))
  have he₀outside : _root_.Set.EqOn e₀ id Uᶜ := by simpa only [_root_.Set.iUnion_const] using he₀fix
  let F := e₀ ∘ f
  have hF : ContinuousOn F unitInterval := e₀.continuous.comp_continuousOn hf
  have hFi : _root_.Set.InjOn F unitInterval := fun x hx y hy hxy => hi hx hy (e₀.injective hxy)
  have hFU : F '' unitInterval ⊆ U := by
    rintro x ⟨v, hv, rfl⟩
    by_contra hx
    have hfix : e₀ (f v) = f v := e₀.injective (he₀outside hx)
    apply hx
    change e₀ (f v) ∈ U
    rw [hfix]
    exact hAU (_root_.Set.mem_image_of_mem f hv)
  have hends (n : ℕ) : ∃ u v : ℝ, 0 < u ∧ u < v ∧ v < 1 ∧
      IsPolygonal (subarc F (t (n + 1)) (t n) '' _root_.Set.Icc 0 u) ∧
      IsPolygonal (subarc F (t (n + 1)) (t n) '' _root_.Set.Icc v 1) := by
    obtain ⟨han, hatn, _, _, hpln, _, _⟩ := hdata n
    obtain ⟨_, _, htbn, hbn, _, hprn, _⟩ := hdata (n + 1)
    apply exists_polygonal_subarcs_subarc hF hFi (htI (n + 1)) (htI n) (hstep n)
      ⟨han.le, hatn.le.trans (htI n).2⟩ ⟨(htI (n + 1)).1.trans htbn.le, hbn.le⟩ hatn htbn
    · simpa only [F, _root_.Set.image_image, Function.comp_def] using hprn
    · simpa only [F, _root_.Set.image_image, Function.comp_def] using hpln
  choose u v hu huv hv hleft hright using hends
  let A (n : ℕ) := subarc F (t (n + 1)) (t n)
  have hAc (n : ℕ) : ContinuousOn (A n) unitInterval :=
    continuousOn_subarc hF (htI (n + 1)) (htI n)
  have hAi (n : ℕ) : _root_.Set.InjOn (A n) unitInterval :=
    injOn_subarc (hFi.mono (uIcc_subset_I (htI (n + 1)) (htI n))) (hstep n).ne
  have htail (n : ℕ) : _root_.Set.Icc 0 (t n) ⊆ unitInterval := _root_.Set.Icc_subset_Icc_right (htI n).2
  let R (n : ℕ) := Metric.diam (F '' _root_.Set.Icc 0 (t n)) + (1 / 2 : ℝ) ^ n
  have hR (n : ℕ) : 0 < R n := add_pos_of_nonneg_of_pos Metric.diam_nonneg (pow_pos (by norm_num) n)
  have hRlim : _root_.Filter.Tendsto R _root_.Filter.atTop (𝓝 0) := by
    have hd := (hF 0 zero_mem_I).tendsto_diam_image_Icc tendsto_const_nhds htlim
      (Eventually.of_forall htail)
    have hp : _root_.Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) _root_.Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [R, zero_add] using hd.add hp
  have htailBall (n : ℕ) : F '' _root_.Set.Icc 0 (t n) ⊆ Metric.ball (F 0) (R n) := by
    intro x hx
    have hbound := (isCompact_Icc.image_of_continuousOn (hF.mono (htail n))).isBounded
    have hdist := Metric.dist_le_diam_of_mem hbound hx
      (_root_.Set.mem_image_of_mem F (show 0 ∈ _root_.Set.Icc 0 (t n) from ⟨le_rfl, (ht n).1.le⟩))
    exact hdist.trans_lt (lt_add_of_pos_right _ (pow_pos (by norm_num) n))
  obtain ⟨g, hg, hgf⟩ := isCompact_I.exists_continuous_leftInvOn hF hFi
  let V (n : ℕ) := g ⁻¹' _root_.Set.Ioo (t (n + 1)) (t n) ∩ (U ∩ Metric.ball (F 0) (R n))
  have hVopen (n : ℕ) : IsOpen (V n) :=
    (isOpen_Ioo.preimage hg).inter (hU.inter Metric.isOpen_ball)
  have hVcore (n : ℕ) : A n '' _root_.Set.Icc (u n) (v n) ⊆ V n := by
    rintro x ⟨s, hs, rfl⟩
    have hs0 : 0 < s := (hu n).trans_le hs.1
    have hs1 : s < 1 := hs.2.trans_lt (hv n)
    have hsI : s ∈ unitInterval := ⟨hs0.le, hs1.le⟩
    have hpI : reparam (t (n + 1)) (t n) s ∈ unitInterval :=
      uIcc_subset_I (htI (n + 1)) (htI n) (mapsTo_reparam hsI)
    have hparam : reparam (t (n + 1)) (t n) s ∈ _root_.Set.Ioo (t (n + 1)) (t n) := by
      dsimp [reparam]
      constructor <;> nlinarith [hstep n]
    change g (F (reparam (t (n + 1)) (t n) s)) ∈ _root_.Set.Ioo (t (n + 1)) (t n) ∧
      F (reparam (t (n + 1)) (t n) s) ∈ U ∩ Metric.ball (F 0) (R n)
    refine ⟨by rwa [hgf hpI], hFU (_root_.Set.mem_image_of_mem F hpI), htailBall n ?_⟩
    exact _root_.Set.mem_image_of_mem F ⟨hpI.1, hparam.2.le⟩
  have hVdis : Pairwise fun n m => Disjoint (V n) (V m) := by
    intro n m hnm
    refine disjoint_left.mpr fun x hx hy => ?_
    have hn : g x ∈ _root_.Set.Ioo (t (n + 1)) (t n) := hx.1
    have hm : g x ∈ _root_.Set.Ioo (t (m + 1)) (t m) := hy.1
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · have hle := hanti.antitone (Nat.succ_le_of_lt hlt)
      linarith [hn.1, hm.2]
    · have hle := hanti.antitone (Nat.succ_le_of_lt hgt)
      linarith [hm.1, hn.2]
  have hVavoid (n m : ℕ) (hnm : n ≠ m) : Disjoint (V n) (A m '' unitInterval) := by
    refine disjoint_left.mpr fun x hx hy => ?_
    rw [show A m = subarc F (t (m + 1)) (t m) from rfl,
      subarc_image, _root_.Set.uIcc_of_le (hstep m).le] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    have hsI : s ∈ unitInterval := ⟨(htI (m + 1)).1.trans hs.1, hs.2.trans (htI m).2⟩
    have hn : s ∈ _root_.Set.Ioo (t (n + 1)) (t n) := by simpa only [_root_.Set.mem_preimage, hgf hsI] using hx.1
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · have hle := hanti.antitone (Nat.succ_le_of_lt hlt)
      linarith [hn.1, hs.2]
    · have hle := hanti.antitone (Nat.succ_le_of_lt hgt)
      linarith [hn.2, hs.1]
  have hVball (n : ℕ) : V n ⊆ Metric.closedBall (F 0) (R n) :=
    fun _ hx => Metric.ball_subset_closedBall hx.2.2
  have hVbounded (n : ℕ) : Bornology.IsBounded (V n) :=
    Metric.isBounded_closedBall.subset (hVball n)
  have hVlim : _root_.Filter.Tendsto (fun n => Metric.diam (V n)) _root_.Filter.cofinite (𝓝 0) := by
    rw [Nat.cofinite_eq_atTop]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [_root_.MulZeroClass.mul_zero] using hRlim.const_mul 2) (fun _ => Metric.diam_nonneg)
      (fun n => Metric.diam_le_of_subset_closedBall (hR n).le (hVball n))
  obtain ⟨D, e₁, hD, _, _, hepoly, hefix, _⟩ :=
    exists_homeomorph_polygonal_arc_family_of_disjoint_neighborhoods hAc hAi hu huv hv hleft hright
      (fun n => (hVopen n).mem_nhdsSet.mpr (hVcore n)) hVdis hVavoid hVbounded hVlim
  have he₁outside : _root_.Set.EqOn e₁ id Uᶜ := by
    intro x hx
    apply hefix
    intro hmem
    obtain ⟨n, hn⟩ := mem_iUnion.mp hmem
    exact hx ((hD n).2.2.1 (interior_subset hn)).2.1
  have he₁param (s : ℝ) (hs : s ∈ unitInterval)
      (hsV : ∀ n, s ∉ _root_.Set.Ioo (t (n + 1)) (t n)) : e₁ (F s) = F s := by
    apply hefix
    intro hmem
    obtain ⟨n, hn⟩ := mem_iUnion.mp hmem
    have hx := (hD n).2.2.1 (interior_subset hn)
    exact hsV n (by simpa only [_root_.Set.mem_preimage, hgf hs] using hx.1)
  refine ⟨e₀.trans e₁, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_⟩
    · have hp : IsPolygonal (e₁ '' (F '' _root_.Set.Icc (t (n + 1)) (t n))) := by
        simpa only [A, subarc_image, _root_.Set.uIcc_of_le (hstep n).le] using hepoly n
      simpa only [F, _root_.Set.image_image, Function.comp_def, Homeomorph.trans_apply] using hp
    · change e₁ (F (t n)) = f (t n)
      refine (he₁param (t n) (htI n) ?_).trans (hdata n).2.2.2.2.2.2
      intro m hm
      by_cases hnm : n ≤ m
      · have hle := hanti.antitone hnm
        linarith [hm.2]
      · have hle := hanti.antitone (Nat.succ_le_of_lt (not_le.mp hnm))
        linarith [hm.1]
  · change e₁ (F 0) = f 0
    refine (he₁param 0 zero_mem_I ?_).trans he₀0
    intro n hn
    exact (ht n.succ).1.not_gt hn.1
  · change e₁ (F 1) = f 1
    refine (he₁param 1 one_mem_I ?_).trans he₀1
    intro n hn
    exact (ht n).2.not_gt hn.2
  · intro x hx
    change e₁ (e₀ x) = x
    rw [he₀outside hx]
    exact he₁outside hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_intervals_of_strictAnti then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_intervals_of_strictAnti"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_intervals_of_strictAnti ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_intervals_of_strictAnti
private theorem isPolygonal_subarc_of_polygonal_intervals
    {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : _root_.Set.InjOn f unitInterval)
    {t : ℕ → ℝ} (ht : ∀ n, t n ∈ _root_.Set.Ioo (0 : ℝ) 1) (hanti : StrictAnti t)
    (htlim : _root_.Filter.Tendsto t _root_.Filter.atTop (𝓝 0))
    (hpoly : ∀ n, IsPolygonal (f '' _root_.Set.Icc (t (n + 1)) (t n)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ t 0) :
    IsPolygonal (f '' _root_.Set.Icc a b) := by
  have htI (n : ℕ) : t n ∈ unitInterval := ⟨(ht n).1.le, (ht n).2.le⟩
  have hfinite (n : ℕ) : IsPolygonal (f '' _root_.Set.Icc (t (n + 1)) (t 0)) := by
    induction n with
    | zero => exact hpoly 0
    | succ n hn =>
      have hlt := hanti (Nat.lt_succ_self (n + 1))
      have hle := hanti.antitone (Nat.zero_le (n + 1))
      rw [← _root_.Set.Icc_union_Icc_eq_Icc hlt.le hle, _root_.Set.image_union]
      exact (hpoly (n + 1)).union hn ⟨f (t (n + 1)),
        _root_.Set.mem_image_of_mem f ⟨hlt.le, le_rfl⟩, _root_.Set.mem_image_of_mem f ⟨le_rfl, hle⟩⟩
  obtain ⟨n, hn⟩ := (htlim.eventually (Iio_mem_nhds ha)).exists
  have hna : t (n + 1) < a := (hanti (Nat.lt_succ_self n)).trans hn
  have haI : a ∈ unitInterval := ⟨ha.le, hab.le.trans (hb.trans (htI 0).2)⟩
  have hbI : b ∈ unitInterval := ⟨ha.le.trans hab.le, hb.trans (htI 0).2⟩
  have hsmall : IsArcBetween (f '' _root_.Set.Icc a b) (f a) (f b) := by
    simpa only [_root_.Set.uIcc_of_le hab.le] using isArcBetween_subarc_of_injOn_I hf hi haI hbI hab.ne
  have hlt := hanti (Nat.succ_pos n)
  have hbig : IsArcBetween (f '' _root_.Set.Icc (t (n + 1)) (t 0)) (f (t (n + 1))) (f (t 0)) := by
    simpa only [_root_.Set.uIcc_of_le hlt.le] using
      isArcBetween_subarc_of_injOn_I hf hi (htI (n + 1)) (htI 0) hlt.ne
  exact hsmall.isPolygonal_of_subset_arc hbig (hfinite n) (_root_.Set.image_mono (_root_.Set.Icc_subset_Icc hna.le hb))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.isPolygonal_subarc_of_polygonal_intervals
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.isPolygonal_subarc_of_polygonal_intervals target :: scope.openDecls } }

theorem exists_homeomorph_polygonal_subarcs_away_from_endpoint
    {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : _root_.Set.InjOn f unitInterval)
    {r : ℝ} (hr : r ∈ _root_.Set.Ioo (0 : ℝ) 1) {U : Set Plane} (hU : IsOpen U)
    (hAU : f '' unitInterval ⊆ U) :
    ∃ e : Plane ≃ₜ Plane,
      (∀ a b : ℝ, 0 < a → a < b → b ≤ r → IsPolygonal (e '' (f '' _root_.Set.Icc a b))) ∧
      e (f 0) = f 0 ∧ e (f 1) = f 1 ∧ e (f r) = f r ∧ _root_.Set.EqOn e id Uᶜ := by
  let t (n : ℕ) := r * (1 / 2 : ℝ) ^ n
  have hpos (n : ℕ) : 0 < t n := mul_pos hr.1 (pow_pos (by norm_num) n)
  have ht (n : ℕ) : t n ∈ _root_.Set.Ioo (0 : ℝ) 1 := by
    refine ⟨hpos n, ?_⟩
    calc
      t n ≤ r * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hr.1.le
      _ = r := mul_one _
      _ < 1 := hr.2
  have hanti : StrictAnti t := by
    apply strictAnti_nat_of_succ_lt
    intro n
    have hp := hpos n
    dsimp [t] at hp ⊢
    rw [pow_succ]
    nlinarith
  have htlim : _root_.Filter.Tendsto t _root_.Filter.atTop (𝓝 0) := by
    have hp : _root_.Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) _root_.Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [t, _root_.MulZeroClass.mul_zero] using hp.const_mul r
  obtain ⟨e, he, he0, he1, hefix⟩ :=
    exists_homeomorph_polygonal_intervals_of_strictAnti hf hi ht hanti htlim hU hAU
  refine ⟨e, ?_, he0, he1, ?_, hefix⟩
  · intro a b ha hab hb
    have hpoly (n : ℕ) : IsPolygonal ((e ∘ f) '' _root_.Set.Icc (t (n + 1)) (t n)) := by
      simpa only [_root_.Set.image_image, Function.comp_def] using (he n).1
    have hresult := isPolygonal_subarc_of_polygonal_intervals (e.continuous.comp_continuousOn hf)
      (fun x hx y hy hxy => hi hx hy (e.injective hxy)) ht hanti htlim hpoly ha hab
      (by simpa only [t, pow_zero, mul_one] using hb)
    simpa only [_root_.Set.image_image, Function.comp_def] using hresult
  · simpa only [t, pow_zero, mul_one] using (he 0).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_subarcs_away_from_endpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_subarcs_away_from_endpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_subarcs_away_from_endpoint ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_subarcs_away_from_endpoint
end DifferentialGeometry.Topology.PlanarJordan
