/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskShrink
import Submission.DifferentialGeometry.Topology.InvarianceOfDomainManifold
import Submission.DifferentialGeometry.Topology.Homeomorph.Alexander
import Submission.DifferentialGeometry.Topology.Homeomorph.JordanDiskMove

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Topology _root_.Submission.Schoenflies

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.DifferentialGeometry.Topology.PlanarJordan

theorem exists_openPartialHomeomorph_ball_of_closedBall_embedding
    {S : Type*} [TopologicalSpace S] [ChartedSpace Plane S]
    (e : _root_.Metric.closedBall (0 : Plane) 1 → S) (he : Continuous e) (hinj : Function.Injective e) :
    ∃ κ : OpenPartialHomeomorph Plane S, κ.source = _root_.Metric.ball 0 1 ∧
      ∀ v : _root_.Metric.closedBall (0 : Plane) 1, v.val ∈ _root_.Metric.ball (0 : Plane) 1 → κ v.val = e v := by
  classical
  let F : Plane → S := fun x =>
    if hx : x ∈ _root_.Metric.closedBall (0 : Plane) 1 then e ⟨x, hx⟩
    else e ⟨0, _root_.Metric.mem_closedBall_self zero_le_one⟩
  have hFv : ∀ v : _root_.Metric.closedBall (0 : Plane) 1, F v.val = e v := fun v => dif_pos v.2
  have hFc : ContinuousOn F (_root_.Metric.ball (0 : Plane) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h : (_root_.Metric.ball (0 : Plane) 1).domRestrict F =
        e ∘ (fun x : _root_.Metric.ball (0 : Plane) 1 => (⟨x.val, _root_.Metric.ball_subset_closedBall x.2⟩ :
          closedBall (0 : Plane) 1)) := by
      funext x
      exact hFv ⟨x.val, _root_.Metric.ball_subset_closedBall x.2⟩
    rw [h]
    exact he.comp (continuous_subtype_val.subtype_mk _)
  have hFinj : _root_.Set.InjOn F (_root_.Metric.ball (0 : Plane) 1) := by
    intro x hx y hy hxy
    have h := hinj ((hFv ⟨x, _root_.Metric.ball_subset_closedBall hx⟩).symm.trans
      (hxy.trans (hFv ⟨y, _root_.Metric.ball_subset_closedBall hy⟩)))
    exact congrArg (fun w : _root_.Metric.closedBall (0 : Plane) 1 => w.val) h
  let e₀ := hFinj.toPartialEquiv F (_root_.Metric.ball (0 : Plane) 1)
  have hopen : IsOpenMap ((_root_.Metric.ball (0 : Plane) 1).domRestrict F) := by
    intro V hV
    have hV' : IsOpen (Subtype.val '' V) := isOpen_ball.isOpenMap_subtype_val V hV
    have hVb : Subtype.val '' V ⊆ _root_.Metric.ball (0 : Plane) 1 := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have himage : (_root_.Metric.ball (0 : Plane) 1).domRestrict F '' V = F '' (Subtype.val '' V) := by
      rw [← _root_.Set.image_comp]
      rfl
    rw [himage]
    exact isOpen_image_of_continuousOn_injOn (E := Plane) hV' (hFc.mono hVb) (hFinj.mono hVb)
  exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict e₀ hFc hopen _root_.Metric.isOpen_ball, rfl,
    fun v _ => hFv v⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_openPartialHomeomorph_ball_of_closedBall_embedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_openPartialHomeomorph_ball_of_closedBall_embedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_openPartialHomeomorph_ball_of_closedBall_embedding ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_openPartialHomeomorph_ball_of_closedBall_embedding

theorem exists_isotopy_closedBall_embedding_onto
    {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (e : _root_.Metric.closedBall (0 : Plane) 1 → S) (he : Continuous e) (hinj : Function.Injective e)
    {W : Set S} (hW : IsOpen W) (hDW : _root_.Set.range e ⊆ W) :
    ∃ O : Set S, IsOpen O ∧ O.Nonempty ∧ O ⊆ W ∧
      ∀ g : _root_.Metric.closedBall (0 : Plane) 1 → S, Continuous g → Function.Injective g → _root_.Set.range g ⊆ O →
        ∃ G : ℝ → S ≃ₜ S, Continuous (fun p : ℝ × S => G p.1 p.2) ∧
          Continuous (fun p : ℝ × S => (G p.1).symm p.2) ∧ G 0 = Homeomorph.refl S ∧
          (∃ K : Set S, IsCompact K ∧ K ⊆ W ∧ ∀ t, _root_.Set.EqOn (G t) id Kᶜ) ∧
          G 1 '' _root_.Set.range e = _root_.Set.range g := by
  classical
  obtain ⟨s, hs0, hs1, G₁, hG₁c, hG₁ci, hG₁0, ⟨K₁, hK₁c, hK₁W, hK₁fix⟩, hG₁img⟩ :=
    exists_isotopy_shrink_closedBall_embedding e he hinj hW hDW
  obtain ⟨κ, hκs, hκe⟩ := exists_openPartialHomeomorph_ball_of_closedBall_embedding e he hinj
  have hκt : κ.target ⊆ _root_.Set.range e := by
    intro y hy
    have hx := κ.map_target hy
    rw [hκs] at hx
    exact ⟨⟨κ.symm y, _root_.Metric.ball_subset_closedBall hx⟩,
      (hκe ⟨κ.symm y, _root_.Metric.ball_subset_closedBall hx⟩ hx).symm.trans (κ.right_inv hy)⟩
  have hsub : _root_.Metric.ball (0 : Plane) s ⊆ κ.source := by
    rw [hκs]
    exact _root_.Metric.ball_subset_ball hs1.le
  refine ⟨κ '' _root_.Metric.ball 0 s, κ.isOpen_image_of_subset_source _root_.Metric.isOpen_ball hsub,
    ⟨κ 0, 0, _root_.Metric.mem_ball_self hs0, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hDW (hκt (κ.map_source (hsub hx)))
  intro g hg hginj hgO
  have hgt : ∀ v, g v ∈ κ.target := by
    intro v
    obtain ⟨x, hx, hxe⟩ := hgO ⟨v, rfl⟩
    rw [← hxe]
    exact κ.map_source (hsub hx)
  let g' : _root_.Metric.closedBall (0 : Plane) 1 → Plane := fun v => κ.symm (g v)
  have hg'c : Continuous g' := κ.continuousOn_symm.comp_continuous hg hgt
  have hg'inj : Function.Injective g' := fun v w h => hginj (κ.symm.injOn (hgt v) (hgt w) h)
  have hg'ball : ∀ v, g' v ∈ _root_.Metric.ball (0 : Plane) s := by
    intro v
    obtain ⟨x, hx, hxe⟩ := hgO ⟨v, rfl⟩
    change κ.symm (g v) ∈ _
    rw [← hxe, κ.left_inv (hsub hx)]
    exact hx
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph_extending_closedBall_embedding g' hg'c hg'inj
  have hΦB : Φ '' _root_.Metric.closedBall (0 : Plane) 1 = _root_.Set.range g' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hΦ ⟨x, hx⟩).symm⟩
    · rintro ⟨v, rfl⟩
      exact ⟨v.val, v.2, hΦ v⟩
  have hΨ : (Homeomorph.smulOfNeZero s hs0.ne' : Plane ≃ₜ Plane) '' _root_.Metric.closedBall (0 : Plane) 1 =
      closedBall 0 s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_closedBall_zero_iff] at hx ⊢
      change ‖s • x‖ ≤ s
      rw [norm_smul, Real.norm_of_nonneg hs0.le]
      nlinarith [norm_nonneg x]
    · intro hy
      refine ⟨s⁻¹ • y, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hs0.le,
          inv_mul_le_iff₀ hs0, mul_one]
        exact mem_closedBall_zero_iff.mp hy
      · change s • s⁻¹ • y = y
        rw [smul_inv_smul₀ hs0.ne']
  let φ₁ : _root_.Metric.closedBall (0 : Plane) s ≃ₜ _root_.Metric.closedBall (0 : Plane) 1 :=
    (((Homeomorph.smulOfNeZero s hs0.ne' : Plane ≃ₜ Plane).image
      (_root_.Metric.closedBall (0 : Plane) 1)).trans (Homeomorph.setCongr hΨ)).symm
  let φ₂ : (Φ '' _root_.Metric.closedBall (0 : Plane) 1 : Set Plane) ≃ₜ _root_.Metric.closedBall (0 : Plane) 1 :=
    (Φ.image (_root_.Metric.closedBall (0 : Plane) 1)).symm
  have hC₁ := closure_inside_frontier_eq_of_homeomorphClosedBall φ₁
  have hC₂ := closure_inside_frontier_eq_of_homeomorphClosedBall φ₂
  set t₁ : ℝ := (1 + s) / 2 with ht₁
  have hU₁ : _root_.Metric.closedBall (0 : Plane) s ⊆ _root_.Metric.ball 0 t₁ := _root_.Metric.closedBall_subset_ball (by linarith)
  have hU₂ : Φ '' _root_.Metric.closedBall (0 : Plane) 1 ⊆ _root_.Metric.ball 0 t₁ := by
    rw [hΦB]
    rintro _ ⟨v, rfl⟩
    exact _root_.Metric.ball_subset_ball (by linarith) (hg'ball v)
  obtain ⟨m, hm, hmfix⟩ := Homeomorph.exists_image_closed_region_eqOn_compl
    (isJordanCurve_frontier_of_homeomorphClosedBall φ₁)
    (isJordanCurve_frontier_of_homeomorphClosedBall φ₂) _root_.Metric.isOpen_ball
    (convex_ball (0 : Plane) t₁).isPreconnected (by rw [hC₁]; exact hU₁) (by rw [hC₂]; exact hU₂)
  rw [hC₁, hC₂] at hm
  obtain ⟨H, hHc, hHci, hH0, hH1, hHfix, -, -⟩ := m.alexander_trick (R := t₁) (by linarith) hmfix
  have hHfix' : ∀ p, _root_.Set.EqOn (H p) id (_root_.Metric.closedBall (0 : Plane) t₁)ᶜ ∧
      EqOn (H p).symm id (_root_.Metric.closedBall (0 : Plane) t₁)ᶜ := fun p =>
    ⟨(hHfix p).1.mono (compl_subset_compl.mpr _root_.Metric.ball_subset_closedBall),
      (hHfix p).2.mono (compl_subset_compl.mpr _root_.Metric.ball_subset_closedBall)⟩
  have hCs : _root_.Metric.closedBall (0 : Plane) t₁ ⊆ κ.source := by
    rw [hκs]
    exact _root_.Metric.closedBall_subset_ball (by linarith)
  obtain ⟨J, hJc, hJci, hJeq, hJfix⟩ := κ.symm.exists_conjugate_homeomorph_family H hHc hHci
    (_root_.ProperSpace.isCompact_closedBall _ _) (by rw [OpenPartialHomeomorph.symm_target]; exact hCs) hHfix'
  let G : ℝ → S ≃ₜ S := fun t => (G₁ t).trans (J t)
  have hGc : Continuous (fun p : ℝ × S => G p.1 p.2) :=
    hJc.comp (continuous_fst.prodMk hG₁c)
  have hGci : Continuous (fun p : ℝ × S => (G p.1).symm p.2) :=
    hG₁ci.comp (continuous_fst.prodMk hJci)
  have hG0 : G 0 = Homeomorph.refl S := by
    ext y
    change J 0 (G₁ 0 y) = y
    rw [hG₁0, (hJeq 0 _).1, hH0]
    change κ.symm.conjugateMap (Homeomorph.refl Plane) y = y
    by_cases hy : y ∈ κ.symm.source
    · rw [κ.symm.conjugateMap_of_mem _ hy]
      exact κ.symm.left_inv hy
    · exact κ.symm.conjugateMap_of_notMem _ hy
  have hKc : IsCompact (K₁ ∪ κ '' _root_.Metric.closedBall (0 : Plane) t₁) :=
    hK₁c.union ((_root_.ProperSpace.isCompact_closedBall _ _).image_of_continuousOn (κ.continuousOn.mono hCs))
  have hKW : K₁ ∪ κ '' _root_.Metric.closedBall (0 : Plane) t₁ ⊆ W := _root_.Set.union_subset hK₁W (by
    rintro _ ⟨x, hx, rfl⟩
    exact hDW (hκt (κ.map_source (hCs hx))))
  have hKfix : ∀ t, _root_.Set.EqOn (G t) id (K₁ ∪ κ '' _root_.Metric.closedBall (0 : Plane) t₁)ᶜ := by
    intro t y hy
    rw [_root_.Set.mem_compl_iff, _root_.Set.mem_union, not_or] at hy
    have hyC : y ∉ κ.symm.symm '' _root_.Metric.closedBall (0 : Plane) t₁ := by
      rw [OpenPartialHomeomorph.symm_symm]
      exact hy.2
    change J t (G₁ t y) = y
    rw [hK₁fix t hy.1]
    exact (hJfix t).1 hyC
  refine ⟨G, hGc, hGci, hG0, ⟨_, hKc, hKW, hKfix⟩, ?_⟩
  have himg : G 1 '' _root_.Set.range e = J 1 '' (G₁ 1 '' _root_.Set.range e) := by
    rw [← _root_.Set.image_comp]
    rfl
  have hD : e '' {v : _root_.Metric.closedBall (0 : Plane) 1 | ‖v.val‖ ≤ s} = κ '' _root_.Metric.closedBall 0 s := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.val, mem_closedBall_zero_iff.mpr hv,
        hκe v (mem_ball_zero_iff.mpr (lt_of_le_of_lt hv hs1))⟩
    · rintro ⟨x, hx, rfl⟩
      have hx1 : x ∈ _root_.Metric.closedBall (0 : Plane) 1 := _root_.Metric.closedBall_subset_closedBall hs1.le hx
      exact ⟨⟨x, hx1⟩, mem_closedBall_zero_iff.mp hx, (hκe ⟨x, hx1⟩
        (mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hx) hs1))).symm⟩
  have hJκ : ∀ x ∈ _root_.Metric.ball (0 : Plane) 1, J 1 (κ x) = κ (m x) := by
    intro x hx
    have hxs : x ∈ κ.source := by
      rw [hκs]
      exact hx
    rw [(hJeq 1 _).1, κ.symm.conjugateMap_of_mem _ (κ.map_source hxs), κ.left_inv hxs, hH1]
    rfl
  rw [himg, hG₁img, hD]
  calc J 1 '' (κ '' _root_.Metric.closedBall (0 : Plane) s) = κ '' (m '' _root_.Metric.closedBall (0 : Plane) s) := by
        rw [← _root_.Set.image_comp, ← _root_.Set.image_comp]
        exact _root_.Set.image_congr fun x hx => hJκ x (_root_.Metric.closedBall_subset_ball (by linarith) hx)
    _ = κ '' _root_.Set.range g' := by rw [hm, hΦB]
    _ = _root_.Set.range g := by
        rw [← _root_.Set.range_comp]
        exact congrArg _root_.Set.range (funext fun v => κ.right_inv (hgt v))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isotopy_closedBall_embedding_onto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isotopy_closedBall_embedding_onto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isotopy_closedBall_embedding_onto ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isotopy_closedBall_embedding_onto

end DifferentialGeometry.Topology.PiecewiseLinear
