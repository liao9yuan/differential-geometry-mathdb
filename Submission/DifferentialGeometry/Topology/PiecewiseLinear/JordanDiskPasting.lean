/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homeomorph.JordanDiskMove
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.InnermostLevel
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.MoiseChainPL
import Submission.DifferentialGeometry.Topology.PlanarJordan.AmbientExtension
import Submission.DifferentialGeometry.Topology.PlanarJordan.CompactRegion
import Submission.DifferentialGeometry.Topology.PlanarJordan.Transport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Metric _root_.Submission.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_homeomorph_image_closure_inside_eq_closedBall {J : Set Schoenflies.Plane}
    (hJ : Schoenflies.IsJordanCurve J) :
    ∃ e : Schoenflies.Plane ≃ₜ Schoenflies.Plane, e '' J = _root_.Metric.sphere 0 1 ∧
      e '' closure (Schoenflies.inside J) = _root_.Metric.closedBall 0 1 ∧
      e '' Schoenflies.inside J = _root_.Metric.ball 0 1 := by
  have hs : Schoenflies.IsJordanCurve (_root_.Metric.sphere (0 : Schoenflies.Plane) 1) := by
    simpa only [Subtype.range_coe] using PlanarJordan.isJordanCurve_range_of_isEmbedding_circle
      (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : _root_.Metric.sphere (0 : Schoenflies.Plane) 1 → Schoenflies.Plane))
  have hfr := frontier_closedBall (0 : Schoenflies.Plane) one_ne_zero
  have hi : (interior (_root_.Metric.closedBall (0 : Schoenflies.Plane) 1)).Nonempty := by
    rw [interior_closedBall (0 : Schoenflies.Plane) one_ne_zero]
    exact nonempty_ball.mpr one_pos
  have hreg : closure (Schoenflies.inside (_root_.Metric.sphere (0 : Schoenflies.Plane) 1)) = _root_.Metric.closedBall 0 1 := by
    simpa only [hfr] using PlanarJordan.closure_inside_frontier_eq_of_isCompact
      (_root_.ProperSpace.isCompact_closedBall (0 : Schoenflies.Plane) 1) (hfr.symm ▸ hs) hi
  have hint : Schoenflies.inside (_root_.Metric.sphere (0 : Schoenflies.Plane) 1) = _root_.Metric.ball 0 1 := by
    have hh := PlanarJordan.interior_eq_inside_frontier_of_isCompact
      (_root_.ProperSpace.isCompact_closedBall (0 : Schoenflies.Plane) 1) (hfr.symm ▸ hs) hi
    simpa only [hfr, interior_closedBall (0 : Schoenflies.Plane) one_ne_zero] using hh.symm
  obtain ⟨e, he, -⟩ := Homeomorph.exists_image_closed_region_eqOn_compl hJ hs isOpen_univ
    _root_.PreconnectedSpace.isPreconnected_univ (_root_.Set.subset_univ _) (_root_.Set.subset_univ _)
  rw [hreg] at he
  have hJe : e '' J = _root_.Metric.sphere 0 1 := by
    rw [← PlanarJordan.frontier_closure_inside hJ, e.image_frontier, he, hfr]
  refine ⟨e, hJe, he, ?_⟩
  rw [PlanarJordan.image_inside, hJe, hint]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_homeomorph_image_closure_inside_eq_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_homeomorph_image_closure_inside_eq_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_homeomorph_image_closure_inside_eq_closedBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_homeomorph_image_closure_inside_eq_closedBall

theorem isConnected_setOf_one_lt_norm_lt {ε : ℝ} (hε : 0 < ε) :
    IsConnected {z : Schoenflies.Plane | 1 < ‖z‖ ∧ ‖z‖ < 1 + ε} := by
  have hrank : 1 < Module.rank ℝ Schoenflies.Plane := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by norm_num : 1 < 2)
  have hS := isConnected_sphere hrank (0 : Schoenflies.Plane) zero_le_one
  have hI : IsConnected (_root_.Set.Ioo (1 : ℝ) (1 + ε)) := isConnected_Ioo (by linarith)
  have heq : {z : Schoenflies.Plane | 1 < ‖z‖ ∧ ‖z‖ < 1 + ε} =
      (fun p : ℝ × Schoenflies.Plane => p.1 • p.2) '' (_root_.Set.Ioo (1 : ℝ) (1 + ε) ×ˢ _root_.Metric.sphere 0 1) := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      have hz : ‖z‖ ≠ 0 := by linarith
      refine ⟨(‖z‖, ‖z‖⁻¹ • z), ⟨⟨h1, h2⟩, ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hz]
      · change ‖z‖ • ‖z‖⁻¹ • z = z
        rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
    · rintro ⟨⟨r, u⟩, ⟨⟨hr1, hr2⟩, hu⟩, rfl⟩
      have hu' : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
      change 1 < ‖r • u‖ ∧ ‖r • u‖ < 1 + ε
      rw [norm_smul, hu', mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
      exact ⟨hr1, hr2⟩
  rw [heq]
  exact (hI.prod hS).image _ (continuous_fst.smul continuous_snd).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isConnected_setOf_one_lt_norm_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isConnected_setOf_one_lt_norm_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isConnected_setOf_one_lt_norm_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isConnected_setOf_one_lt_norm_lt

theorem exists_isOpen_isConnected_sdiff_closure_inside {J Z : Set Schoenflies.Plane}
    (hJ : Schoenflies.IsJordanCurve J) (hZ : IsClosed Z) (hJZ : Disjoint J Z) :
    ∃ N : Set Schoenflies.Plane, IsOpen N ∧ J ⊆ N ∧ Disjoint N Z ∧
      IsConnected (N \ closure (Schoenflies.inside J)) := by
  obtain ⟨e, hJe, hDe, -⟩ := exists_homeomorph_image_closure_inside_eq_closedBall hJ
  have hSZ : _root_.Metric.sphere (0 : Schoenflies.Plane) 1 ⊆ (e '' Z)ᶜ := by
    rw [← hJe]
    rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
    rw [e.injective hxx'] at hx'
    exact disjoint_left.mp hJZ hx hx'
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_sphere (0 : Schoenflies.Plane) 1).exists_thickening_subset_open
      (e.isClosed_image.mpr hZ).isOpen_compl hSZ
  set ε : ℝ := _root_.Min.min δ (1 / 2)
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε2 : ε ≤ 1 / 2 := min_le_right _ _
  let A : Set Schoenflies.Plane := {z | 1 - ε < ‖z‖ ∧ ‖z‖ < 1 + ε}
  have hAopen : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hAthick : A ⊆ _root_.Metric.thickening δ (_root_.Metric.sphere (0 : Schoenflies.Plane) 1) := by
    rintro z ⟨h1, h2⟩
    have hz : ‖z‖ ≠ 0 := by linarith
    rw [_root_.Metric.mem_thickening_iff]
    refine ⟨‖z‖⁻¹ • z, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hz]
    · have hu : ‖‖z‖⁻¹ • z‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hz]
      have hzz : z - ‖z‖⁻¹ • z = (‖z‖ - 1) • (‖z‖⁻¹ • z) := by
        rw [smul_smul, sub_mul, mul_inv_cancel₀ hz, one_mul, sub_smul, one_smul]
      rw [dist_eq_norm, hzz, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
  have hpre : closure (Schoenflies.inside J) = e ⁻¹' _root_.Metric.closedBall 0 1 := by
    rw [← hDe, e.preimage_image]
  refine ⟨e ⁻¹' A, hAopen.preimage e.continuous, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : e x ∈ _root_.Metric.sphere (0 : Schoenflies.Plane) 1 := hJe ▸ _root_.Set.mem_image_of_mem e hx
    have h1 : ‖e x‖ = 1 := mem_sphere_zero_iff_norm.mp hx'
    change 1 - ε < ‖e x‖ ∧ ‖e x‖ < 1 + ε
    rw [h1]
    constructor <;> linarith
  · rw [_root_.Set.disjoint_left]
    intro x hxA hxZ
    exact hthick (hAthick hxA) (_root_.Set.mem_image_of_mem e hxZ)
  · have heq : e ⁻¹' A \ closure (Schoenflies.inside J) =
        e.symm '' {z : Schoenflies.Plane | 1 < ‖z‖ ∧ ‖z‖ < 1 + ε} := by
      rw [hpre, ← _root_.Set.preimage_sdiff, e.image_symm]
      congr 1
      ext z
      simp only [A, _root_.Set.mem_sdiff, _root_.Set.mem_ofPred_eq, _root_.Metric.mem_closedBall, dist_zero_right, not_le]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by linarith, h2⟩, h1⟩
    rw [heq]
    exact (isConnected_setOf_one_lt_norm_lt hε).image _ e.symm.continuous.continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isOpen_isConnected_sdiff_closure_inside then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isOpen_isConnected_sdiff_closure_inside"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isOpen_isConnected_sdiff_closure_inside ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isOpen_isConnected_sdiff_closure_inside

theorem exists_continuousOn_mapsTo_closure_inside_of_nullhomotopic {Y : Type*}
    [TopologicalSpace Y] {J : Set Schoenflies.Plane} (hJ : Schoenflies.IsJordanCurve J)
    {B : Set Y} (b : C(J, B)) (hb : b.Nullhomotopic) :
    ∃ G : Schoenflies.Plane → Y, ContinuousOn G (closure (Schoenflies.inside J)) ∧
      MapsTo G (closure (Schoenflies.inside J)) B ∧ ∀ z : J, G z = b z := by
  classical
  obtain ⟨e, hJe, hDe, -⟩ := exists_homeomorph_image_closure_inside_eq_closedBall hJ
  have hfr := frontier_closedBall (0 : Schoenflies.Plane) one_ne_zero
  have hi : (interior (_root_.Metric.closedBall (0 : Schoenflies.Plane) 1)).Nonempty := by
    rw [interior_closedBall (0 : Schoenflies.Plane) one_ne_zero]
    exact nonempty_ball.mpr one_pos
  have hback : ∀ z ∈ frontier (_root_.Metric.closedBall (0 : Schoenflies.Plane) 1), e.symm z ∈ J := by
    intro z hz
    rw [hfr, ← hJe] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rwa [e.symm_apply_apply]
  let k : C(frontier (_root_.Metric.closedBall (0 : Schoenflies.Plane) 1), J) :=
    ⟨fun z => ⟨e.symm z, hback z z.2⟩,
      (e.symm.continuous.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨F, hF⟩ := exists_continuousMap_extension_of_nullhomotopic
    (_root_.ProperSpace.isCompact_closedBall (0 : Schoenflies.Plane) 1) (convex_closedBall 0 1) hi (b.comp k)
    (hb.comp_left k)
  have hJne : J.Nonempty := by
    obtain ⟨f, -, hfJ⟩ := hJ
    exact ⟨f 0, hfJ ▸ _root_.Set.mem_image_of_mem f Schoenflies.zero_mem_I⟩
  obtain ⟨j₀, hj₀⟩ := hJne
  have hmem : ∀ x ∈ closure (Schoenflies.inside J), e x ∈ _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 :=
    fun x hx => hDe ▸ _root_.Set.mem_image_of_mem e hx
  let G : Schoenflies.Plane → Y := fun x =>
    if h : e x ∈ _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 then (F ⟨e x, h⟩ : Y) else b ⟨j₀, hj₀⟩
  refine ⟨G, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_subtype_val.comp (F.continuous.comp
      ((e.continuous.comp continuous_subtype_val).subtype_mk fun x => hmem x x.2))).congr ?_
    intro x
    change (F ⟨e x, hmem x x.2⟩ : Y) = G x
    simp only [G, dif_pos (hmem x x.2)]
  · intro x hx
    simp only [G, dif_pos (hmem x hx)]
    exact (F _).2
  · intro z
    have hz : e z ∈ frontier (_root_.Metric.closedBall (0 : Schoenflies.Plane) 1) := by
      rw [hfr, ← hJe]
      exact _root_.Set.mem_image_of_mem e z.2
    have hzb : e z ∈ _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 :=
      (_root_.ProperSpace.isCompact_closedBall _ _).isClosed.frontier_subset hz
    change G z = b z
    simp only [G, dif_pos hzb]
    have h' : (F ⟨e z, hzb⟩ : Y) = ((b.comp k) ⟨e z, hz⟩ : Y) := congrArg Subtype.val (hF ⟨e z, hz⟩)
    have hk : k ⟨e z, hz⟩ = z := Subtype.ext (e.symm_apply_apply z)
    rw [h']
    change (b (k ⟨e z, hz⟩) : Y) = b z
    rw [hk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_continuousOn_mapsTo_closure_inside_of_nullhomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_continuousOn_mapsTo_closure_inside_of_nullhomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_continuousOn_mapsTo_closure_inside_of_nullhomotopic ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_continuousOn_mapsTo_closure_inside_of_nullhomotopic

theorem IsPLBall.nullhomotopic_of_continuousOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {Y : Type*} [TopologicalSpace Y] {n : ℕ} {D J : Set F}
    (hD : IsPLBall n D) (hJD : J ⊆ D) {X : Set Y} {G : F → Y} (hG : ContinuousOn G D)
    (hGX : _root_.Set.MapsTo G D X) (b : C(J, X)) (hb : ∀ z : J, (b z : Y) = G z) : b.Nullhomotopic := by
  let _ := hD.contractibleSpace
  let i : C(J, D) := ⟨Set.inclusion hJD, continuous_inclusion hJD⟩
  let g : C(D, X) := ⟨fun z => ⟨G z, hGX z.2⟩,
    (hG.domRestrict.subtype_mk _)⟩
  have hbg : b = g.comp ((ContinuousMap.id D).comp i) := by
    ext z
    exact hb z
  rw [hbg]
  exact ((id_nullhomotopic D).comp_left i).comp_right g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nullhomotopic_of_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nullhomotopic_of_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nullhomotopic_of_continuousOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nullhomotopic_of_continuousOn

theorem closure_inside_subset_interior_of_subset_interior {P J : Set Schoenflies.Plane}
    (hP : IsPLBall 2 P) (hJ : Schoenflies.IsJordanCurve J) (hJP : J ⊆ interior P) :
    closure (Schoenflies.inside J) ⊆ interior P := by
  have hPJ : Schoenflies.IsJordanCurve (frontier P) :=
    isJordanCurve_of_isPLSphere_one hP.isPLSphere_frontier
  have hint := PlanarJordan.interior_eq_inside_frontier_of_isCompact hP.isPolyhedron.isCompact hPJ
    hP.interior_nonempty
  have hsub : Schoenflies.inside J ⊆ Schoenflies.inside (frontier P) :=
    PlanarJordan.inside_subset_of_subset_closure_inside (Schoenflies.jordan_curve_theorem hPJ)
      (Schoenflies.jordan_curve_theorem hJ) (hJP.trans (hint ▸ subset_closure))
  rw [closure_eq_self_union_frontier, (Schoenflies.jordan_curve_theorem hJ).frontier_inside, hint]
  exact _root_.Set.union_subset hsub (hJP.trans hint.subset)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closure_inside_subset_interior_of_subset_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closure_inside_subset_interior_of_subset_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closure_inside_subset_interior_of_subset_interior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closure_inside_subset_interior_of_subset_interior

theorem exists_continuousOn_mapsTo_of_jordan_disk_pasting {Y : Type*}
    [TopologicalSpace Y] {P : Set Schoenflies.Plane} (hP : IsPLBall 2 P) {XW XR : Set Y}
    {C : Set (Set Schoenflies.Plane)} (B : Set Schoenflies.Plane → Set Y)
    (hB : ∀ c ∈ C, B c ⊆ XW ∩ XR)
    (hfillW : ∀ c ∈ C, ∀ G : Schoenflies.Plane → Y,
      ContinuousOn G (closure (Schoenflies.inside c)) →
      _root_.Set.MapsTo G (closure (Schoenflies.inside c)) XW → _root_.Set.MapsTo G c (B c) →
      ∃ G' : Schoenflies.Plane → Y, ContinuousOn G' (closure (Schoenflies.inside c)) ∧
        _root_.Set.MapsTo G' (closure (Schoenflies.inside c)) (B c) ∧ _root_.Set.EqOn G' G c)
    (hfillR : ∀ c ∈ C, ∀ G : Schoenflies.Plane → Y,
      ContinuousOn G (closure (Schoenflies.inside c)) →
      _root_.Set.MapsTo G (closure (Schoenflies.inside c)) XR → _root_.Set.MapsTo G c (B c) →
      ∃ G' : Schoenflies.Plane → Y, ContinuousOn G' (closure (Schoenflies.inside c)) ∧
        _root_.Set.MapsTo G' (closure (Schoenflies.inside c)) (B c) ∧ _root_.Set.EqOn G' G c)
    (hCfin : C.Finite) (hC : ∀ c ∈ C, IsPLSphere 1 c) (hCdisj : C.PairwiseDisjoint id)
    (hCP : ∀ c ∈ C, c ⊆ interior P) {F : Schoenflies.Plane → Y} (hF : ContinuousOn F P)
    (hFB : ∀ c ∈ C, _root_.Set.MapsTo F c (B c)) {U V : Set Schoenflies.Plane} (hU : IsOpen U)
    (hV : IsOpen V) (hUV : Disjoint (U ∩ P) (V ∩ P)) (hcover : P \ ⋃₀ C ⊆ U ∪ V)
    (hFU : _root_.Set.MapsTo F (U ∩ P) XW) (hFV : _root_.Set.MapsTo F (V ∩ P) XR) (hfront : frontier P ⊆ U) :
    ∃ G : Schoenflies.Plane → Y, ContinuousOn G P ∧ _root_.Set.MapsTo G P XW ∧ _root_.Set.EqOn G F (frontier P) := by
  classical
  have key : ∀ n : ℕ, ∀ S : Set (Set Schoenflies.Plane), S.ncard = n → S ⊆ C → S.Finite →
      (∀ c ∈ S, IsPLSphere 1 c) → S.PairwiseDisjoint id → (∀ c ∈ S, c ⊆ interior P) →
      ∀ F : Schoenflies.Plane → Y, ContinuousOn F P → (∀ c ∈ S, _root_.Set.MapsTo F c (B c)) →
      ∀ U V : Set Schoenflies.Plane, IsOpen U → IsOpen V → Disjoint (U ∩ P) (V ∩ P) →
      P \ ⋃₀ S ⊆ U ∪ V → _root_.Set.MapsTo F (U ∩ P) XW → _root_.Set.MapsTo F (V ∩ P) XR → frontier P ⊆ U →
      ∃ G : Schoenflies.Plane → Y, ContinuousOn G P ∧ _root_.Set.MapsTo G P XW ∧
        EqOn G F (frontier P) := by
    intro n
    have hUVdisj (U V S : Set Schoenflies.Plane) (hUV : Disjoint (U ∩ P) (V ∩ P)) (hS : S ⊆ P) :
        S ∩ (U ∩ V) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      exact disjoint_left.mp hUV ⟨hx.2.1, hS hx.1⟩ ⟨hx.2.2, hS hx.1⟩
    have hfrontP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
    induction n with
    | zero =>
      intro S hn _ hSfin _ _ _ F hF _ U V hU hV hUV hcover hFU _ hfront
      have hSe : S = ∅ := (Set.ncard_eq_zero hSfin).mp hn
      subst hSe
      have hPUV : P ⊆ U ∪ V := by simpa using hcover
      rcases isPreconnected_iff_subset_of_disjoint.mp hP.isConnected.isPreconnected U V hU hV hPUV
        (hUVdisj U V P hUV subset_rfl) with hPU | hPV
      · exact ⟨F, hF, fun x hx => hFU ⟨hPU hx, hx⟩, fun _ _ => rfl⟩
      · exfalso
        obtain ⟨x, hx⟩ := hP.isPLSphere_frontier.nonempty
        exact disjoint_left.mp hUV ⟨hfront hx, hfrontP hx⟩ ⟨hPV (hfrontP hx), hfrontP hx⟩
    | succ n ih =>
      intro S hn hSC hSfin hS hSdisj hSP F hF hFB U V hU hV hUV hcover hFU hFV hfront
      have hne : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
      obtain ⟨J, hJC, D, hD, hDfr, hDC⟩ := exists_innermost_isPLBall hSfin hne hS 0
        (fun c hc T hT hcT x hx => (disjoint_left.mp (hSdisj hc hT hcT) hx.1 hx.2).elim)
      have hJj := isJordanCurve_of_isPLSphere_one (hS J hJC)
      have hsepJ := Schoenflies.jordan_curve_theorem hJj
      have hDeq : closure (Schoenflies.inside J) = D := by
        have h := PlanarJordan.closure_inside_frontier_eq_of_isCompact hD.isPolyhedron.isCompact
          (hDfr ▸ hJj) hD.interior_nonempty
        rwa [hDfr] at h
      have hintD : interior D = Schoenflies.inside J := by
        have h := PlanarJordan.interior_eq_inside_frontier_of_isCompact hD.isPolyhedron.isCompact
          (hDfr ▸ hJj) hD.interior_nonempty
        rwa [hDfr] at h
      have hDclosed : IsClosed D := hD.isPolyhedron.isClosed
      have hDint : D ⊆ interior P :=
        hDeq ▸ closure_inside_subset_interior_of_subset_interior hP hJj (hSP J hJC)
      have hDP : D ⊆ P := hDint.trans interior_subset
      have hJD : J ⊆ D := hDfr ▸ hDclosed.frontier_subset
      have hmemJ : ∀ x ∈ D, x ∉ interior D → x ∈ J := fun x hx hxi => by
        rw [← hDfr]
        exact ⟨subset_closure hx, hxi⟩
      have hDother : ∀ c ∈ S, c ≠ J → Disjoint c D := by
        intro c hc hcJ
        rw [_root_.Set.disjoint_left]
        intro x hxc hxD
        have hxJ : x ∈ J := hDC.subset ⟨⟨c, hc, hxc⟩, hxD⟩
        exact disjoint_left.mp (hSdisj hc hJC hcJ) hxc hxJ
      have hintsub : interior D ⊆ P \ ⋃₀ S := by
        intro x hx
        refine ⟨hDP (interior_subset hx), fun hxC => ?_⟩
        have hxJ : x ∈ J := hDC.subset ⟨hxC, interior_subset hx⟩
        rw [← hDfr] at hxJ
        exact hxJ.2 hx
      have hintconn : IsPreconnected (interior D) := hintD ▸ hsepJ.isConnected_inside.isPreconnected
      have hBJ := hB J (hSC hJC)
      have hFJ : _root_.Set.MapsTo F J (B J) := hFB J hJC
      have hFD : ContinuousOn F (closure (Schoenflies.inside J)) := hDeq ▸ hF.mono hDP
      obtain ⟨G', hG'c, hG'B, hG'eq⟩ :
          ∃ G' : Schoenflies.Plane → Y, ContinuousOn G' D ∧ _root_.Set.MapsTo G' D (B J) ∧ _root_.Set.EqOn G' F J := by
        rcases isPreconnected_iff_subset_of_disjoint.mp hintconn U V hU hV (hintsub.trans hcover)
            (hUVdisj U V _ hUV (interior_subset.trans hDP)) with hsub | hsub
        · obtain ⟨G', h1, h2, h3⟩ := hfillW J (hSC hJC) F hFD (by
            rw [hDeq]
            intro x hx
            by_cases hxi : x ∈ interior D
            · exact hFU ⟨hsub hxi, hDP hx⟩
            · exact (hBJ (hFJ (hmemJ x hx hxi))).1) hFJ
          exact ⟨G', hDeq ▸ h1, hDeq ▸ h2, h3⟩
        · obtain ⟨G', h1, h2, h3⟩ := hfillR J (hSC hJC) F hFD (by
            rw [hDeq]
            intro x hx
            by_cases hxi : x ∈ interior D
            · exact hFV ⟨hsub hxi, hDP hx⟩
            · exact (hBJ (hFJ (hmemJ x hx hxi))).2) hFJ
          exact ⟨G', hDeq ▸ h1, hDeq ▸ h2, h3⟩
      set S' := S \ {J} with hS'def
      have hS'fin : S'.Finite := hSfin.subset _root_.Set.sdiff_subset
      have hZ : IsClosed ((⋃₀ S') ∪ (interior P)ᶜ) := by
        refine IsClosed.union ?_ isOpen_interior.isClosed_compl
        rw [_root_.Set.sUnion_eq_biUnion]
        exact hS'fin.isClosed_biUnion fun c hc => (hS c hc.1).isPolyhedron.isClosed
      have hJZ : Disjoint J ((⋃₀ S') ∪ (interior P)ᶜ) := by
        rw [_root_.Set.disjoint_union_right, _root_.Set.disjoint_sUnion_right]
        refine ⟨fun c hc => hSdisj hJC hc.1 (Ne.symm hc.2), ?_⟩
        exact disjoint_compl_right_iff_subset.mpr (hSP J hJC)
      obtain ⟨N, hN, hJN, hNZ, hNconn⟩ := exists_isOpen_isConnected_sdiff_closure_inside hJj hZ hJZ
      rw [hDeq] at hNconn
      have hNP : N ⊆ interior P := fun x hx => by
        by_contra h
        exact disjoint_left.mp hNZ hx (Or.inr h)
      have hNsub : N \ D ⊆ P \ ⋃₀ S := by
        rintro x ⟨hxN, hxD⟩
        refine ⟨interior_subset (hNP hxN), ?_⟩
        rintro ⟨c, hc, hxc⟩
        by_cases hcJ : c = J
        · subst hcJ
          exact hxD (hJD hxc)
        · exact disjoint_left.mp hNZ hxN (Or.inl ⟨c, ⟨hc, hcJ⟩, hxc⟩)
      let F' : Schoenflies.Plane → Y := D.piecewise G' F
      have hF'D : _root_.Set.EqOn F' G' D := fun x hx => D.piecewise_eq_of_mem _ _ hx
      have hF'nD : ∀ x, x ∉ D → F' x = F x := fun x hx => D.piecewise_eq_of_notMem _ _ hx
      have hF'out : _root_.Set.EqOn F' F (P \ interior D) := by
        intro x hx
        by_cases hxD : x ∈ D
        · rw [hF'D hxD]
          exact hG'eq (hmemJ x hxD hx.2)
        · exact hF'nD x hxD
      have hF'c : ContinuousOn F' P := by
        have h1 : ContinuousOn F' (P \ interior D) := (hF.mono _root_.Set.sdiff_subset).congr hF'out
        have h2 : ContinuousOn F' D := hG'c.congr hF'D
        refine (h1.union_of_isClosed h2 (hP.isPolyhedron.isClosed.sdiff isOpen_interior)
          hDclosed).mono fun x hx => ?_
        by_cases hxi : x ∈ interior D
        · exact Or.inr (interior_subset hxi)
        · exact Or.inl ⟨hx, hxi⟩
      have hfrontD : Disjoint (frontier P) D := by
        rw [_root_.Set.disjoint_left]
        intro x hx hxD
        exact hx.2 (hDint hxD)
      have hF'front : _root_.Set.EqOn F' F (frontier P) := fun x hx =>
        hF'out ⟨hfrontP hx, fun hxi => disjoint_left.mp hfrontD hx (interior_subset hxi)⟩
      have hF'B : ∀ c ∈ S', _root_.Set.MapsTo F' c (B c) := by
        intro c hc x hx
        have hxD : x ∉ D := disjoint_left.mp (hDother c hc.1 hc.2) hx
        rw [hF'nD x hxD]
        exact hFB c hc.1 hx
      have hcoverJ : ∀ x ∈ P \ ⋃₀ S', x ∉ J → x ∉ interior D → x ∈ (U ∪ V) \ D := by
        intro x hx hxJ hxi
        have hxD : x ∉ D := fun hxD => hxJ (hmemJ x hxD hxi)
        refine ⟨hcover ⟨hx.1, fun hxC => ?_⟩, hxD⟩
        obtain ⟨c, hc, hxc⟩ := hxC
        by_cases hcJ : c = J
        · subst hcJ
          exact hxJ hxc
        · exact hx.2 ⟨c, ⟨hc, hcJ⟩, hxc⟩
      obtain ⟨U', V', hU', hV', hUV', hcover', hFU', hFV', hfront'⟩ :
          ∃ U' V' : Set Schoenflies.Plane, IsOpen U' ∧ IsOpen V' ∧ Disjoint (U' ∩ P) (V' ∩ P) ∧
            P \ ⋃₀ S' ⊆ U' ∪ V' ∧ _root_.Set.MapsTo F' (U' ∩ P) XW ∧ _root_.Set.MapsTo F' (V' ∩ P) XR ∧
            frontier P ⊆ U' := by
        rcases isPreconnected_iff_subset_of_disjoint.mp hNconn.isPreconnected U V hU hV
            (hNsub.trans hcover) (hUVdisj U V _ hUV fun x hx => interior_subset (hNP hx.1))
          with hNU | hNV
        · refine ⟨U ∪ N ∪ interior D, V \ D, (hU.union hN).union isOpen_interior,
            hV.sdiff hDclosed, ?_, ?_, ?_, ?_, fun x hx => hfront hx |> Or.inl |> Or.inl⟩
          · rw [_root_.Set.disjoint_left]
            rintro x ⟨(hxU | hxN) | hxi, hxP⟩ ⟨⟨hxV, hxD⟩, -⟩
            · exact disjoint_left.mp hUV ⟨hxU, hxP⟩ ⟨hxV, hxP⟩
            · exact disjoint_left.mp hUV ⟨hNU ⟨hxN, hxD⟩, hxP⟩ ⟨hxV, hxP⟩
            · exact hxD (interior_subset hxi)
          · intro x hx
            by_cases hxJ : x ∈ J
            · exact Or.inl (Or.inl (Or.inr (hJN hxJ)))
            by_cases hxi : x ∈ interior D
            · exact Or.inl (Or.inr hxi)
            obtain ⟨hxUV, hxD⟩ := hcoverJ x hx hxJ hxi
            rcases hxUV with hxU | hxV
            · exact Or.inl (Or.inl (Or.inl hxU))
            · exact Or.inr ⟨hxV, hxD⟩
          · rintro x ⟨hxU', hxP⟩
            by_cases hxD : x ∈ D
            · rw [hF'D hxD]
              exact (hBJ (hG'B hxD)).1
            · rw [hF'nD x hxD]
              rcases hxU' with (hxU | hxN) | hxi
              · exact hFU ⟨hxU, hxP⟩
              · exact hFU ⟨hNU ⟨hxN, hxD⟩, hxP⟩
              · exact absurd (interior_subset hxi) hxD
          · rintro x ⟨⟨hxV, hxD⟩, hxP⟩
            rw [hF'nD x hxD]
            exact hFV ⟨hxV, hxP⟩
        · refine ⟨U \ D, V ∪ N ∪ interior D, hU.sdiff hDclosed,
            (hV.union hN).union isOpen_interior, ?_, ?_, ?_, ?_, ?_⟩
          · rw [_root_.Set.disjoint_left]
            rintro x ⟨⟨hxU, hxD⟩, hxP⟩ ⟨(hxV | hxN) | hxi, -⟩
            · exact disjoint_left.mp hUV ⟨hxU, hxP⟩ ⟨hxV, hxP⟩
            · exact disjoint_left.mp hUV ⟨hxU, hxP⟩ ⟨hNV ⟨hxN, hxD⟩, hxP⟩
            · exact hxD (interior_subset hxi)
          · intro x hx
            by_cases hxJ : x ∈ J
            · exact Or.inr (Or.inl (Or.inr (hJN hxJ)))
            by_cases hxi : x ∈ interior D
            · exact Or.inr (Or.inr hxi)
            obtain ⟨hxUV, hxD⟩ := hcoverJ x hx hxJ hxi
            rcases hxUV with hxU | hxV
            · exact Or.inl ⟨hxU, hxD⟩
            · exact Or.inr (Or.inl (Or.inl hxV))
          · rintro x ⟨⟨hxU, hxD⟩, hxP⟩
            rw [hF'nD x hxD]
            exact hFU ⟨hxU, hxP⟩
          · rintro x ⟨hxV', hxP⟩
            by_cases hxD : x ∈ D
            · rw [hF'D hxD]
              exact (hBJ (hG'B hxD)).2
            · rw [hF'nD x hxD]
              rcases hxV' with (hxV | hxN) | hxi
              · exact hFV ⟨hxV, hxP⟩
              · exact hFV ⟨hNV ⟨hxN, hxD⟩, hxP⟩
              · exact absurd (interior_subset hxi) hxD
          · intro x hx
            exact ⟨hfront hx, fun hxD => disjoint_left.mp hfrontD hx hxD⟩
      have hn' : S'.ncard = n := by
        rw [hS'def, Set.ncard_sdiff_singleton_of_mem hJC, hn]
        omega
      obtain ⟨G, hGc, hGX, hGeq⟩ := ih S' hn' (sdiff_subset.trans hSC) hS'fin
        (fun c hc => hS c hc.1) (hSdisj.subset _root_.Set.sdiff_subset) (fun c hc => hSP c hc.1)
        F' hF'c hF'B U' V' hU' hV' hUV' hcover' hFU' hFV' hfront'
      exact ⟨G, hGc, hGX, fun x hx => (hGeq hx).trans (hF'front hx)⟩
  exact key _ C rfl subset_rfl hCfin hC hCdisj hCP F hF hFB U V hU hV hUV hcover hFU hFV hfront

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_continuousOn_mapsTo_of_jordan_disk_pasting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_continuousOn_mapsTo_of_jordan_disk_pasting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_continuousOn_mapsTo_of_jordan_disk_pasting ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_continuousOn_mapsTo_of_jordan_disk_pasting

end DifferentialGeometry.Topology.PiecewiseLinear
