import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CylinderBoundary
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CapAnnulus
import Submission.DifferentialGeometry.Topology.Diffeomorph.SphereGermExtension
import Submission.DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "Cylinder" => S2 × ℝ

private instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

private def axialTranslate (L : ℝ) :
    PartialDiffeomorph IC IC Cylinder Cylinder ∞ where
  toPartialEquiv := {
    toFun := fun q => (q.1, q.2 - L)
    invFun := fun q => (q.1, q.2 + L)
    source := _root_.Set.univ
    target := _root_.Set.univ
    map_source' := fun _ _ => trivial
    map_target' := fun _ _ => trivial
    left_inv' := fun _ _ => by simp
    right_inv' := fun _ _ => by simp }
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)).contMDiffOn
  contMDiffOn_invFun := (contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const)).contMDiffOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.axialTranslate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.axialTranslate target :: scope.openDecls } }

@[simp] private theorem axialTranslate_apply (L : ℝ) (q : Cylinder) :
    axialTranslate L q = (q.1, q.2 - L) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.axialTranslate_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.axialTranslate_apply target :: scope.openDecls } }

private def capTubeRadialAnnulusChart (T : PartialDiffeomorph IC (𝓡 3) Cylinder M ∞)
    (v : S2) (L : ℝ) :
    PartialDiffeomorph 𝓘(ℝ, E3) (𝓡 3) E3 M ∞ :=
  ((spherePolarChart (n := 2) v).symm.trans (axialTranslate L)).trans T

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.capTubeRadialAnnulusChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.capTubeRadialAnnulusChart target :: scope.openDecls } }

private theorem capTubeRadialAnnulusChart_source_mem
    (T : PartialDiffeomorph IC (𝓡 3) Cylinder M ∞) (v : S2) (L r : ℝ) (z : S2)
    (hr : 0 < r) (hT : (z, r - L) ∈ T.source) :
    r • (z : E3) ∈ (capTubeRadialAnnulusChart T v L).source := by
  refine ⟨⟨smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere z), _root_.Set.mem_univ _⟩, ?_⟩
  change (axialTranslate L) ((spherePolarChart (n := 2) v).symm (r • (z : E3))) ∈ T.source
  rw [spherePolarChart_symm_apply, sphereDirection_pos_smul v z hr,
    axialTranslate_apply]
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one] using hT

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.capTubeRadialAnnulusChart_source_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.capTubeRadialAnnulusChart_source_mem target :: scope.openDecls } }

private theorem capTubeRadialAnnulusChart_apply
    (T : PartialDiffeomorph IC (𝓡 3) Cylinder M ∞) (v : S2) (L r : ℝ) (z : S2)
    (hr : 0 < r) :
    capTubeRadialAnnulusChart T v L (r • (z : E3)) = T (z, r - L) := by
  change T ((axialTranslate L) ((spherePolarChart (n := 2) v).symm (r • (z : E3)))) = _
  rw [spherePolarChart_symm_apply, sphereDirection_pos_smul v z hr,
    axialTranslate_apply]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.capTubeRadialAnnulusChart_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.capTubeRadialAnnulusChart_apply target :: scope.openDecls } }

theorem exists_ball_chart_of_ball_and_cylinder_eqOn_neighborhoods [T2Space M]
    (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (T : PartialDiffeomorph IC (𝓡 3) Cylinder M ∞)
    (hA : Metric.closedBall (0 : E3) 1 ⊆ A.source)
    (hT : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ T.source)
    (hboundary : A '' Metric.sphere (0 : E3) 1 = _root_.Set.range (fun q : S2 => T (q, 0)))
    (hside : ∀ q : S2, ∀ a ∈ _root_.Set.Icc (0 : ℝ) 1,
      T (q, a) ∈ A '' Metric.closedBall (0 : E3) 1 → a = 0) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      Metric.closedBall (0 : E3) 1 ⊆ B.source ∧
      B '' Metric.closedBall (0 : E3) 1 = A '' Metric.closedBall (0 : E3) 1 ∪ T '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      ∃ F : E3 ≃ₘ⟮(𝓡 3), (𝓡 3)⟯ E3,
        F '' Metric.closedBall (0 : E3) 1 = Metric.closedBall (0 : E3) 1 ∧
        (∀ z ∈ Metric.closedBall (0 : E3) 1, B ((1 / 2 : ℝ) • z) = A (F z)) ∧
        (∀ q : S2, ∀ a ∈ _root_.Set.Icc (0 : ℝ) 1,
          B (((a + 1) / 2) • (q : E3)) = T (q, a)) ∧
        ∃ V : Set Cylinder, IsOpen V ∧ _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ V ∧
          EqOn (fun q => B (((q.2 + 1) / 2) • (q.1 : E3))) T V := by
  let _ : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  let v : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let R := capTubeRadialAnnulusChart T v 1
  have hRformula (z : E3) : R z = T (sphereDirection v z, ‖z‖ - 1) := rfl
  have hRsphere (q : S2) : R (q : E3) = T (q, 0) := by
    have he := capTubeRadialAnnulusChart_apply T v 1 1 q zero_lt_one
    simpa only [one_smul, sub_self] using he
  have hRsource : Metric.closedBall (0 : E3) 2 \ Metric.ball (0 : E3) 1 ⊆ R.source := by
    intro z hz
    have hlo : 1 ≤ ‖z‖ := le_of_not_gt (by simpa only [mem_ball_zero_iff] using hz.2)
    have hhi : ‖z‖ ≤ 2 := mem_closedBall_zero_iff.mp hz.1
    have hn : z ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖z‖ ≠ 0)
    have he := capTubeRadialAnnulusChart_source_mem T v 1 ‖z‖
      (sphereDirection v z) (by linarith) (hT ⟨mem_univ _, by constructor <;> linarith⟩)
    simpa only [norm_smul_sphereDirection v hn] using he
  have hRsrcS : Metric.sphere (0 : E3) 1 ⊆ R.source := by
    intro z hz
    exact hRsource ⟨Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall hz),
      by simp only [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hz, lt_self_iff_false, not_false_eq_true]⟩
  obtain ⟨η, hη, hηi⟩ := exists_sphere_diffeomorph_of_sphere_chart_and_cylinder_boundary
    A T (Metric.sphere_subset_closedBall.trans hA)
    (fun q => hT ⟨mem_univ _, le_rfl, zero_le_one⟩) hboundary
  have himages : A '' Metric.sphere (0 : E3) 1 = R '' Metric.sphere (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨η.symm ⟨z, hz⟩, (η.symm ⟨z, hz⟩).property,
        (hRsphere _).trans (hηi ⟨z, hz⟩)⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨η ⟨z, hz⟩, (η ⟨z, hz⟩).property,
        (hη ⟨z, hz⟩).trans (hRsphere ⟨z, hz⟩).symm⟩
  let R₀ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict R
    (Metric.ball (0 : E3) 2) Metric.isOpen_ball
  let H := A.trans R₀.symm
  have hRs0 (z : E3) (hz : z ∈ Metric.sphere (0 : E3) 1) : z ∈ R₀.source :=
    ⟨hRsrcS hz, by rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hz]; norm_num⟩
  have hHs : Metric.sphere (0 : E3) 1 ⊆ H.source := by
    intro z hz
    refine ⟨hA (Metric.sphere_subset_closedBall hz), ?_⟩
    obtain ⟨w, hw, heq⟩ := himages ▸ _root_.Set.mem_image_of_mem A hz
    change A z ∈ R₀.target
    have ht : R w ∈ R₀.target := R₀.map_source (hRs0 w hw)
    exact heq ▸ ht
  have hHimage : H '' Metric.sphere (0 : E3) 1 = Metric.sphere (0 : E3) 1 := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨q, hq, heq⟩ := himages ▸ _root_.Set.mem_image_of_mem A hw
      change R₀.symm (A w) ∈ Metric.sphere 0 1
      have hleft : R₀.symm (R q) = q := R₀.left_inv' (hRs0 q hq)
      rw [← heq, hleft]
      exact hq
    · intro hz
      obtain ⟨w, hw, heq⟩ := himages.symm ▸ _root_.Set.mem_image_of_mem R hz
      refine ⟨w, hw, ?_⟩
      change R₀.symm (A w) = z
      rw [heq]
      exact R₀.left_inv' (hRs0 z hz)
  have hHmap : _root_.Set.MapsTo H (Metric.closedBall (0 : E3) 1 ∩ H.source)
      (Metric.closedBall (0 : E3) 1) := by
    intro z hz
    have ht : A z ∈ R₀.target := hz.2.2
    have htarget := R₀.map_target ht
    have hnorm : ‖R₀.symm (A z)‖ < 2 := mem_ball_zero_iff.mp htarget.2
    rw [mem_closedBall_zero_iff]
    change ‖R₀.symm (A z)‖ ≤ 1
    by_contra! hgt
    let q := sphereDirection v (R₀.symm (A z))
    let a := ‖R₀.symm (A z)‖ - 1
    have ha : a ∈ _root_.Set.Icc (0 : ℝ) 1 := by dsimp only [a]; constructor <;> linarith
    have heq : T (q, a) = A z := by
      exact (hRformula (R₀.symm (A z))).symm.trans (R₀.right_inv' ht)
    have hmem : T (q, a) ∈ A '' Metric.closedBall (0 : E3) 1 := by
      rw [heq]
      exact _root_.Set.mem_image_of_mem A hz.1
    have ha0 := hside q a ha hmem
    dsimp only [a] at ha0
    linarith
  obtain ⟨F, hFball, V, hVo, hSV, hVH, hFH⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph H hHs hHimage hHmap
  let C := F.symm.toPartialDiffeomorph.trans A
  have hFinvball : F.symm '' Metric.closedBall (0 : E3) 1 = Metric.closedBall (0 : E3) 1 := by
    calc
      F.symm '' Metric.closedBall (0 : E3) 1 =
          F.symm '' (F '' Metric.closedBall (0 : E3) 1) := congrArg (Set.image F.symm) hFball.symm
      _ = Metric.closedBall (0 : E3) 1 := by
        rw [Set.image_image]
        simp only [F.symm_apply_apply, _root_.Set.image_id']
  have hCs : Metric.closedBall (0 : E3) 1 ⊆ C.source := by
    intro z hz
    refine ⟨mem_univ _, hA ?_⟩
    exact hFinvball ▸ _root_.Set.mem_image_of_mem F.symm hz
  let O := F '' V
  have hOo : IsOpen O := F.toHomeomorph.isOpenMap V hVo
  have hSO : Metric.sphere (0 : E3) 1 ⊆ O := by
    intro z hz
    obtain ⟨w, hw, heq⟩ := hHimage.symm ▸ hz
    exact ⟨w, hSV hw, (hFH (hSV hw)).trans heq⟩
  have hCR : _root_.Set.EqOn C R O := by
    rintro z ⟨w, hw, rfl⟩
    change A (F.symm (F w)) = R (F w)
    rw [F.symm_apply_apply, hFH hw]
    exact (R₀.right_inv' (hVH hw).2).symm
  have hCimage : C '' Metric.closedBall (0 : E3) 1 = A '' Metric.closedBall (0 : E3) 1 := by
    change (A ∘ F.symm) '' Metric.closedBall (0 : E3) 1 = _
    rw [Set.image_comp, hFinvball]
  have hinter : C '' Metric.closedBall (0 : E3) 1 ∩
      R '' (Metric.closedBall (0 : E3) 2 \ Metric.ball (0 : E3) 1) ⊆
      C '' Metric.sphere (0 : E3) 1 := by
    rintro y ⟨hy, z, hz, rfl⟩
    have hlo : 1 ≤ ‖z‖ := le_of_not_gt (by simpa only [mem_ball_zero_iff] using hz.2)
    have hhi : ‖z‖ ≤ 2 := mem_closedBall_zero_iff.mp hz.1
    have ha : ‖z‖ - 1 ∈ _root_.Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
    have hz0 := hside (sphereDirection v z) (‖z‖ - 1) ha (by
      rw [← hRformula, ← hCimage]
      exact hy)
    have hzs : z ∈ Metric.sphere (0 : E3) 1 := mem_sphere_zero_iff_norm.mpr (by linarith)
    exact ⟨z, hzs, hCR (hSO hzs)⟩
  obtain ⟨B, hBs, hBC, hBR, _, V₀, V₁, _, hV₁o, _, hKV₁, _, hBV₁⟩ :=
    exists_ball_chart_of_cap_and_annulus_eqOn_neighborhoods C R
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
    hCs hRsource hOo hSO hCR hinter
  have hcap (z : E3) (hz : z ∈ Metric.closedBall (0 : E3) 1) :
      B ((1 / 2 : ℝ) • z) = A (F.symm z) := by
    have he := hBC z hz
    change B ((2 : ℝ)⁻¹ • z) = A (F.symm z) at he
    simpa using he
  have htube (q : S2) (a : ℝ) (ha : a ∈ _root_.Set.Icc (0 : ℝ) 1) :
      B (((a + 1) / 2) • (q : E3)) = T (q, a) := by
    have hn : ‖(a + 1) • (q : E3)‖ = a + 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [ha.1]), norm_eq_of_mem_sphere, mul_one]
    have he := hBR ((a + 1) • (q : E3)) ⟨by rw [mem_closedBall_zero_iff, hn]; linarith [ha.2],
      by rw [mem_ball_zero_iff, hn]; linarith [ha.1]⟩
    have hscale : (2 : ℝ)⁻¹ • ((a + 1) • (q : E3)) = ((a + 1) / 2) • (q : E3) := by
      rw [smul_smul]; congr 1; ring
    rw [hscale] at he
    exact he.trans (by simpa only [add_sub_cancel_right] using
      capTubeRadialAnnulusChart_apply T v 1 (a + 1) q (by linarith [ha.1]))
  have hneighborhood : ∃ V : Set Cylinder, IsOpen V ∧ _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ V ∧
      EqOn (fun q => B (((q.2 + 1) / 2) • (q.1 : E3))) T V := by
    let V : Set Cylinder := {q | -1 < q.2} ∩
      (fun q : Cylinder => (q.2 + 1) • (q.1 : E3)) ⁻¹' V₁
    have hVo : IsOpen V :=
      (isOpen_lt continuous_const continuous_snd).inter
        (hV₁o.preimage ((continuous_snd.add continuous_const).smul
          (continuous_subtype_val.comp continuous_fst)))
    have hcontains : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ V := by
      intro q hq
      refine ⟨by change -1 < q.2; linarith [hq.2.1], hKV₁ ?_⟩
      have hn : ‖(q.2 + 1) • (q.1 : E3)‖ = q.2 + 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hq.2.1]),
          norm_eq_of_mem_sphere, mul_one]
      constructor
      · rw [mem_closedBall_zero_iff, hn]; linarith [hq.2.2]
      · rw [mem_ball_zero_iff, hn]; linarith [hq.2.1]
    refine ⟨V, hVo, hcontains, ?_⟩
    intro q hq
    have he := hBV₁ hq.2
    change B (2⁻¹ • ((q.2 + 1) • (q.1 : E3))) = R ((q.2 + 1) • (q.1 : E3)) at he
    have hscale : (2 : ℝ)⁻¹ • ((q.2 + 1) • (q.1 : E3)) =
        ((q.2 + 1) / 2) • (q.1 : E3) := by rw [smul_smul]; congr 1; ring
    rw [hscale] at he
    exact he.trans (by
      simpa only [add_sub_cancel_right] using
        capTubeRadialAnnulusChart_apply T v 1 (q.2 + 1) q.1 (by have h := hq.1; change -1 < q.2 at h; linarith))
  refine ⟨B, hBs, ?_, F.symm, hFinvball, hcap, htube, hneighborhood⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hn : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    by_cases hsmall : ‖z‖ ≤ 1 / 2
    · left
      have h2z : (2 : ℝ) • z ∈ Metric.closedBall (0 : E3) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul]; norm_num; linarith
      have hval := hcap ((2 : ℝ) • z) h2z
      simp only [smul_smul] at hval
      norm_num at hval
      rw [hval]
      exact _root_.Set.mem_image_of_mem A (hFinvball ▸ _root_.Set.mem_image_of_mem F.symm h2z)
    · right
      have hpos : 0 < ‖z‖ := by linarith
      let a := 2 * ‖z‖ - 1
      have ha : a ∈ _root_.Set.Icc (0 : ℝ) 1 := by dsimp only [a]; constructor <;> linarith
      have he := htube (sphereDirection v z) a ha
      have hs : ((a + 1) / 2) • (sphereDirection v z : E3) = z := by
        have hh : (a + 1) / 2 = ‖z‖ := by dsimp only [a]; ring
        rw [hh, norm_smul_sphereDirection v (norm_ne_zero_iff.mp hpos.ne')]
      rw [hs] at he
      rw [he]
      exact ⟨(sphereDirection v z, a), ⟨mem_univ _, ha⟩, rfl⟩
  · rintro (hy | hy)
    · obtain ⟨z, hz, rfl⟩ := hy
      refine ⟨(1 / 2 : ℝ) • F z, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff, norm_smul]
        have hfz : ‖F z‖ ≤ 1 := mem_closedBall_zero_iff.mp (hFball ▸ _root_.Set.mem_image_of_mem F hz)
        norm_num
        linarith
      · rw [hcap _ (hFball ▸ _root_.Set.mem_image_of_mem F hz), F.symm_apply_apply]
    · obtain ⟨⟨q, a⟩, ha, rfl⟩ := hy
      refine ⟨((a + 1) / 2) • (q : E3), ?_, htube q a ha.2⟩
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [ha.2.1] : (0 : ℝ) ≤ (a + 1) / 2), norm_eq_of_mem_sphere, mul_one]
      linarith [ha.2.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_ball_and_cylinder_eqOn_neighborhoods then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_ball_and_cylinder_eqOn_neighborhoods"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_ball_and_cylinder_eqOn_neighborhoods ``Submission.DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_ball_and_cylinder_eqOn_neighborhoods

theorem exists_ball_chart_of_ball_and_cylinder [T2Space M]
    (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (T : PartialDiffeomorph IC (𝓡 3) Cylinder M ∞)
    (hA : Metric.closedBall (0 : E3) 1 ⊆ A.source)
    (hT : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ T.source)
    (hboundary : A '' Metric.sphere (0 : E3) 1 = _root_.Set.range (fun q : S2 => T (q, 0)))
    (hside : ∀ q : S2, ∀ a ∈ _root_.Set.Icc (0 : ℝ) 1,
      T (q, a) ∈ A '' Metric.closedBall (0 : E3) 1 → a = 0) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      Metric.closedBall (0 : E3) 1 ⊆ B.source ∧
      B '' Metric.closedBall (0 : E3) 1 = A '' Metric.closedBall (0 : E3) 1 ∪ T '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      ∃ F : E3 ≃ₘ⟮(𝓡 3), (𝓡 3)⟯ E3,
        F '' Metric.closedBall (0 : E3) 1 = Metric.closedBall (0 : E3) 1 ∧
        (∀ z ∈ Metric.closedBall (0 : E3) 1, B ((1 / 2 : ℝ) • z) = A (F z)) ∧
        ∀ q : S2, ∀ a ∈ _root_.Set.Icc (0 : ℝ) 1,
          B (((a + 1) / 2) • (q : E3)) = T (q, a) := by
  obtain ⟨B, hBs, hBU, F, hF, hcore, htube, _⟩ :=
    exists_ball_chart_of_ball_and_cylinder_eqOn_neighborhoods A T hA hT hboundary hside
  exact ⟨B, hBs, hBU, F, hF, hcore, htube⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_ball_and_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_ball_and_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_ball_and_cylinder ``Submission.DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_ball_and_cylinder

end DifferentialGeometry.Topology.Manifold
