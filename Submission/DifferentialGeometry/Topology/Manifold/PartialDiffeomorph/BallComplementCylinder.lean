import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.BallComplement
import Submission.DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric _root_.Manifold
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

private def inwardRadius : PartialDiffeomorph IC IC Cylinder Cylinder ∞ where
  toPartialEquiv := {
    toFun := fun q => (q.1, 2 * (1 - q.2))
    invFun := fun q => (q.1, 1 - q.2 / 2)
    source := _root_.Set.univ
    target := _root_.Set.univ
    map_source' := fun _ _ => trivial
    map_target' := fun _ _ => trivial
    left_inv' := fun q _ => Prod.ext rfl (by dsimp; ring)
    right_inv' := fun q _ => Prod.ext rfl (by dsimp; ring) }
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contMDiff_fst.prodMk
    (contMDiff_const.mul (contMDiff_const.sub contMDiff_snd))).contMDiffOn
  contMDiffOn_invFun := (contMDiff_fst.prodMk
    (contMDiff_const.sub (contMDiff_snd.div_const 2))).contMDiffOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.inwardRadius
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.inwardRadius target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

private def inwardRadialChart (T : PartialDiffeomorph IC (𝓡 3) Cylinder M ∞)
    (v : S2) : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞ :=
  ((spherePolarChart (n := 2) v).symm.trans inwardRadius).trans T

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.inwardRadialChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.inwardRadialChart target :: scope.openDecls } }

private theorem inwardRadialChart_apply
    (T : PartialDiffeomorph IC (𝓡 3) Cylinder M ∞) (v q : S2) (r : ℝ) (hr : 0 < r) :
    inwardRadialChart T v (r • (q : E3)) = T (q, 2 * (1 - r)) := by
  change T ((sphereDirection v (r • (q : E3))), 2 * (1 - ‖r • (q : E3)‖)) = _
  rw [sphereDirection_pos_smul v q hr, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.inwardRadialChart_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.inwardRadialChart_apply target :: scope.openDecls } }

private theorem inwardRadialChart_source
    (T : PartialDiffeomorph IC (𝓡 3) Cylinder M ∞) (v : S2)
    (hT : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ T.source) :
    closedBall (0 : E3) 1 \ _root_.Metric.ball (0 : E3) (1 / 2) ⊆ (inwardRadialChart T v).source := by
  intro z hz
  have hlo : 1 / 2 ≤ ‖z‖ := le_of_not_gt (by simpa only [mem_ball_zero_iff] using hz.2)
  have hhi : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz.1
  refine ⟨⟨?_, _root_.Set.mem_univ _⟩, ?_⟩
  · exact norm_ne_zero_iff.mp (by linarith)
  · change T.source (sphereDirection v z, 2 * (1 - ‖z‖))
    exact hT ⟨mem_univ _, by constructor <;> linarith⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.inwardRadialChart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.inwardRadialChart_source target :: scope.openDecls } }

private theorem inwardRadialChart_sphere
    (T : PartialDiffeomorph IC (𝓡 3) Cylinder M ∞) (v q : S2) :
    inwardRadialChart T v (q : E3) = T (q, 0) := by
  simpa only [one_smul, sub_self, _root_.MulZeroClass.mul_zero] using inwardRadialChart_apply T v q 1 zero_lt_one

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.inwardRadialChart_sphere
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.inwardRadialChart_sphere target :: scope.openDecls } }

private theorem image_ball_of_image_closedBall
    (F : E3 ≃ₘ[ℝ] E3) (hF : F '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1) :
    F '' _root_.Metric.ball (0 : E3) 1 = _root_.Metric.ball (0 : E3) 1 := by
  have h := congrArg interior hF
  change interior (F.toHomeomorph '' _root_.Metric.closedBall (0 : E3) 1) = interior (_root_.Metric.closedBall (0 : E3) 1) at h
  rw [← F.toHomeomorph.image_interior, interior_closedBall _ one_ne_zero] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.image_ball_of_image_closedBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.image_ball_of_image_closedBall target :: scope.openDecls } }

private theorem image_sphere_of_image_closedBall
    (F : E3 ≃ₘ[ℝ] E3) (hF : F '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1) :
    F '' _root_.Metric.sphere (0 : E3) 1 = _root_.Metric.sphere (0 : E3) 1 := by
  have h := congrArg frontier hF
  change frontier (F.toHomeomorph '' _root_.Metric.closedBall (0 : E3) 1) = frontier (_root_.Metric.closedBall (0 : E3) 1) at h
  rw [← F.toHomeomorph.image_frontier, frontier_closedBall _ one_ne_zero] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.image_sphere_of_image_closedBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.image_sphere_of_image_closedBall target :: scope.openDecls } }

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z] [T2Space Z] [CompactSpace Z]
  [T2Space M]

theorem exists_ball_complement_chart_of_ball_complement_and_cylinder
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (T : PartialDiffeomorph IC (𝓡 3) Cylinder M ∞)
    (hb : _root_.Metric.closedBall (0 : E3) 1 ⊆ b.source)
    (hP : (b '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ P.source)
    (hT : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ T.source)
    (hboundary : P '' (b '' _root_.Metric.sphere (0 : E3) 1) = _root_.Set.range (fun q : S2 => T (q, 0)))
    (hside : ∀ q : S2, ∀ a ∈ _root_.Set.Icc (0 : ℝ) 1,
      T (q, a) ∈ P '' (b '' _root_.Metric.ball (0 : E3) 1)ᶜ → a = 0) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞,
      ∃ F : E3 ≃ₘ[ℝ] E3,
        F '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1 ∧
        ((b ∘ F) '' _root_.Metric.ball (0 : E3) (1 / 2))ᶜ ⊆ B.source ∧
        B '' ((b ∘ F) '' _root_.Metric.ball (0 : E3) (1 / 2))ᶜ =
          P '' (b '' _root_.Metric.ball (0 : E3) 1)ᶜ ∪ T '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
        _root_.Set.EqOn B P (b '' _root_.Metric.ball (0 : E3) 1)ᶜ ∧
        (∀ q : S2, ∀ a ∈ _root_.Set.Icc (0 : ℝ) 1,
          B (b (F ((1 - a / 2) • (q : E3)))) = T (q, a)) ∧
        ∃ V : Set Cylinder, IsOpen V ∧ _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ V ∧
          EqOn (fun q => B (b (F ((1 - q.2 / 2) • (q.1 : E3))))) T V := by
  let K : Set Z := (b '' _root_.Metric.ball (0 : E3) 1)ᶜ
  have hKc : IsCompact K :=
    (b.toOpenPartialHomeomorph.isOpen_image_of_subset_source _root_.Metric.isOpen_ball
      (ball_subset_closedBall.trans hb)).isClosed_compl.isCompact
  have hbs : _root_.Metric.sphere (0 : E3) 1 ⊆ b.source := sphere_subset_closedBall.trans hb
  have hbsK : b '' _root_.Metric.sphere (0 : E3) 1 ⊆ K := by
    rintro y ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
    have hwz := b.injOn (hb (_root_.Metric.ball_subset_closedBall hw)) (hbs hz) heq
    subst w
    exact (ne_of_lt hw) hz
  let v : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let R := inwardRadialChart T v
  let L : Set E3 := _root_.Metric.closedBall (0 : E3) 1 \ _root_.Metric.ball (0 : E3) (1 / 2)
  have hLc : IsCompact L := (_root_.ProperSpace.isCompact_closedBall _ _).diff _root_.Metric.isOpen_ball
  have hRL : L ⊆ R.source := inwardRadialChart_source T v hT
  have hLs : _root_.Metric.sphere (0 : E3) 1 ⊆ L := by
    intro z hz
    refine ⟨sphere_subset_closedBall hz, ?_⟩
    rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hz]
    norm_num
  have hRsource : _root_.Metric.sphere (0 : E3) 1 ⊆ R.source := hLs.trans hRL
  have hRs (q : S2) : R q = T (q, 0) := inwardRadialChart_sphere T v q
  have hboundaryR : R '' _root_.Metric.sphere (0 : E3) 1 = P '' (b '' _root_.Metric.sphere (0 : E3) 1) := by
    rw [hboundary]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, (hRs ⟨z, hz⟩).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.property, hRs q⟩
  let H₀ := (R.trans P.symm).trans b.symm
  let H := DifferentialGeometry.Topology.PartialDiffeomorph.restrict H₀
    {z | (1 / 2 : ℝ) < ‖z‖} (isOpen_lt continuous_const continuous_norm)
  have hHs : _root_.Metric.sphere (0 : E3) 1 ⊆ H.source := by
    intro z hz
    obtain ⟨_, ⟨w, hw, rfl⟩, heq⟩ := hboundaryR ▸ _root_.Set.mem_image_of_mem R hz
    have hbsP := hP (hbsK (_root_.Set.mem_image_of_mem b hw))
    refine ⟨⟨⟨hRsource hz, ?_⟩, ?_⟩, ?_⟩
    · change R z ∈ P.target
      exact heq ▸ P.map_source hbsP
    · change P.symm (R z) ∈ b.target
      rw [← heq]
      have hp : P.symm (P (b w)) = b w := P.left_inv' hbsP
      rw [hp]
      exact b.map_source (hbs hw)
    · change 1 / 2 < ‖z‖
      rw [mem_sphere_zero_iff_norm.mp hz]
      norm_num
  have hHimage : H '' _root_.Metric.sphere (0 : E3) 1 = _root_.Metric.sphere (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨_, ⟨w, hw, rfl⟩, heq⟩ := hboundaryR ▸ _root_.Set.mem_image_of_mem R hz
      have hp : P.symm (P (b w)) = b w := P.left_inv' (hP (hbsK (_root_.Set.mem_image_of_mem b hw)))
      have hb' : b.symm (b w) = w := b.left_inv' (hbs hw)
      change b.symm (P.symm (R z)) ∈ _root_.Metric.sphere 0 1
      rw [← heq, hp, hb']
      exact hw
    · intro hy
      obtain ⟨z, hz, heq⟩ := hboundaryR.symm ▸ _root_.Set.mem_image_of_mem P (_root_.Set.mem_image_of_mem b hy)
      refine ⟨z, hz, ?_⟩
      change b.symm (P.symm (R z)) = y
      rw [heq]
      have hp : P.symm (P (b y)) = b y := P.left_inv' (hP (hbsK (_root_.Set.mem_image_of_mem b hy)))
      rw [hp]
      exact b.left_inv' (hbs hy)
  have hHmap : _root_.Set.MapsTo H (_root_.Metric.closedBall (0 : E3) 1 ∩ H.source) (_root_.Metric.closedBall (0 : E3) 1) := by
    intro z hz
    have htP : R z ∈ P.target := hz.2.1.1.2
    have htb : P.symm (R z) ∈ b.target := hz.2.1.2
    have hHs' : H z ∈ b.source := b.map_target htb
    have heq : P (b (H z)) = R z := by
      change P (b (b.symm (P.symm (R z)))) = R z
      have hb' : b (b.symm (P.symm (R z))) = P.symm (R z) := b.right_inv' htb
      rw [hb']
      exact P.right_inv' htP
    rw [mem_closedBall_zero_iff]
    by_contra! hgt
    have hnot : b (H z) ∈ K := by
      rintro ⟨w, hw, heq'⟩
      have hwz := b.injOn (hb (_root_.Metric.ball_subset_closedBall hw)) hHs' heq'
      have hn := mem_ball_zero_iff.mp hw
      rw [hwz] at hn
      linarith
    have hr : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz.1
    have hl : 1 / 2 < ‖z‖ := hz.2.2
    have ha : 2 * (1 - ‖z‖) ∈ _root_.Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
    have hcore : T (sphereDirection v z, 2 * (1 - ‖z‖)) ∈ P '' K :=
      ⟨b (H z), hnot, heq⟩
    have hzero := hside (sphereDirection v z) (2 * (1 - ‖z‖)) ha hcore
    have hzs : z ∈ _root_.Metric.sphere (0 : E3) 1 := mem_sphere_zero_iff_norm.mpr (by linarith)
    have hHsz : H z ∈ _root_.Metric.sphere (0 : E3) 1 := hHimage ▸ _root_.Set.mem_image_of_mem H hzs
    rw [mem_sphere_zero_iff_norm] at hHsz
    linarith
  obtain ⟨F, hFball, V, hVo, hSV, hVH, hFH⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph H hHs hHimage hHmap
  have hFopen := image_ball_of_image_closedBall F hFball
  have hFsphere := image_sphere_of_image_closedBall F hFball
  let Q := (b.symm.trans F.symm.toPartialDiffeomorph).trans R
  let J : Set Z := (b ∘ F) '' L
  have hJc : IsCompact J := by
    apply hLc.image_of_continuousOn
    exact (b.contMDiffOn_toFun.comp F.contMDiff.contMDiffOn
      (fun z hz => hb (hFball ▸ _root_.Set.mem_image_of_mem F hz.1))).continuousOn
  have hJs : J ⊆ Q.source := by
    rintro y ⟨z, hz, rfl⟩
    have hFb : F z ∈ b.source := hb (hFball ▸ _root_.Set.mem_image_of_mem F hz.1)
    have hb' : b.symm (b (F z)) = F z := b.left_inv' hFb
    refine ⟨⟨b.map_source hFb, _root_.Set.mem_univ _⟩, ?_⟩
    change R.source (F.symm (b.symm (b (F z))))
    rw [hb', F.symm_apply_apply]
    exact hRL hz
  have hQ (z : E3) (hz : z ∈ L) : Q (b (F z)) = R z := by
    change R (F.symm (b.symm (b (F z)))) = R z
    have hb' : b.symm (b (F z)) = F z := b.left_inv' (hb (hFball ▸ _root_.Set.mem_image_of_mem F hz.1))
    rw [hb', F.symm_apply_apply]
  have hseam : K ∩ J = b '' _root_.Metric.sphere (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨hy, z, hz, rfl⟩
      refine ⟨F z, ?_, rfl⟩
      have hFz : F z ∈ _root_.Metric.closedBall (0 : E3) 1 := hFball ▸ _root_.Set.mem_image_of_mem F hz.1
      exact le_antisymm hFz (not_lt.mp fun hh => hy ⟨F z, hh, rfl⟩)
    · rintro ⟨z, hz, rfl⟩
      refine ⟨hbsK (_root_.Set.mem_image_of_mem b hz), ?_⟩
      obtain ⟨w, hw, rfl⟩ := hFsphere.symm ▸ hz
      exact ⟨w, hLs hw, rfl⟩
  let O : Set Z := b '' (F '' V)
  have hFbV : F '' V ⊆ b.source := by
    rintro z ⟨w, hw, rfl⟩
    rw [hFH hw]
    exact b.map_target (hVH hw).1.2
  have hOo : IsOpen O := b.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (F.toHomeomorph.isOpenMap V hVo) hFbV
  have hSO : b '' _root_.Metric.sphere (0 : E3) 1 ⊆ O := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hFsphere.symm ▸ hz
    exact ⟨F w, ⟨w, hSV hw, rfl⟩, rfl⟩
  have hPQ : _root_.Set.EqOn P Q O := by
    rintro y ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hb' : b.symm (b (F z)) = F z := b.left_inv' (hFbV ⟨z, hz, rfl⟩)
    change P (b (F z)) = R (F.symm (b.symm (b (F z))))
    rw [hb', F.symm_apply_apply, hFH hz]
    change P (b (b.symm (P.symm (R z)))) = R z
    have hbb : b (b.symm (P.symm (R z))) = P.symm (R z) := b.right_inv' (hVH hz).1.2
    rw [hbb]
    exact P.right_inv' (hVH hz).1.1.2
  have hinter : P '' K ∩ Q '' J ⊆ P '' (K ∩ J) := by
    rintro y ⟨hy, _, ⟨z, hz, rfl⟩, rfl⟩
    change Q (b (F z)) ∈ P '' K at hy
    change Q (b (F z)) ∈ P '' (K ∩ J)
    rw [hQ z hz] at hy ⊢
    have hlo : 1 / 2 ≤ ‖z‖ := le_of_not_gt (by simpa only [mem_ball_zero_iff] using hz.2)
    have hhi : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz.1
    have ha : 2 * (1 - ‖z‖) ∈ _root_.Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
    have hzero := hside (sphereDirection v z) (2 * (1 - ‖z‖)) ha hy
    have hzs : z ∈ _root_.Metric.sphere (0 : E3) 1 := mem_sphere_zero_iff_norm.mpr (by linarith)
    rw [hseam]
    exact hboundaryR ▸ _root_.Set.mem_image_of_mem R hzs
  obtain ⟨B, O₀, O₁, _, hO₁o, hKO, hJO, hBO, hBP, hBQ⟩ :=
    PartialDiffeomorph.exists_eqOn_neighborhoods_of_isCompact P Q hKc hJc hP hJs
      hOo (hseam ▸ hSO) hPQ hinter
  have hcover : K ∪ J = ((b ∘ F) '' _root_.Metric.ball (0 : E3) (1 / 2))ᶜ := by
    ext y
    constructor
    · rintro (hy | ⟨z, hz, rfl⟩) ⟨w, hw, heq⟩
      · exact hy ⟨F w, hFopen ▸ _root_.Set.mem_image_of_mem F (_root_.Metric.ball_subset_ball (by norm_num) hw), heq⟩
      · have hwb : F w ∈ b.source := hb (hFball ▸ _root_.Set.mem_image_of_mem F
          (_root_.Metric.ball_subset_closedBall (_root_.Metric.ball_subset_ball (by norm_num) hw)))
        have hzb : F z ∈ b.source := hb (hFball ▸ _root_.Set.mem_image_of_mem F hz.1)
        have hwz : w = z := F.injective (b.injOn hwb hzb heq)
        exact hz.2 (hwz ▸ hw)
    · intro hy
      by_cases hyK : y ∈ K
      · exact Or.inl hyK
      · have hymem : y ∈ b '' _root_.Metric.ball (0 : E3) 1 := not_not.mp hyK
        obtain ⟨z, hz, rfl⟩ := hymem
        obtain ⟨w, hw, rfl⟩ := hFopen.symm ▸ hz
        refine Or.inr ⟨w, ⟨ball_subset_closedBall hw, ?_⟩, rfl⟩
        exact fun hh => hy ⟨w, hh, rfl⟩
  have hBsource : ((b ∘ F) '' _root_.Metric.ball (0 : E3) (1 / 2))ᶜ ⊆ B.source := by
    rw [← hcover]
    exact (_root_.Set.union_subset_union hKO hJO).trans hBO
  have hBT (q : S2) (a : ℝ) (ha : a ∈ _root_.Set.Icc (0 : ℝ) 1) :
      B (b (F ((1 - a / 2) • (q : E3)))) = T (q, a) := by
    have hr : 0 < 1 - a / 2 := by linarith [ha.2]
    have hn : ‖(1 - a / 2) • (q : E3)‖ = 1 - a / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
    have hzL : (1 - a / 2) • (q : E3) ∈ L := by
      constructor
      · rw [mem_closedBall_zero_iff, hn]; linarith [ha.1]
      · rw [mem_ball_zero_iff, hn]; linarith [ha.2]
    have hm : b (F ((1 - a / 2) • (q : E3))) ∈ O₁ := hJO ⟨_, hzL, rfl⟩
    rw [hBQ hm, hQ _ hzL]
    have he := inwardRadialChart_apply T v q (1 - a / 2) hr
    have hh : 2 * (1 - (1 - a / 2)) = a := by ring
    simpa only [hh] using he
  have hBimage : B '' ((b ∘ F) '' _root_.Metric.ball (0 : E3) (1 / 2))ᶜ =
      P '' K ∪ T '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    rw [← hcover, _root_.Set.image_union]
    have hBiK : B '' K = P '' K := _root_.Set.image_congr (fun z hz => hBP (hKO hz))
    rw [hBiK]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      change B (b (F z)) ∈ _
      have hm : b (F z) ∈ O₁ := hJO ⟨z, hz, rfl⟩
      rw [hBQ hm, hQ z hz]
      have hlo : 1 / 2 ≤ ‖z‖ := le_of_not_gt (by simpa only [mem_ball_zero_iff] using hz.2)
      have hhi : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz.1
      exact ⟨(sphereDirection v z, 2 * (1 - ‖z‖)),
        ⟨mem_univ _, by constructor <;> linarith⟩, rfl⟩
    · rintro ⟨⟨q, a⟩, ha, rfl⟩
      have hr : 0 < 1 - a / 2 := by linarith [ha.2.2]
      have hn : ‖(1 - a / 2) • (q : E3)‖ = 1 - a / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
      refine ⟨b (F ((1 - a / 2) • (q : E3))), ⟨_, ?_, rfl⟩, hBT q a ha.2⟩
      constructor
      · rw [mem_closedBall_zero_iff, hn]; linarith [ha.2.1]
      · rw [mem_ball_zero_iff, hn]; linarith [ha.2.2]
  refine ⟨B, F, hFball, hBsource, hBimage, fun z hz => hBP (hKO hz), hBT, ?_⟩
  let f : Cylinder → Z := fun q => b (F ((1 - q.2 / 2) • (q.1 : E3)))
  let A₀ : Set Cylinder := {q | F ((1 - q.2 / 2) • (q.1 : E3)) ∈ b.source}
  have hc : ContinuousOn f A₀ := by
    exact b.contMDiffOn_toFun.continuousOn.comp
      (F.continuous.comp ((continuous_const.sub (continuous_snd.div_const 2)).smul
        (continuous_subtype_val.comp continuous_fst))).continuousOn (fun _ h => h)
  have hA₀o : IsOpen A₀ :=
    b.open_source.preimage (F.continuous.comp
      ((continuous_const.sub (continuous_snd.div_const 2)).smul
        (continuous_subtype_val.comp continuous_fst)))
  let W : Set Cylinder := {q | q.2 < 2} ∩ (A₀ ∩ f ⁻¹' O₁)
  have hWo : IsOpen W :=
    (isOpen_lt continuous_snd continuous_const).inter (hc.isOpen_inter_preimage hA₀o hO₁o)
  have hW : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ W := by
    intro q hq
    have hr : 0 < 1 - q.2 / 2 := by linarith [hq.2.2]
    have hn : ‖(1 - q.2 / 2) • (q.1 : E3)‖ = 1 - q.2 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
    have hzL : (1 - q.2 / 2) • (q.1 : E3) ∈ L := by
      constructor
      · rw [mem_closedBall_zero_iff, hn]; linarith [hq.2.1]
      · rw [mem_ball_zero_iff, hn]; linarith [hq.2.2]
    have hm : b (F ((1 - q.2 / 2) • (q.1 : E3))) ∈ J := ⟨_, hzL, rfl⟩
    exact ⟨by change q.2 < 2; linarith [hq.2.2],
      hb (hFball ▸ _root_.Set.mem_image_of_mem F hzL.1), hJO hm⟩
  refine ⟨W, hWo, hW, ?_⟩
  intro q hq
  have hr : 0 < 1 - q.2 / 2 := by have h := hq.1; change q.2 < 2 at h; linarith
  have hbb : b.symm (b (F ((1 - q.2 / 2) • (q.1 : E3)))) =
      F ((1 - q.2 / 2) • (q.1 : E3)) := b.left_inv' hq.2.1
  have hm : b (F ((1 - q.2 / 2) • (q.1 : E3))) ∈ O₁ := hq.2.2
  change B (b (F ((1 - q.2 / 2) • (q.1 : E3)))) = T q
  rw [hBQ hm]
  change R (F.symm (b.symm (b (F ((1 - q.2 / 2) • (q.1 : E3)))))) = T q
  rw [hbb, F.symm_apply_apply]
  have he := inwardRadialChart_apply T v q.1 (1 - q.2 / 2) hr
  have hh : 2 * (1 - (1 - q.2 / 2)) = q.2 := by ring
  simpa only [hh] using he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_ball_complement_chart_of_ball_complement_and_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_ball_complement_chart_of_ball_complement_and_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_ball_complement_chart_of_ball_complement_and_cylinder ``Submission.DifferentialGeometry.Topology.Manifold.exists_ball_complement_chart_of_ball_complement_and_cylinder

end DifferentialGeometry.Topology.Manifold
