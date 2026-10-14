import Submission.DifferentialGeometry.Analysis.Complex.BoundaryUniqueness
import Submission.DifferentialGeometry.Analysis.Complex.RiemannMapping.DiskImage
import Submission.DifferentialGeometry.Analysis.Complex.RiemannMapping.LipschitzExtension
import Submission.DifferentialGeometry.Analysis.Integration.Measure.SmoothNullImage
import Submission.DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk
import Submission.DifferentialGeometry.Analysis.Complex.RiemannMapping.BoundaryModulus
import Submission.DifferentialGeometry.Topology.Homeomorph.ExtensionFibers
import Submission.DifferentialGeometry.Topology.Connected.CircleCaps
import Mathlib.Topology.OpenPartialHomeomorph.Composition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.Metric _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Geometry
open scoped _root_.Topology _root_.ContDiff _root_.NNReal

namespace Complex
open _root_.Complex

open _root_.Complex in
theorem not_constant_on_circle_patch_of_riemann_map_extension
    (W f : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hWsource : W.source = _root_.Metric.ball (0 : ℂ) r)
    (hW : ContDiffOn ℝ 1 W W.source) (hWi : ContDiffOn ℝ 1 W.symm W.target)
    (hfsource : f.source = W '' _root_.Metric.ball (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f f.source)
    (G : C(_root_.Metric.closedBall (0 : ℂ) 1, _root_.Metric.closedBall (0 : ℂ) 1)) {C : ℝ≥0}
    (hGLip : LipschitzWith C G)
    (hG : ∀ z (hz : z ∈ _root_.Metric.ball (0 : ℂ) 1),
      (G ⟨z, _root_.Metric.ball_subset_closedBall hz⟩ : ℂ) = f (W z))
    {p : ℂ} (hp : p ∈ _root_.Metric.sphere (0 : ℂ) 1) {R : ℝ} (hR : 0 < R) (c : ℂ) :
    ¬ ∀ z (hz : z ∈ _root_.Metric.sphere (0 : ℂ) 1 ∩ _root_.Metric.ball p R),
      (G ⟨z, _root_.Metric.sphere_subset_closedBall hz.1⟩ : ℂ) = c := by
  classical
  intro hconst
  obtain ⟨_, _, hclosure, hfrontier, hclt, hft, _⟩ :=
    buffered_disk_image_geometry W hr hWsource
  have hclosed : _root_.Metric.closedBall (0 : ℂ) 1 ⊆ W.source := by
    rw [hWsource]
    exact _root_.Metric.closedBall_subset_ball hr
  have hps := hclosed (_root_.Metric.sphere_subset_closedBall hp)
  have hpT := W.map_source hps
  have hpF : W p ∈ frontier f.source := by
    rw [hfsource, hfrontier]
    exact _root_.Set.mem_image_of_mem W hp
  have hnull : _root_.MeasureTheory.MeasureSpace.volume (frontier f.source) = 0 := by
    rw [hfsource, hfrontier]
    exact DifferentialGeometry.Analysis.volume_image_sphere_eq_zero_of_contDiffOn W.open_source
      hW (0 : ℂ) 1 (sphere_subset_closedBall.trans hclosed)
  obtain ⟨ε₁, hε₁, hε₁T, L, hLip⟩ := exists_lipschitzOnWith_inverse_ball_of_contDiffOn
    W hWi hpT
  have hnear : W.symm ⁻¹' _root_.Metric.ball p R ∈ 𝓝 (W p) := by
    have hc := W.continuousOn_invFun.continuousAt (W.open_target.mem_nhds hpT)
    apply hc.preimage_mem_nhds
    change _root_.Metric.ball p R ∈ 𝓝 (W.symm (W p))
    rw [W.left_inv hps]
    exact _root_.Metric.ball_mem_nhds p hR
  obtain ⟨ε₂, hε₂, hε₂map⟩ := Metric.mem_nhds_iff.mp hnear
  let ε := _root_.Min.min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hεLip : LipschitzOnWith L W.symm (_root_.Metric.ball (W p) ε) :=
    hLip.mono (_root_.Metric.ball_subset_ball (min_le_left _ _))
  have hεT : _root_.Metric.ball (W p) ε ⊆ W.target :=
    (_root_.Metric.ball_subset_ball (min_le_left _ _)).trans hε₁T
  have hεmap : _root_.Set.MapsTo W.symm (_root_.Metric.ball (W p) ε) (_root_.Metric.ball p R) :=
    (_root_.Metric.ball_subset_ball (min_le_right _ _)).trans hε₂map
  let g : ℂ → ℂ := fun y => (G (diskRetraction (W.symm y)) : ℂ)
  have hGcomplex : LipschitzWith C (fun z : _root_.Metric.closedBall (0 : ℂ) 1 => (G z : ℂ)) := by
    intro x y
    exact hGLip x y
  have hg : LipschitzOnWith (C * L) g (_root_.Metric.ball (W p) ε) := by
    have h := (hGcomplex.comp diskRetraction_lipschitz).comp_lipschitzOnWith hεLip
    simpa only [mul_one, g, Function.comp_apply] using! h
  have hge : _root_.Set.EqOn g f (f.source ∩ _root_.Metric.ball (W p) ε) := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hfsource ▸ hy.1
    have hzS := hclosed (_root_.Metric.ball_subset_closedBall hz)
    rw [← hzy]
    change (G (diskRetraction (W.symm (W z))) : ℂ) = f (W z)
    rw [W.left_inv hzS, diskRetraction_coe ⟨z, _root_.Metric.ball_subset_closedBall hz⟩]
    exact hG z hz
  have hgc : ∀ y ∈ frontier f.source ∩ _root_.Metric.ball (W p) ε, g y = c := by
    intro y hy
    have hyF : y ∈ W '' _root_.Metric.sphere (0 : ℂ) 1 := by
      rw [← hfrontier, ← hfsource]
      exact hy.1
    obtain ⟨z, hz, hzy⟩ := hyF
    have hzS := hclosed (_root_.Metric.sphere_subset_closedBall hz)
    have hznear : z ∈ _root_.Metric.ball p R := by
      have hh := hεmap hy.2
      rw [← hzy, W.left_inv hzS] at hh
      exact hh
    rw [← hzy]
    change (G (diskRetraction (W.symm (W z))) : ℂ) = c
    rw [W.left_inv hzS, diskRetraction_coe ⟨z, _root_.Metric.sphere_subset_closedBall hz⟩]
    exact hconst z ⟨hz, hznear⟩
  have hout : ∃ y ∈ _root_.Metric.ball (W p) ε, y ∉ closure f.source := by
    rw [hfsource]
    exact exists_exterior_point_near_frontier_buffered_disk_image W hr hWsource
      (by simpa only [hfsource] using hpF) hε
  exact not_constant_boundary_patch_of_lipschitz_extension f hf hpF hε
    (_root_.MeasureTheory.measure_mono_null _root_.Set.inter_subset_left hnull) hout
    (hg.mono _root_.Set.inter_subset_right) hge c hgc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.not_constant_on_circle_patch_of_riemann_map_extension then
    throwError "Refusing to shadow existing declaration Complex.not_constant_on_circle_patch_of_riemann_map_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.not_constant_on_circle_patch_of_riemann_map_extension ``Submission.Complex.not_constant_on_circle_patch_of_riemann_map_extension

end Complex

end

end

section

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.ContDiff _root_.NNReal

namespace Complex
open _root_.Complex

open _root_.Complex in
private theorem bijective_disk_extension_of_no_constant_patch
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = _root_.Metric.ball (0 : ℂ) 1) (het : e.target = _root_.Metric.ball (0 : ℂ) 1)
    (G : C(_root_.Metric.closedBall (0 : ℂ) 1, _root_.Metric.closedBall (0 : ℂ) 1))
    (hG : ∀ z (hz : z ∈ _root_.Metric.ball (0 : ℂ) 1),
      (G ⟨z, _root_.Metric.ball_subset_closedBall hz⟩ : ℂ) = e z)
    (hpatch : ∀ p ∈ _root_.Metric.sphere (0 : ℂ) 1, ∀ R > 0, ∀ c : ℂ,
      ¬ ∀ z (hz : z ∈ _root_.Metric.sphere (0 : ℂ) 1 ∩ _root_.Metric.ball p R),
        (G ⟨z, _root_.Metric.sphere_subset_closedBall hz.1⟩ : ℂ) = c) :
    Function.Bijective G := by
  let h : _root_.Metric.ball (0 : ℂ) 1 ≃ₜ _root_.Metric.ball (0 : ℂ) 1 :=
    e.homeomorphOfImageSubsetSource (by rw [hes]) ((congrArg (fun s => e ''
      s) hes.symm).trans (e.image_source_eq_target.trans het))
  have hh (z : _root_.Metric.ball (0 : ℂ) 1) : G ⟨z, _root_.Metric.ball_subset_closedBall z.2⟩ =
      ⟨h z, _root_.Metric.ball_subset_closedBall (h z).2⟩ := Subtype.ext (hG z z.2)
  have hmap (z : _root_.Metric.closedBall (0 : ℂ) 1) (hz : (z : ℂ) ∈ _root_.Metric.ball (0 : ℂ) 1) :
      (G z : ℂ) ∈ _root_.Metric.ball (0 : ℂ) 1 := by
    rw [hG z hz]
    exact het ▸ e.map_source (hes ▸ hz)
  have hsurj : Function.Surjective G := by
    intro y
    obtain ⟨x, hx⟩ := (h.isConnected_fiber_extension_to_closedBall
      (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1) G hh y).nonempty
    exact ⟨x, hx⟩
  refine ⟨?_, hsurj⟩
  intro x y hxy
  by_cases hxG : (G x : ℂ) ∈ _root_.Metric.ball (0 : ℂ) 1
  · have hpre (z : _root_.Metric.closedBall (0 : ℂ) 1) (hz : G z = G x) :
        (z : ℂ) ∈ _root_.Metric.ball (0 : ℂ) 1 := by
      have hzn := mem_closedBall_zero_iff.mp z.2
      rcases lt_or_eq_of_le hzn with hi | hb
      · exact mem_ball_zero_iff.mpr hi
      have hnorm := norm_extension_eq_one_on_sphere e hes het G hG
        (mem_sphere_zero_iff_norm.mpr hb)
      rw [hz] at hnorm
      exact False.elim ((ne_of_lt (mem_ball_zero_iff.mp hxG)) hnorm)
    have hx := hpre x rfl
    have hy := hpre y hxy.symm
    apply Subtype.ext
    apply e.injOn (hes ▸ hx) (hes ▸ hy)
    exact (hG x hx).symm.trans ((congrArg Subtype.val hxy).trans (hG y hy))
  · by_contra hne
    let S : Set ℂ := Subtype.val '' (G ⁻¹' {G x})
    have hS : S ⊆ _root_.Metric.sphere (0 : ℂ) 1 := by
      rintro _ ⟨z, hz, rfl⟩
      have hzG : G z = G x := hz
      apply mem_sphere_zero_iff_norm.mpr
      apply le_antisymm (mem_closedBall_zero_iff.mp z.2)
      by_contra! hzlt
      exact hxG (hzG ▸ hmap z (mem_ball_zero_iff.mpr hzlt))
    have hconn : IsPreconnected S :=
      (h.isConnected_fiber_extension_to_closedBall (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1)
        G hh (G x)).isPreconnected.image Subtype.val continuous_subtype_val.continuousOn
    have hpair : S.Nontrivial := by
      refine ⟨x, ⟨x, rfl, rfl⟩, y, ⟨y, hxy.symm, rfl⟩, ?_⟩
      exact fun hv => hne (Subtype.ext hv)
    obtain ⟨p, hp, R, hR, hRS⟩ :=
      exists_relative_ball_subset_of_isPreconnected_sphere hS hconn hpair
    apply hpatch p hp R hR (G x)
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hRS hz
    have hwsub : w = ⟨z, _root_.Metric.sphere_subset_closedBall hz.1⟩ := Subtype.ext hwz
    rw [← hwsub]
    exact congrArg Subtype.val hw

run_cmd do
  let target := ``Submission.Complex.bijective_disk_extension_of_no_constant_patch
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Complex.bijective_disk_extension_of_no_constant_patch target :: scope.openDecls } }

open _root_.Complex in
theorem exists_lipschitz_homeomorph_riemann_map_comp_of_buffered_disk
    (W f : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hWsource : W.source = _root_.Metric.ball (0 : ℂ) r)
    (hW : ContDiffOn ℝ ∞ W W.source) (hWi : ContDiffOn ℝ ∞ W.symm W.target)
    (hfsource : f.source = W '' _root_.Metric.ball (0 : ℂ) 1)
    (hftarget : f.target = _root_.Metric.ball (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f f.source) :
    ∃ (C : ℝ≥0) (H : _root_.Metric.closedBall (0 : ℂ) 1 ≃ₜ _root_.Metric.closedBall (0 : ℂ) 1),
      LipschitzWith C H ∧
      (∀ z (hz : z ∈ _root_.Metric.ball (0 : ℂ) 1),
        (H ⟨z, _root_.Metric.ball_subset_closedBall hz⟩ : ℂ) = f (W z)) ∧
      (∀ z (hz : z ∈ _root_.Metric.ball (0 : ℂ) 1),
        (H.symm ⟨z, _root_.Metric.ball_subset_closedBall hz⟩ : ℂ) = W.symm (f.symm z)) := by
  have hD : _root_.Metric.ball (0 : ℂ) 1 ⊆ W.source := by
    rw [hWsource]
    exact _root_.Metric.ball_subset_ball hr.le
  let W₁ := W.restrOpen (_root_.Metric.ball (0 : ℂ) 1) _root_.Metric.isOpen_ball
  have hW₁s : W₁.source = _root_.Metric.ball (0 : ℂ) 1 := inter_eq_right.mpr hD
  have hW₁t : W₁.target = f.source := by
    rw [← W₁.image_source_eq_target, hW₁s, hfsource]
    rfl
  let e := W₁.trans' f hW₁t
  have hes : e.source = _root_.Metric.ball (0 : ℂ) 1 := hW₁s
  have het : e.target = _root_.Metric.ball (0 : ℂ) 1 := hftarget
  obtain ⟨C, G, hGLip, hG⟩ :=
    exists_lipschitz_riemann_map_comp_extension_of_buffered_disk
      W f hr hWsource hW hWi hfsource hftarget hf
  have hbij : Function.Bijective G := bijective_disk_extension_of_no_constant_patch e hes het G hG
    (fun p hp R hR c => not_constant_on_circle_patch_of_riemann_map_extension W f hr hWsource
      (hW.of_le (by simp)) (hWi.of_le (by simp)) hfsource hf G hGLip hG hp hR c)
  let H := (Equiv.ofBijective G hbij).toHomeomorphOfContinuousClosed G.continuous
    G.continuous.isClosedMap
  refine ⟨C, H, hGLip, hG, ?_⟩
  intro z hz
  have hzT : z ∈ e.target := het ▸ hz
  have hi : e.symm z ∈ _root_.Metric.ball (0 : ℂ) 1 := hes ▸ e.map_target hzT
  have heq : H ⟨e.symm z, _root_.Metric.ball_subset_closedBall hi⟩ = ⟨z, _root_.Metric.ball_subset_closedBall hz⟩ := by
    apply Subtype.ext
    exact (hG _ hi).trans (e.right_inv hzT)
  have hiH := congrArg H.symm heq
  rw [H.symm_apply_apply] at hiH
  exact (congrArg Subtype.val hiH).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.exists_lipschitz_homeomorph_riemann_map_comp_of_buffered_disk then
    throwError "Refusing to shadow existing declaration Complex.exists_lipschitz_homeomorph_riemann_map_comp_of_buffered_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.exists_lipschitz_homeomorph_riemann_map_comp_of_buffered_disk ``Submission.Complex.exists_lipschitz_homeomorph_riemann_map_comp_of_buffered_disk

open _root_.Complex in
theorem exists_homeomorph_riemann_map_of_buffered_disk
    (W f : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hWsource : W.source = _root_.Metric.ball (0 : ℂ) r)
    (hW : ContDiffOn ℝ ∞ W W.source) (hWi : ContDiffOn ℝ ∞ W.symm W.target)
    (hfsource : f.source = W '' _root_.Metric.ball (0 : ℂ) 1)
    (hftarget : f.target = _root_.Metric.ball (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f f.source) :
    ∃ F : closure f.source ≃ₜ _root_.Metric.closedBall (0 : ℂ) 1,
      (∀ z (hz : z ∈ f.source), (F ⟨z, subset_closure hz⟩ : ℂ) = f z) ∧
      (∀ z (hz : z ∈ _root_.Metric.ball (0 : ℂ) 1),
        (F.symm ⟨z, _root_.Metric.ball_subset_closedBall hz⟩ : ℂ) = f.symm z) := by
  obtain ⟨_, H, _, hH, hHi⟩ :=
    exists_lipschitz_homeomorph_riemann_map_comp_of_buffered_disk
      W f hr hWsource hW hWi hfsource hftarget hf
  have hclosed : _root_.Metric.closedBall (0 : ℂ) 1 ⊆ W.source := by
    rw [hWsource]
    exact _root_.Metric.closedBall_subset_ball hr
  have hcl : W '' _root_.Metric.closedBall (0 : ℂ) 1 = closure f.source := by
    rw [hfsource]
    exact (buffered_disk_image_geometry W hr hWsource).2.2.1.symm
  let J := W.homeomorphOfImageSubsetSource hclosed hcl
  let F := J.symm.trans H
  refine ⟨F, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hfsource ▸ hz
    have hi : W.symm (W x) = x := W.left_inv (hclosed (_root_.Metric.ball_subset_closedBall hx))
    change (H (J.symm ⟨W x, _⟩) : ℂ) = f (W x)
    have heq : J.symm ⟨W x, subset_closure hz⟩ = ⟨x, _root_.Metric.ball_subset_closedBall hx⟩ := Subtype.ext hi
    rw [heq]
    exact hH x hx
  · intro z hz
    change W (H.symm ⟨z, _root_.Metric.ball_subset_closedBall hz⟩) = f.symm z
    rw [hHi z hz]
    apply W.right_inv
    have hfs : f.symm z ∈ W '' _root_.Metric.ball (0 : ℂ) 1 := hfsource ▸ f.map_target (hftarget ▸ hz)
    obtain ⟨x, hx, hxf⟩ := hfs
    rw [← hxf]
    exact W.map_source (hclosed (_root_.Metric.ball_subset_closedBall hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.exists_homeomorph_riemann_map_of_buffered_disk then
    throwError "Refusing to shadow existing declaration Complex.exists_homeomorph_riemann_map_of_buffered_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.exists_homeomorph_riemann_map_of_buffered_disk ``Submission.Complex.exists_homeomorph_riemann_map_of_buffered_disk

end Complex

end

end
