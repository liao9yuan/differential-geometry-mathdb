import Submission.DifferentialGeometry.Analysis.Complex.RiemannMapping.BoundaryModulus
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Topology.MetricSpace.Thickening
import Submission.DifferentialGeometry.Analysis.Complex.RiemannMapping.DiskImage
import Submission.DifferentialGeometry.Geometry.Boundary.StrictExteriorBall
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.BoundaryBarrier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.Metric _root_.InnerProductSpace _root_.Submission.InnerProductSpace
open scoped _root_.Topology

namespace Complex
open _root_.Complex

open _root_.Complex in
theorem exists_norm_gt_on_cthickening_frontier_of_unit_disk_homeomorph
    (e : OpenPartialHomeomorph ℂ ℂ) (htarget : e.target = _root_.Metric.ball (0 : ℂ) 1)
    (hfrontier : IsCompact (frontier e.source)) {a : ℝ} (ha : a < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ _root_.Metric.cthickening δ (frontier e.source),
      z ∈ e.source → a < ‖e z‖ := by
  have hsub : _root_.Metric.closedBall (0 : ℂ) a ⊆ e.target := by
    rw [htarget]
    exact _root_.Metric.closedBall_subset_ball ha
  let K := e.symm '' _root_.Metric.closedBall (0 : ℂ) a
  have hK : IsCompact K := (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) a).image_of_continuousOn
    (e.continuousOn_invFun.mono hsub)
  have hFK : frontier e.source ⊆ Kᶜ := by
    intro z hz hKz
    obtain ⟨y, hy, rfl⟩ := hKz
    have hs := e.map_target (hsub hy)
    exact (e.open_source.frontier_eq ▸ hz).2 hs
  obtain ⟨δ, hδ, hd⟩ := hfrontier.exists_cthickening_subset_open hK.isClosed.isOpen_compl hFK
  refine ⟨δ, hδ, ?_⟩
  intro z hz hzs
  apply lt_of_not_ge
  intro hnorm
  exact hd hz ⟨e z, mem_closedBall_zero_iff.mpr hnorm, e.left_inv hzs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.exists_norm_gt_on_cthickening_frontier_of_unit_disk_homeomorph then
    throwError "Refusing to shadow existing declaration Complex.exists_norm_gt_on_cthickening_frontier_of_unit_disk_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.exists_norm_gt_on_cthickening_frontier_of_unit_disk_homeomorph ``Submission.Complex.exists_norm_gt_on_cthickening_frontier_of_unit_disk_homeomorph

open scoped _root_.Classical in
open _root_.Complex in
theorem exists_bounded_harmonic_log_norm_collar
    (e : OpenPartialHomeomorph ℂ ℂ) (htarget : e.target = _root_.Metric.ball (0 : ℂ) 1)
    (hfrontier : IsCompact (frontier e.source))
    (he : DifferentiableOn ℂ e e.source) :
    ∃ δ : ℝ, 0 < δ ∧
      ContinuousOn (e.source.piecewise (fun z => Real.log ‖e z‖) (fun _ => 0))
        (_root_.Metric.cthickening δ (frontier e.source)) ∧
      (∀ z ∈ _root_.Metric.cthickening δ (frontier e.source),
        |e.source.piecewise (fun z => Real.log ‖e z‖) (fun _ => 0) z| ≤ Real.log 2) ∧
      ∀ z ∈ _root_.Metric.thickening δ (frontier e.source) ∩ e.source,
        HarmonicAt (fun z => Real.log ‖e z‖) z := by
  classical
  obtain ⟨δ, hδ, hnorm⟩ :=
    exists_norm_gt_on_cthickening_frontier_of_unit_disk_homeomorph e htarget hfrontier
      (show (1 / 2 : ℝ) < 1 by norm_num)
  let u := e.source.piecewise (fun z => Real.log ‖e z‖) (fun _ => 0)
  have hne (z : ℂ) (hz : z ∈ _root_.Metric.cthickening δ (frontier e.source)) (hzs : z ∈ e.source) :
      e z ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) (hnorm z hz hzs))
  refine ⟨δ, hδ, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzs : z ∈ e.source
    · have huc : ContinuousAt (fun z => Real.log ‖e z‖) z :=
        ((e.continuousOn_toFun z hzs).continuousAt (e.open_source.mem_nhds hzs)).norm.log
          (norm_ne_zero_iff.mpr (hne z hz hzs))
      have heq : u =ᶠ[𝓝 z] fun z => Real.log ‖e z‖ := by
        filter_upwards [e.open_source.mem_nhds hzs] with w hw
        exact _root_.Set.piecewise_eq_of_mem e.source _ _ hw
      exact (huc.congr_of_eventuallyEq heq).continuousWithinAt
    · by_cases hzf : z ∈ frontier e.source
      · exact (continuousAt_piecewise_log_norm_of_unit_disk_homeomorph e
        htarget hzf).continuousWithinAt
      · have hzc : z ∉ closure e.source := by
          intro hzcl
          apply hzf
          rw [e.open_source.frontier_eq]
          exact ⟨hzcl, hzs⟩
        have heq : u =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hzc] with w hw
          exact _root_.Set.piecewise_eq_of_notMem e.source _ _ (fun hws => hw (subset_closure hws))
        exact (continuousAt_const.congr_of_eventuallyEq heq).continuousWithinAt
  · intro z hz
    by_cases hzs : z ∈ e.source
    · rw [_root_.Set.piecewise_eq_of_mem e.source _ _ hzs]
      have hnorm1 : ‖e z‖ < 1 := mem_ball_zero_iff.mp (htarget ▸ e.map_source hzs)
      have hnormpos : 0 < ‖e z‖ := norm_pos_iff.mpr (hne z hz hzs)
      have hlognonpos : Real.log ‖e z‖ ≤ 0 := Real.log_nonpos hnormpos.le hnorm1.le
      rw [abs_of_nonpos hlognonpos]
      have hlow := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) (hnorm z hz hzs).le
      have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
      rw [hhalf] at hlow
      linarith
    · rw [_root_.Set.piecewise_eq_of_notMem e.source _ _ hzs, abs_zero]
      exact Real.log_nonneg (by norm_num)
  · intro z hz
    have hz' : z ∈ _root_.Metric.cthickening δ (frontier e.source) :=
      _root_.Metric.thickening_subset_cthickening δ (frontier e.source) hz.1
    exact (he.analyticOnNhd e.open_source z hz.2).harmonicAt_log_norm (hne z hz' hz.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.exists_bounded_harmonic_log_norm_collar then
    throwError "Refusing to shadow existing declaration Complex.exists_bounded_harmonic_log_norm_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.exists_bounded_harmonic_log_norm_collar ``Submission.Complex.exists_bounded_harmonic_log_norm_collar

end Complex

end

end

section

noncomputable section

open _root_.Set _root_.Filter _root_.Metric _root_.InnerProductSpace _root_.Submission.InnerProductSpace
open _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Topology _root_.ContDiff

namespace Complex
open _root_.Complex

open _root_.Complex in
theorem exists_log_norm_boundary_growth_of_buffered_disk
    (W f : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hWsource : W.source = _root_.Metric.ball (0 : ℂ) r)
    (hW : ContDiffOn ℝ ∞ W W.source) (hWi : ContDiffOn ℝ ∞ W.symm W.target)
    (hfsource : f.source = W '' _root_.Metric.ball (0 : ℂ) 1)
    (hftarget : f.target = _root_.Metric.ball (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f f.source) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ p ∈ frontier f.source,
      ∀ z ∈ f.source ∩ _root_.Metric.ball p ε, |Real.log ‖f z‖| ≤ C * _root_.Dist.dist z p := by
  classical
  let U := f.source
  let K := frontier U
  let g : ℂ → ℝ := fun y => ‖W.symm y‖ ^ 2 - 1
  let u : ℂ → ℝ := U.piecewise (fun z => Real.log ‖f z‖) (fun _ => 0)
  obtain ⟨hUopen, hcompact, hclosure, hfrontier, hKt, hKft, _⟩ :=
    buffered_disk_image_geometry W hr hWsource
  have hKcompact : IsCompact K := by
    apply hcompact.of_isClosed_subset isClosed_frontier
    rw [← hclosure]
    simpa only [K, U, hfsource] using (frontier_subset_closure (s := W '' _root_.Metric.ball (0 : ℂ) 1))
  have hKtarget : K ⊆ W.target := by simpa only [K, U, hfsource, hfrontier] using hKft
  obtain ⟨hgs, hgle, hgreg⟩ := buffered_disk_image_defining_function W hr hWsource hW hWi
  have hzero : ∀ p ∈ K, g p = 0 := by
    intro p hp
    exact (hgreg p (by simpa only [K, U, hfsource] using hp)).1
  have hreg : ∀ p ∈ K, gradient g p ≠ 0 := by
    intro p hp hgrad
    have hn := (hgreg p (by simpa only [K, U, hfsource] using hp)).2
    apply hn
    ext v
    have h := inner_gradient_left (f := g) (x := p) (y := v)
    rw [hgrad, inner_zero_left] at h
    exact h.symm
  obtain ⟨δg, ρ, hδg, hρ, hsphere⟩ :=
    exists_uniform_strict_exterior_ball_on_compact_regular_level W.open_target
      (hgs.of_le (by decide)) hKcompact hKtarget hzero hreg
  obtain ⟨δu, hδu, huc, hubound, huh⟩ :=
    exists_bounded_harmonic_log_norm_collar f hftarget hKcompact hf
  let δ := _root_.Min.min δg δu / 2
  have hδ : 0 < δ := half_pos (lt_min hδg hδu)
  have hδg' : δ < δg := by dsimp only [δ]; linarith [min_le_left δg δu]
  have hδu' : δ < δu := by dsimp only [δ]; linarith [min_le_right δg δu]
  let gap := Real.sqrt (ρ ^ 2 + δ ^ 2 / 2) - ρ
  have hgap : 0 < gap := by
    dsimp only [gap]
    apply sub_pos.mpr
    exact (Real.lt_sqrt hρ.le).mpr (by nlinarith)
  let C := Real.log 2 / Real.log ((ρ + gap) / ρ) / ρ
  have hlog : 0 < Real.log ((ρ + gap) / ρ) :=
    Real.log_pos ((one_lt_div hρ).mpr (by linarith))
  have hM : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hC : 0 ≤ C := div_nonneg (div_nonneg hM hlog.le) hρ.le
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro p hp z hz
  let a := p + ρ • (‖gradient g p‖⁻¹ • gradient g p)
  have ha : _root_.Dist.dist a p = ρ := (hsphere p hp).1
  have hcap : _root_.Metric.closedBall p δ ⊆ _root_.Metric.cthickening δu K :=
    (_root_.Metric.closedBall_subset_closedBall hδu'.le).trans (_root_.Metric.closedBall_subset_cthickening hp δu)
  have hcapOpen : _root_.Metric.ball p δ ⊆ _root_.Metric.thickening δu K := by
    intro y hy
    apply mem_thickening_iff.mpr
    exact ⟨p, hp, (mem_ball.mp hy).trans hδu'⟩
  have hsep (y : ℂ) (hy : y ∈ closure U ∩ _root_.Metric.closedBall p δ) :
      ρ ^ 2 + _root_.Dist.dist y p ^ 2 / 2 ≤ ‖y - a‖ ^ 2 := by
    have hyg : g y ≤ 0 := hgle y (by simpa only [U, hfsource] using hy.1)
    simpa only [dist_eq_norm, a, g] using (hsphere p hp).2 y
      (mem_ball.mpr ((mem_closedBall.mp hy.2).trans_lt hδg')) hyg
  have hext (y : ℂ) (hy : y ∈ closure U ∩ _root_.Metric.closedBall p δ) : ρ ≤ ‖y - a‖ := by
    have h := hsep y hy
    nlinarith [norm_nonneg (y - a), sq_nonneg (_root_.Dist.dist y p)]
  have hrim (y : ℂ) (hy : y ∈ closure U ∩ _root_.Metric.sphere p δ) : ρ + gap ≤ ‖y - a‖ := by
    have h := hsep y ⟨hy.1, _root_.Metric.sphere_subset_closedBall hy.2⟩
    rw [mem_sphere.mp hy.2] at h
    dsimp only [gap]
    rw [add_sub_cancel]
    exact (Real.sqrt_le_iff).mpr ⟨norm_nonneg _, h⟩
  have hclcap : closure (U ∩ _root_.Metric.ball p δ) ⊆ _root_.Metric.cthickening δu K :=
    (closure_minimal (inter_subset_right.trans _root_.Metric.ball_subset_closedBall)
      _root_.Metric.isClosed_closedBall).trans hcap
  have hharm : _root_.InnerProductSpace.HarmonicOnNhd u (U ∩ _root_.Metric.ball p δ) := by
    intro y hy
    have heq : u =ᶠ[𝓝 y] fun z => Real.log ‖f z‖ := by
      filter_upwards [f.open_source.mem_nhds hy.1] with x hx
      exact _root_.Set.piecewise_eq_of_mem U _ _ hx
    exact (_root_.InnerProductSpace.harmonicAt_congr_nhds heq).mpr (huh y ⟨hcapOpen hy.2, hy.1⟩)
  have hu0 (y : ℂ) (hy : y ∈ frontier U ∩ _root_.Metric.closedBall p δ) : u y = 0 := by
    have hnot : y ∉ U := (f.open_source.frontier_eq ▸ hy.1).2
    exact _root_.Set.piecewise_eq_of_notMem U _ _ hnot
  have hub (y : ℂ) (hy : y ∈ closure U ∩ _root_.Metric.sphere p δ) : |u y| ≤ Real.log 2 :=
    hubound y (hcap (_root_.Metric.sphere_subset_closedBall hy.2))
  have hcompare := abs_le_logarithmic_boundary_barrier f.open_source hρ hgap hM
    (huc.mono hclcap) hharm hu0 hub hext hrim z (subset_closure hz)
  have hzs : z ∈ f.source := hz.1
  rw [_root_.Set.piecewise_eq_of_mem f.source _ _ hzs] at hcompare
  have hznorm : 0 < ‖z - a‖ := hρ.trans_le (hext z ⟨subset_closure hz.1,
    _root_.Metric.ball_subset_closedBall hz.2⟩)
  have hnormle : ‖z - a‖ ≤ ρ + _root_.Dist.dist z p := by
    have h := dist_triangle z p a
    rw [dist_comm p a, ha, dist_eq_norm z a] at h
    linarith
  have hlogle : Real.log (‖z - a‖ / ρ) ≤ _root_.Dist.dist z p / ρ := by
    have h := Real.log_le_sub_one_of_pos (div_pos hznorm hρ)
    have hd : ‖z - a‖ / ρ ≤ (ρ + _root_.Dist.dist z p) / ρ := (div_le_div_iff_of_pos_right hρ).mpr hnormle
    have he : (ρ + _root_.Dist.dist z p) / ρ - 1 = _root_.Dist.dist z p / ρ := by field_simp; ring
    linarith
  exact hcompare.trans ((mul_le_mul_of_nonneg_left hlogle (div_nonneg hM hlog.le)).trans_eq
    (by dsimp only [C]; ring))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.exists_log_norm_boundary_growth_of_buffered_disk then
    throwError "Refusing to shadow existing declaration Complex.exists_log_norm_boundary_growth_of_buffered_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.exists_log_norm_boundary_growth_of_buffered_disk ``Submission.Complex.exists_log_norm_boundary_growth_of_buffered_disk

end Complex

end

end
