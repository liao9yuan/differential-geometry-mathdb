import Submission.DifferentialGeometry.Analysis.Complex.WeakHolomorphic
import Submission.DifferentialGeometry.Analysis.Calculus.Lipschitz.FrontierExtension
import Submission.DifferentialGeometry.Analysis.Complex.Univalent
import Mathlib.Analysis.Complex.OpenMapping

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.Metric _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.NNReal

namespace Complex
open _root_.Complex

open _root_.Complex in
theorem not_constant_boundary_patch_of_lipschitz_extension
    (e : OpenPartialHomeomorph ℂ ℂ) (he : DifferentiableOn ℂ e e.source)
    {p : ℂ} (hp : p ∈ frontier e.source) {R : ℝ} (hR : 0 < R)
    (hnull : _root_.MeasureTheory.MeasureSpace.volume (frontier e.source ∩ _root_.Metric.ball p R) = 0)
    (hout : ∃ y ∈ _root_.Metric.ball p R, y ∉ closure e.source)
    {g : ℂ → ℂ} {L : ℝ≥0} (hg : LipschitzOnWith L g (closure e.source ∩ _root_.Metric.ball p R))
    (hge : _root_.Set.EqOn g e (e.source ∩ _root_.Metric.ball p R)) (c : ℂ) :
    ¬ ∀ y ∈ frontier e.source ∩ _root_.Metric.ball p R, g y = c := by
  classical
  intro hgc
  let H : ℂ → ℂ := e.source.piecewise (fun z => g z - c) (fun _ => 0)
  have hHLip : LipschitzOnWith L H (_root_.Metric.ball p R) :=
    hg.piecewise_sub_const_on_ball_of_eq_on_frontier e.open_source hgc
  have hnotfront : ∀ᵐ z : ℂ ∂volume.restrict (_root_.Metric.ball p R), z ∉ frontier e.source := by
    apply ae_iff.mpr
    simpa only [_root_.Classical.not_not, _root_.Set.ofPred_mem_eq, Measure.restrict_apply
      isClosed_frontier.measurableSet] using hnull
  have hAE : ∀ᵐ z ∂volume.restrict (_root_.Metric.ball p R), DifferentiableAt ℂ H z := by
    filter_upwards [hnotfront, _root_.MeasureTheory.ae_restrict_mem isOpen_ball.measurableSet]
      with z hzf hz
    by_cases hzs : z ∈ e.source
    · have hnear : H =ᶠ[𝓝 z] fun y => e y - c := by
        filter_upwards [(e.open_source.inter _root_.Metric.isOpen_ball).mem_nhds ⟨hzs, hz⟩] with y hy
        rw [show H y = g y - c from _root_.Set.piecewise_eq_of_mem e.source _ _ hy.1, hge hy]
      exact (((he z hzs).differentiableAt (e.open_source.mem_nhds
        hzs)).sub_const c).congr_of_eventuallyEq hnear
    · have hzcl : z ∉ closure e.source := by
        intro hzc
        apply hzf
        rw [e.open_source.frontier_eq]
        exact ⟨hzc, hzs⟩
      have hnear : H =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hzcl] with y hy
        exact _root_.Set.piecewise_eq_of_notMem e.source _ _ (fun hs => hy (subset_closure hs))
      exact (differentiableAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hnear
  have hHol :=
    DifferentialGeometry.Analysis.differentiableOn_of_lipschitzOnWith_of_ae_differentiableAt
    _root_.Metric.isOpen_ball hHLip hAE
  obtain ⟨y, hy, hycl⟩ := hout
  have hzeroNear : H =ᶠ[𝓝 y] 0 := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hycl] with z hz
    exact _root_.Set.piecewise_eq_of_notMem e.source _ _ (fun hs => hz (subset_closure hs))
  have hzero : _root_.Set.EqOn H 0 (_root_.Metric.ball p R) :=
    hHol.analyticOnNhd _root_.Metric.isOpen_ball |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball p R).isPreconnected hy hzeroNear
  have hpcl : p ∈ closure e.source := frontier_subset_closure hp
  obtain ⟨z, hzs, hzp⟩ := Metric.mem_closure_iff.mp hpcl R hR
  have hz : z ∈ _root_.Metric.ball p R := by simpa only [_root_.Metric.mem_ball, dist_comm] using hzp
  have heNear : e =ᶠ[𝓝 z] fun _ => c := by
    filter_upwards [(e.open_source.inter _root_.Metric.isOpen_ball).mem_nhds ⟨hzs, hz⟩] with w hw
    have h := hzero hw.2
    change H w = 0 at h
    rw [show H w = g w - c from _root_.Set.piecewise_eq_of_mem e.source _ _ hw.1, hge hw] at h
    exact sub_eq_zero.mp h
  have hder : deriv e z = 0 := by simpa only [deriv_const] using heNear.deriv_eq
  exact deriv_ne_zero_of_differentiableOn_of_injOn e.open_source he e.injOn hzs hder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.not_constant_boundary_patch_of_lipschitz_extension then
    throwError "Refusing to shadow existing declaration Complex.not_constant_boundary_patch_of_lipschitz_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.not_constant_boundary_patch_of_lipschitz_extension ``Submission.Complex.not_constant_boundary_patch_of_lipschitz_extension

end Complex

end

end
