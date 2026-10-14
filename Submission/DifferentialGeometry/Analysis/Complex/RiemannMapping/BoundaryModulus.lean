import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Piecewise
import Submission.DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.Metric
open scoped _root_.Topology

namespace Complex
open _root_.Complex

open _root_.Complex in
theorem tendsto_norm_at_frontier_of_unit_disk_homeomorph
    (e : OpenPartialHomeomorph ℂ ℂ) (htarget : e.target = _root_.Metric.ball (0 : ℂ) 1)
    {p : ℂ} (hp : p ∈ frontier e.source) :
    Tendsto (fun z => ‖e z‖) (𝓝[e.source] p) (𝓝 (1 : ℝ)) := by
  have hps : p ∉ e.source := by
    rw [e.open_source.frontier_eq] at hp
    exact hp.2
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hsub : _root_.Metric.closedBall (0 : ℂ) a ⊆ e.target := by
      rw [htarget]
      exact _root_.Metric.closedBall_subset_ball ha
    have hK : IsCompact (e.symm '' _root_.Metric.closedBall (0 : ℂ) a) :=
      (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) a).image_of_continuousOn
        (e.continuousOn_invFun.mono hsub)
    have hpK : p ∉ e.symm '' _root_.Metric.closedBall (0 : ℂ) a := by
      rintro ⟨w, hw, hpw⟩
      exact hps (hpw ▸ e.map_target (hsub hw))
    have hnear : (e.symm '' _root_.Metric.closedBall (0 : ℂ) a)ᶜ ∈ 𝓝 p :=
      hK.isClosed.isOpen_compl.mem_nhds hpK
    filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with z hz hzs
    apply lt_of_not_ge
    intro hza
    have hez : e z ∈ _root_.Metric.closedBall (0 : ℂ) a := by
      simpa only [_root_.Metric.mem_closedBall, dist_zero_right] using hza
    exact hz ⟨e z, hez, e.left_inv hzs⟩
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hez := e.map_source hz
    rw [htarget] at hez
    exact (mem_ball_zero_iff.mp hez).trans ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.tendsto_norm_at_frontier_of_unit_disk_homeomorph then
    throwError "Refusing to shadow existing declaration Complex.tendsto_norm_at_frontier_of_unit_disk_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.tendsto_norm_at_frontier_of_unit_disk_homeomorph ``Submission.Complex.tendsto_norm_at_frontier_of_unit_disk_homeomorph

open _root_.Complex in
theorem tendsto_log_norm_at_frontier_of_unit_disk_homeomorph
    (e : OpenPartialHomeomorph ℂ ℂ) (htarget : e.target = _root_.Metric.ball (0 : ℂ) 1)
    {p : ℂ} (hp : p ∈ frontier e.source) :
    Tendsto (fun z => Real.log ‖e z‖) (𝓝[e.source] p) (𝓝 (0 : ℝ)) := by
  simpa only [Function.comp_def, Real.log_one] using
    (Real.continuousAt_log one_ne_zero).tendsto.comp
      (tendsto_norm_at_frontier_of_unit_disk_homeomorph e htarget hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.tendsto_log_norm_at_frontier_of_unit_disk_homeomorph then
    throwError "Refusing to shadow existing declaration Complex.tendsto_log_norm_at_frontier_of_unit_disk_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.tendsto_log_norm_at_frontier_of_unit_disk_homeomorph ``Submission.Complex.tendsto_log_norm_at_frontier_of_unit_disk_homeomorph

open scoped _root_.Classical in
open _root_.Complex in
theorem continuousAt_piecewise_log_norm_of_unit_disk_homeomorph
    (e : OpenPartialHomeomorph ℂ ℂ) (htarget : e.target = _root_.Metric.ball (0 : ℂ) 1)
    {p : ℂ} (hp : p ∈ frontier e.source) :
    ContinuousAt (e.source.piecewise (fun z => Real.log ‖e z‖) (fun _ => 0)) p := by
  classical
  have hps : p ∉ e.source := by
    rw [e.open_source.frontier_eq] at hp
    exact hp.2
  have ht := (tendsto_log_norm_at_frontier_of_unit_disk_homeomorph e htarget hp).piecewise
    (s := e.source)
    (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : ℂ => (0 : ℝ)) (𝓝 p ⊓ 𝓟 e.sourceᶜ) (𝓝 0))
  simpa only [ContinuousAt, Set.piecewise, if_neg hps] using ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.continuousAt_piecewise_log_norm_of_unit_disk_homeomorph then
    throwError "Refusing to shadow existing declaration Complex.continuousAt_piecewise_log_norm_of_unit_disk_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.continuousAt_piecewise_log_norm_of_unit_disk_homeomorph ``Submission.Complex.continuousAt_piecewise_log_norm_of_unit_disk_homeomorph

end Complex

end

end

section

noncomputable section

open _root_.Set _root_.Filter _root_.Metric
open _root_.Submission.DifferentialGeometry.Geometry
open scoped _root_.Topology

namespace Complex
open _root_.Complex

open _root_.Complex in
theorem norm_extension_eq_one_on_sphere
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = _root_.Metric.ball (0 : ℂ) 1) (het : e.target = _root_.Metric.ball (0 : ℂ) 1)
    (G : C(_root_.Metric.closedBall (0 : ℂ) 1, _root_.Metric.closedBall (0 : ℂ) 1))
    (hG : ∀ z (hz : z ∈ _root_.Metric.ball (0 : ℂ) 1),
      (G ⟨z, _root_.Metric.ball_subset_closedBall hz⟩ : ℂ) = e z)
    {p : ℂ} (hp : p ∈ _root_.Metric.sphere (0 : ℂ) 1) :
    ‖(G ⟨p, _root_.Metric.sphere_subset_closedBall hp⟩ : ℂ)‖ = 1 := by
  let v : ℂ → ℂ := fun z => (G (diskRetraction z) : ℂ)
  have hvc : Continuous v := continuous_subtype_val.comp
    (G.continuous.comp diskRetraction_lipschitz.continuous)
  have hpcl : p ∈ closure (_root_.Metric.ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact _root_.Metric.sphere_subset_closedBall hp
  let _ : (𝓝[_root_.Metric.ball (0 : ℂ) 1] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hpcl
  have hlim : _root_.Filter.Tendsto (fun z => ‖e z‖) (𝓝[_root_.Metric.ball (0 : ℂ) 1] p) (𝓝 1) := by
    have hpf : p ∈ frontier e.source := by rw [hes, frontier_ball (0 : ℂ) one_ne_zero]; exact hp
    simpa only [hes] using tendsto_norm_at_frontier_of_unit_disk_homeomorph e het hpf
  have heq : (fun z => ‖e z‖) =ᶠ[𝓝[_root_.Metric.ball (0 : ℂ) 1] p] fun z => ‖v z‖ := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [show v z = (G ⟨z, _root_.Metric.ball_subset_closedBall hz⟩ : ℂ) by
      dsimp only [v]; rw [diskRetraction_coe ⟨z, _root_.Metric.ball_subset_closedBall hz⟩], hG z hz]
  have hlimv := hlim.congr' heq
  have hnorm : ‖v p‖ = 1 := tendsto_nhds_unique
    (hvc.norm.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlimv
  simpa only [v, diskRetraction_coe ⟨p, _root_.Metric.sphere_subset_closedBall hp⟩] using hnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.norm_extension_eq_one_on_sphere then
    throwError "Refusing to shadow existing declaration Complex.norm_extension_eq_one_on_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.norm_extension_eq_one_on_sphere ``Submission.Complex.norm_extension_eq_one_on_sphere

end Complex

end

end
