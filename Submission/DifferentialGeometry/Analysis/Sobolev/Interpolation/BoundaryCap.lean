import Submission.DifferentialGeometry.Analysis.Calculus.Interpolation.RadialLipschitzPasting
import Submission.DifferentialGeometry.Analysis.Complex.BoundaryLens.Geometry
import Mathlib.Analysis.Complex.Circle
import Submission.DifferentialGeometry.Analysis.Integration.BallBoundary
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoEMetricSpace F]

theorem lipschitzOnWith_piecewise_closedBall
    {S : Set E} (hS : Convex ℝ S) (c : E) (r : ℝ)
    {u q : E → F} {Ku Kq : ℝ≥0}
    (hu : LipschitzOnWith Ku u S) (hq : LipschitzOnWith Kq q S)
    (hglue : _root_.Set.EqOn q u (S ∩ _root_.Metric.sphere c r)) :
    LipschitzOnWith (_root_.Max.max Kq Ku) (fun z => if _root_.Dist.dist z c ≤ r then q z else u z) S := by
  let f : E → F := fun z => if _root_.Dist.dist z c ≤ r then q z else u z
  have hfinner (z : E) (hz : _root_.Dist.dist z c ≤ r) : f z = q z := if_pos hz
  have hfouter (z : E) (hzS : z ∈ S) (hz : r ≤ _root_.Dist.dist z c) : f z = u z := by
    by_cases hi : _root_.Dist.dist z c ≤ r
    · rw [hfinner z hi]
      exact hglue ⟨hzS, le_antisymm hi hz⟩
    · exact if_neg hi
  have htranslated : LipschitzOnWith (_root_.Max.max Kq Ku) (fun z => f (c + z))
      ((fun z => c + z) ⁻¹' S) := by
    apply lipschitzOnWith_of_radial_pieces (r := r) (hS.translate_preimage_right c)
    · intro z hz w hw
      change _root_.EDist.edist (f (c + z)) (f (c + w)) ≤ _
      rw [hfinner (c + z)
          (by simpa only [dist_eq_norm, add_sub_cancel_left] using (show ‖z‖ ≤ r from hz.2)),
        hfinner (c + w)
          (by simpa only [dist_eq_norm, add_sub_cancel_left] using (show ‖w‖ ≤ r from hw.2))]
      have h := (hq.weaken (le_max_left Kq Ku)) hz.1 hw.1
      simpa only [edist_dist, dist_add_left] using h
    · intro z hz w hw
      change _root_.EDist.edist (f (c + z)) (f (c + w)) ≤ _
      rw [hfouter (c + z) hz.1
          (by simpa only [dist_eq_norm, add_sub_cancel_left] using (show r ≤ ‖z‖ from hz.2)),
        hfouter (c + w) hw.1
          (by simpa only [dist_eq_norm, add_sub_cancel_left] using (show r ≤ ‖w‖ from hw.2))]
      have h := (hu.weaken (le_max_right Kq Ku)) hz.1 hw.1
      simpa only [edist_dist, dist_add_left] using h
  intro z hz w hw
  have h := htranslated (x := z - c)
    (by simpa only [_root_.Set.mem_preimage, add_sub_cancel] using hz) (y := w - c)
    (by simpa only [_root_.Set.mem_preimage, add_sub_cancel] using hw)
  simpa only [add_sub_cancel, edist_dist, dist_eq_norm, sub_sub_sub_cancel_right, f] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lipschitzOnWith_piecewise_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lipschitzOnWith_piecewise_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lipschitzOnWith_piecewise_closedBall ``Submission.DifferentialGeometry.Analysis.lipschitzOnWith_piecewise_closedBall

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*}

def attachBoundaryCap (u q : ℂ → F) (ρ : ℝ) (z : ℂ) : F :=
  if ‖z + 1‖ ≤ ρ then q z else u z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachBoundaryCap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachBoundaryCap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachBoundaryCap ``Submission.DifferentialGeometry.Analysis.attachBoundaryCap

theorem attachBoundaryCap_inner (u q : ℂ → F) (ρ : ℝ) {z : ℂ}
    (hz : ‖z + 1‖ ≤ ρ) : attachBoundaryCap u q ρ z = q z := if_pos hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachBoundaryCap_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachBoundaryCap_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachBoundaryCap_inner ``Submission.DifferentialGeometry.Analysis.attachBoundaryCap_inner

theorem attachBoundaryCap_outside (u q : ℂ → F) (ρ : ℝ) {z : ℂ}
    (hz : ρ < ‖z + 1‖) : attachBoundaryCap u q ρ z = u z :=
  if_neg (not_le.mpr hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachBoundaryCap_outside then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachBoundaryCap_outside"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachBoundaryCap_outside ``Submission.DifferentialGeometry.Analysis.attachBoundaryCap_outside

theorem attachBoundaryCap_on_lens (u q : ℂ → F) (ρ : ℝ) :
    EqOn (attachBoundaryCap u q ρ) q (boundaryLens ρ) := by
  intro z hz
  exact attachBoundaryCap_inner u q ρ
    (by simpa only [_root_.Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add] using hz.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachBoundaryCap_on_lens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachBoundaryCap_on_lens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachBoundaryCap_on_lens ``Submission.DifferentialGeometry.Analysis.attachBoundaryCap_on_lens

theorem attachBoundaryCap_outer (u q : ℂ → F) (ρ : ℝ)
    (hglue : _root_.Set.EqOn q u (_root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.sphere (-1) ρ))
    {z : ℂ} (hz : z ∈ _root_.Metric.closedBall (0 : ℂ) 1) (hρz : ρ ≤ ‖z + 1‖) :
    attachBoundaryCap u q ρ z = u z := by
  by_cases hi : ‖z + 1‖ ≤ ρ
  · rw [attachBoundaryCap_inner u q ρ hi]
    apply hglue
    refine ⟨hz, ?_⟩
    simpa only [_root_.Metric.mem_sphere, dist_eq_norm, sub_neg_eq_add] using le_antisymm hi hρz
  · exact if_neg hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachBoundaryCap_outer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachBoundaryCap_outer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachBoundaryCap_outer ``Submission.DifferentialGeometry.Analysis.attachBoundaryCap_outer

theorem attachBoundaryCap_boundary (u q : ℂ → F) (ρ : ℝ) (z : Circle) :
    attachBoundaryCap u q ρ z = if ‖(z : ℂ) + 1‖ ≤ ρ then q z else u z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachBoundaryCap_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachBoundaryCap_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachBoundaryCap_boundary ``Submission.DifferentialGeometry.Analysis.attachBoundaryCap_boundary

theorem attachBoundaryCap_boundary_complement (u q : ℂ → F) (ρ : ℝ)
    (hglue : _root_.Set.EqOn q u (_root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.sphere (-1) ρ))
    {z : Circle} (hz : ρ ≤ ‖(z : ℂ) + 1‖) : attachBoundaryCap u q ρ z = u z :=
  attachBoundaryCap_outer u q ρ hglue
    (by simp only [_root_.Metric.mem_closedBall, dist_zero_right, Circle.norm_coe, le_refl]) hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachBoundaryCap_boundary_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachBoundaryCap_boundary_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachBoundaryCap_boundary_complement ``Submission.DifferentialGeometry.Analysis.attachBoundaryCap_boundary_complement

theorem attachBoundaryCap_lipschitzOn [PseudoEMetricSpace F]
    {u q : ℂ → F} {ρ : ℝ} {Ku Kq : ℝ≥0}
    (hu : LipschitzOnWith Ku u (_root_.Metric.closedBall (0 : ℂ) 1))
    (hq : LipschitzOnWith Kq q (_root_.Metric.closedBall (0 : ℂ) 1))
    (hglue : _root_.Set.EqOn q u (_root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.sphere (-1) ρ)) :
    LipschitzOnWith (_root_.Max.max Kq Ku) (attachBoundaryCap u q ρ) (_root_.Metric.closedBall (0 : ℂ) 1) := by
  change LipschitzOnWith (_root_.Max.max Kq Ku) (fun z : ℂ => if ‖z + 1‖ ≤ ρ then q z else u z) _
  simpa only [dist_eq_norm, sub_neg_eq_add] using
    lipschitzOnWith_piecewise_closedBall (convex_closedBall (0 : ℂ) 1) (-1) ρ hu hq hglue

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachBoundaryCap_lipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachBoundaryCap_lipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachBoundaryCap_lipschitzOn ``Submission.DifferentialGeometry.Analysis.attachBoundaryCap_lipschitzOn

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.Metric _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private def quadraticPlaneEnergyDensity
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (f : ℂ → F) (z : ℂ) : ℝ :=
  (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
    A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.quadraticPlaneEnergyDensity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.quadraticPlaneEnergyDensity target :: scope.openDecls } }

private theorem quadraticPlaneEnergyDensity_congr
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) {f g : ℂ → F} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) :
    quadraticPlaneEnergyDensity A f z = quadraticPlaneEnergyDensity A g z := by
  unfold quadraticPlaneEnergyDensity
  rw [h.fderiv_eq, h.eq_of_nhds]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.quadraticPlaneEnergyDensity_congr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.quadraticPlaneEnergyDensity_congr target :: scope.openDecls } }

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem attachBoundaryCap_eventuallyEq_inner
    (u q : ℂ → F) (ρ : ℝ) {z : ℂ} (hz : ‖z + 1‖ < ρ) :
    attachBoundaryCap u q ρ =ᶠ[𝓝 z] q := by
  have hc : Continuous (fun w : ℂ => ‖w + 1‖) := by fun_prop
  filter_upwards [(hc.tendsto z) (isOpen_Iio.mem_nhds hz)] with w hw
  exact attachBoundaryCap_inner u q ρ hw.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachBoundaryCap_eventuallyEq_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachBoundaryCap_eventuallyEq_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachBoundaryCap_eventuallyEq_inner ``Submission.DifferentialGeometry.Analysis.attachBoundaryCap_eventuallyEq_inner

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem attachBoundaryCap_eventuallyEq_outer
    (u q : ℂ → F) (ρ : ℝ) {z : ℂ} (hz : ρ < ‖z + 1‖) :
    attachBoundaryCap u q ρ =ᶠ[𝓝 z] u := by
  have hc : Continuous (fun w : ℂ => ‖w + 1‖) := by fun_prop
  filter_upwards [(hc.tendsto z) (isOpen_Ioi.mem_nhds hz)] with w hw
  exact attachBoundaryCap_outside u q ρ hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachBoundaryCap_eventuallyEq_outer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachBoundaryCap_eventuallyEq_outer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachBoundaryCap_eventuallyEq_outer ``Submission.DifferentialGeometry.Analysis.attachBoundaryCap_eventuallyEq_outer

theorem integral_quadratic_fderiv_attachBoundaryCap
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (u q : ℂ → F) (ρ : ℝ)
    (hg : _root_.MeasureTheory.IntegrableOn (fun z =>
      (A (attachBoundaryCap u q ρ z)
          (fderiv ℝ (attachBoundaryCap u q ρ) z 1)
          (fderiv ℝ (attachBoundaryCap u q ρ) z 1) +
        A (attachBoundaryCap u q ρ z)
          (fderiv ℝ (attachBoundaryCap u q ρ) z Complex.I)
          (fderiv ℝ (attachBoundaryCap u q ρ) z Complex.I)) / 2)
      (_root_.Metric.closedBall (0 : ℂ) 1)) :
    let e : (ℂ → F) → ℂ → ℝ := fun f z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
    (∫ z in _root_.Metric.closedBall (0 : ℂ) 1, e (attachBoundaryCap u q ρ) z) =
      (∫ z in boundaryLens ρ, e q z) +
        ∫ z in _root_.Metric.closedBall (0 : ℂ) 1 \ _root_.Metric.closedBall (-1) ρ, e u z := by
  let e : (ℂ → F) → ℂ → ℝ := quadraticPlaneEnergyDensity A
  let g := attachBoundaryCap u q ρ
  change (∫ z in _root_.Metric.closedBall (0 : ℂ) 1, e g z) =
    (∫ z in boundaryLens ρ, e q z) +
      ∫ z in _root_.Metric.closedBall (0 : ℂ) 1 \ _root_.Metric.closedBall (-1) ρ, e u z
  have hin : ∀ᵐ z ∂volume.restrict (boundaryLens ρ), z ∈ _root_.Metric.ball (-1 : ℂ) ρ := by
    have h := ae_mem_ball_of_measure_sphere_eq_zero
      (Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume (-1 : ℂ) ρ)
    exact h.filter_mono (_root_.MeasureTheory.ae_mono (Measure.restrict_mono _root_.Set.inter_subset_left le_rfl))
  have hinner : (∫ z in boundaryLens ρ, e g z) = ∫ z in boundaryLens ρ, e q z := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hin] with z hz
    apply quadraticPlaneEnergyDensity_congr
    exact attachBoundaryCap_eventuallyEq_inner u q ρ
      (by simpa only [_root_.Metric.mem_ball, dist_eq_norm, sub_neg_eq_add] using hz)
  have houter : (∫ z in _root_.Metric.closedBall (0 : ℂ) 1 \ _root_.Metric.closedBall (-1) ρ, e g z) =
      ∫ z in _root_.Metric.closedBall (0 : ℂ) 1 \ _root_.Metric.closedBall (-1) ρ, e u z := by
    apply _root_.MeasureTheory.setIntegral_congr_fun (measurableSet_closedBall.diff measurableSet_closedBall)
    intro z hz
    apply quadraticPlaneEnergyDensity_congr
    exact attachBoundaryCap_eventuallyEq_outer u q ρ
      (lt_of_not_ge (by simpa only [_root_.Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add] using hz.2))
  have hsplit := _root_.MeasureTheory.integral_inter_add_sdiff (t := _root_.Metric.closedBall (-1 : ℂ) ρ)
    measurableSet_closedBall hg
  change (∫ z in _root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.closedBall (-1) ρ, e g z) +
    (∫ z in _root_.Metric.closedBall (0 : ℂ) 1 \ _root_.Metric.closedBall (-1) ρ, e g z) =
      ∫ z in _root_.Metric.closedBall (0 : ℂ) 1, e g z at hsplit
  rw [_root_.Set.inter_comm] at hsplit
  change (∫ z in boundaryLens ρ, e g z) +
    (∫ z in _root_.Metric.closedBall (0 : ℂ) 1 \ _root_.Metric.closedBall (-1) ρ, e g z) =
      ∫ z in _root_.Metric.closedBall (0 : ℂ) 1, e g z at hsplit
  rw [hinner, houter] at hsplit
  exact hsplit.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachBoundaryCap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachBoundaryCap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachBoundaryCap ``Submission.DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachBoundaryCap

end DifferentialGeometry.Analysis

end
