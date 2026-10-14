import Submission.DifferentialGeometry.Topology.Circle.Logarithm
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Module.LocallyConvex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology.FixedPoint

theorem exists_zero_of_pos_radial_boundary
    (f : C(_root_.Metric.closedBall (0 : ℂ) 1, ℂ))
    (hboundary : ∀ z : _root_.Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ = 1 →
      0 < (_root_.Star.star (z : ℂ) * f z).re) : ∃ z, f z = 0 := by
  by_contra h
  push Not at h
  let D := _root_.Metric.closedBall (0 : ℂ) 1
  let : ContractibleSpace D := (convex_closedBall (0 : ℂ) 1).contractibleSpace
    ⟨0, by simp⟩
  let : LocallyPathConnectedSpace D := (convex_closedBall (0 : ℂ) 1).locallyPathConnectedSpace
  let z₀ : D := ⟨0, by simp [D]⟩
  let F : C(D, {z : ℂ // z ≠ 0}) := ⟨fun z ↦ ⟨f z, h z⟩, f.continuous.subtype_mk _⟩
  obtain ⟨g, ⟨_, hg⟩, _⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
    F z₀ (Complex.log (f z₀)) (Subtype.ext (Complex.exp_log (h z₀)))
  have hexp (z : D) : Complex.exp (g z) = f z :=
    congrArg Subtype.val (congrFun hg z)
  have hι (z : _root_.Circle) : (z : ℂ) ∈ D := by
    simpa only [D, _root_.Metric.mem_closedBall, dist_zero_right] using z.norm_coe.le
  let ι : C(_root_.Circle, D) :=
    ⟨fun z ↦ ⟨z, hι z⟩, continuous_subtype_val.subtype_mk hι⟩
  let q : _root_.Circle → ℂ := fun z ↦ _root_.Star.star (z : ℂ) * f (ι z)
  have hq : Continuous q := continuous_subtype_val.star.mul (f.continuous.comp ι.continuous)
  have hqpos (z : _root_.Circle) : 0 < (q z).re := hboundary (ι z) z.norm_coe
  have hqslit (z : _root_.Circle) : q z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (hqpos z))
  apply DifferentialGeometry.Topology.Circle.not_exists_continuous_logarithm
  refine ⟨⟨fun z ↦ g (ι z) - Complex.log (q z),
    (g.continuous.comp ι.continuous).sub (hq.clog hqslit)⟩, fun z ↦ ?_⟩
  change Complex.exp (g (ι z) - Complex.log (q z)) = (z : ℂ)
  rw [Complex.exp_sub, hexp, Complex.exp_log (Complex.slitPlane_ne_zero (hqslit z))]
  apply (div_eq_iff (Complex.slitPlane_ne_zero (hqslit z))).mpr
  have hunit : (z : ℂ) * _root_.Star.star (z : ℂ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, _root_.Circle.normSq_coe, Complex.ofReal_one]
  dsimp only [q]
  rw [← mul_assoc, hunit, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FixedPoint.exists_zero_of_pos_radial_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FixedPoint.exists_zero_of_pos_radial_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FixedPoint.exists_zero_of_pos_radial_boundary ``Submission.DifferentialGeometry.Topology.FixedPoint.exists_zero_of_pos_radial_boundary

private theorem exists_fixedPoint_closed_unitDisk_aux
    (f : C(_root_.Metric.closedBall (0 : ℂ) 1, _root_.Metric.closedBall (0 : ℂ) 1)) : ∃ z, f z = z := by
  by_contra h
  push Not at h
  let g : C(_root_.Metric.closedBall (0 : ℂ) 1, ℂ) :=
    ⟨fun z ↦ (z : ℂ) - (f z : ℂ),
      continuous_subtype_val.sub (continuous_subtype_val.comp f.continuous)⟩
  have hboundary (z : _root_.Metric.closedBall (0 : ℂ) 1) (hz : ‖(z : ℂ)‖ = 1) :
      0 < (_root_.Star.star (z : ℂ) * g z).re := by
    have hznorm : Complex.normSq (z : ℂ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hz, one_pow]
    have hwle : ‖(f z : ℂ)‖ ≤ 1 := by
      simpa only [_root_.Metric.mem_closedBall, dist_zero_right] using (f z).property
    have hwnorm : Complex.normSq (f z : ℂ) ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (f z : ℂ)]
    have hdiff : 0 < Complex.normSq ((z : ℂ) - (f z : ℂ)) :=
      Complex.normSq_pos.mpr (sub_ne_zero.mpr (fun he ↦ h z (Subtype.ext he.symm)))
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hznorm hwnorm hdiff
    change 0 < (_root_.Star.star (z : ℂ) * ((z : ℂ) - (f z : ℂ))).re
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im]
    nlinarith
  obtain ⟨z, hz⟩ := exists_zero_of_pos_radial_boundary g hboundary
  exact h z (Subtype.ext (sub_eq_zero.mp hz).symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.FixedPoint.exists_fixedPoint_closed_unitDisk_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.FixedPoint.exists_fixedPoint_closed_unitDisk_aux target :: scope.openDecls } }

theorem exists_fixedPoint_closedBall (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (f : C(_root_.Metric.closedBall c r, _root_.Metric.closedBall c r)) : ∃ z, f z = z := by
  rcases hr.eq_or_lt with hzero | hr
  · subst r
    let z : _root_.Metric.closedBall c 0 := ⟨c, by simp⟩
    refine ⟨z, Subtype.ext ?_⟩
    change (f z : ℂ) = c
    simpa only [_root_.Metric.mem_closedBall, dist_le_zero] using (f z).property
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have ha (z : _root_.Metric.closedBall (0 : ℂ) 1) : c + (r : ℂ) * (z : ℂ) ∈ _root_.Metric.closedBall c r := by
    have hz : ‖(z : ℂ)‖ ≤ 1 := by
      simpa only [_root_.Metric.mem_closedBall, dist_zero_right] using z.property
    rw [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hr.le
  let a : C(_root_.Metric.closedBall (0 : ℂ) 1, _root_.Metric.closedBall c r) :=
    ⟨fun z ↦ ⟨c + (r : ℂ) * (z : ℂ), ha z⟩, by fun_prop⟩
  have hb (y : _root_.Metric.closedBall c r) : ((y : ℂ) - c) / (r : ℂ) ∈ _root_.Metric.closedBall (0 : ℂ) 1 := by
    have hy : ‖(y : ℂ) - c‖ ≤ r := by
      simpa only [_root_.Metric.mem_closedBall, dist_eq_norm] using y.property
    rw [_root_.Metric.mem_closedBall, dist_zero_right, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    exact (div_le_one hr).mpr hy
  let b : C(_root_.Metric.closedBall c r, _root_.Metric.closedBall (0 : ℂ) 1) :=
    ⟨fun y ↦ ⟨((y : ℂ) - c) / (r : ℂ), hb y⟩, by fun_prop⟩
  have hab (y : _root_.Metric.closedBall c r) : a (b y) = y := by
    apply Subtype.ext
    change c + (r : ℂ) * (((y : ℂ) - c) / (r : ℂ)) = (y : ℂ)
    field_simp
    ring
  obtain ⟨z, hz⟩ := exists_fixedPoint_closed_unitDisk_aux (b.comp (f.comp a))
  exact ⟨a z, (hab (f (a z))).symm.trans (congrArg a hz)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FixedPoint.exists_fixedPoint_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FixedPoint.exists_fixedPoint_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FixedPoint.exists_fixedPoint_closedBall ``Submission.DifferentialGeometry.Topology.FixedPoint.exists_fixedPoint_closedBall

theorem exists_fixedPoint_closed_unitDisk
    (f : C(_root_.Metric.closedBall (0 : ℂ) 1, _root_.Metric.closedBall (0 : ℂ) 1)) : ∃ z, f z = z :=
  exists_fixedPoint_closedBall 0 zero_le_one f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FixedPoint.exists_fixedPoint_closed_unitDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FixedPoint.exists_fixedPoint_closed_unitDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FixedPoint.exists_fixedPoint_closed_unitDisk ``Submission.DifferentialGeometry.Topology.FixedPoint.exists_fixedPoint_closed_unitDisk

end DifferentialGeometry.Topology.FixedPoint
