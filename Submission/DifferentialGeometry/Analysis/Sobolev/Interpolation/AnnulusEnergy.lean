import Submission.DifferentialGeometry.Topology.LoopSpace.ThinAnnulus
import Submission.DifferentialGeometry.Analysis.Sobolev.Interpolation.Cylinder
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Polar
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Submission.DifferentialGeometry.Analysis.Integration.PlaneScaling
import Submission.DifferentialGeometry.Analysis.Integration.BallBoundary
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Analysis

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem thinAnnulusProjection_normalized_polar (R : ℝ) {p : ℝ × ℝ}
    (hp : 0 < p.1) :
    thinAnnulusProjection R
        (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)) =
      circleMap 0 R (2 * Real.pi * p.2 - Real.pi) := by
  let θ : ℝ := 2 * Real.pi * p.2 - Real.pi
  let c : Circle := ⟨circleMap 0 1 θ, by
    apply mem_sphere_zero_iff_norm.mpr
    simp only [norm_circleMap_zero, abs_one]⟩
  have hpolar : Complex.polarCoord.symm (p.1, θ) = p.1 • (c : ℂ) := by
    simp [c, Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I,
      Complex.real_smul, mul_add]
  change thinAnnulusProjection R (Complex.polarCoord.symm (p.1, θ)) = circleMap 0 R θ
  rw [hpolar, thinAnnulusProjection, radialDirection_pos_smul hp]
  simp only [c, circleMap_zero, Complex.ofReal_one, one_mul, Complex.real_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.thinAnnulusProjection_normalized_polar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.thinAnnulusProjection_normalized_polar target :: scope.openDecls } }

theorem attachThinAnnulus_normalized_polar
    (u v : ℂ → F) (r : F → F) {R h : ℝ} (hhR : h < R)
    {p : ℝ × ℝ} (hp : p.1 ∈ _root_.Set.Ioo (R - h) R) :
    attachThinAnnulus u v r R h
        (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)) =
      (r ∘ affineCylinderInterpolation h
        (fun t => v (circleMap 0 R (2 * Real.pi * t - Real.pi)))
        (fun t => u (circleMap 0 R (2 * Real.pi * t - Real.pi))))
          (p.1 - (R - h), p.2) := by
  have hp0 : 0 < p.1 := (sub_pos.mpr hhR).trans hp.1
  have hnorm : ‖Complex.polarCoord.symm
      (p.1, 2 * Real.pi * p.2 - Real.pi)‖ = p.1 := by
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp0]
  rw [attachThinAnnulus, if_neg (by simpa only [hnorm] using not_le.mpr hp.1),
    if_neg (by simpa only [hnorm] using not_le.mpr hp.2)]
  rw [thinAnnulusInterpolation, thinAnnulusProjection_normalized_polar R hp0,
    thinAnnulusParameter, hnorm]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachThinAnnulus_normalized_polar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachThinAnnulus_normalized_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachThinAnnulus_normalized_polar ``Submission.DifferentialGeometry.Analysis.attachThinAnnulus_normalized_polar

theorem fderiv_attachThinAnnulus_normalized_polar
    (u v : ℂ → F) (r : F → F) {R h : ℝ} (hhR : h < R)
    {p : ℝ × ℝ} (hp : p.1 ∈ _root_.Set.Ioo (R - h) R) :
    fderiv ℝ (fun q : ℝ × ℝ => attachThinAnnulus u v r R h
      (Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi))) p =
      fderiv ℝ (r ∘ affineCylinderInterpolation h
        (fun t => v (circleMap 0 R (2 * Real.pi * t - Real.pi)))
        (fun t => u (circleMap 0 R (2 * Real.pi * t - Real.pi))))
          (p.1 - (R - h), p.2) := by
  let H : ℝ × ℝ → F := r ∘ affineCylinderInterpolation h
    (fun t => v (circleMap 0 R (2 * Real.pi * t - Real.pi)))
    (fun t => u (circleMap 0 R (2 * Real.pi * t - Real.pi)))
  have heq : (fun q : ℝ × ℝ => attachThinAnnulus u v r R h
      (Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi))) =ᶠ[𝓝 p]
      (fun q => H (q - (R - h, 0))) := by
    filter_upwards [(continuous_fst.tendsto p) (isOpen_Ioo.mem_nhds hp)] with q hq
    simpa only [H, Prod.sub_def, sub_zero] using
      attachThinAnnulus_normalized_polar u v r hhR hq
  rw [heq.fderiv_eq]
  simpa only [Prod.sub_def, sub_zero, H] using
    (fderiv_comp_sub (𝕜 := ℝ) (f := H) (x := p) ((R - h, 0) : ℝ × ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv_attachThinAnnulus_normalized_polar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv_attachThinAnnulus_normalized_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv_attachThinAnnulus_normalized_polar ``Submission.DifferentialGeometry.Analysis.fderiv_attachThinAnnulus_normalized_polar

private theorem integral_rectangle_translate_fst (f : ℝ × ℝ → ℝ) (R h : ℝ) :
    (∫ p in _root_.Set.Icc (R - h) R ×ˢ _root_.Set.Icc (0 : ℝ) 1, f (p.1 - (R - h), p.2)) =
      ∫ p in _root_.Set.Icc (0 : ℝ) h ×ˢ _root_.Set.Icc (0 : ℝ) 1, f p := by
  let c : ℝ × ℝ := (R - h, 0)
  have hpre : (fun p : ℝ × ℝ => p + -c) ⁻¹'
      (_root_.Set.Icc (0 : ℝ) h ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      Icc (R - h) R ×ˢ _root_.Set.Icc (0 : ℝ) 1 := by
    ext p
    change ((0 ≤ p.1 + -(R - h) ∧ p.1 + -(R - h) ≤ h) ∧
        0 ≤ p.2 + -0 ∧ p.2 + -0 ≤ 1) ↔
      ((R - h ≤ p.1 ∧ p.1 ≤ R) ∧ 0 ≤ p.2 ∧ p.2 ≤ 1)
    simp only [neg_zero, add_zero]
    constructor
    · rintro ⟨hp, ht⟩
      exact ⟨⟨by linarith [hp.1], by linarith [hp.2]⟩, ht⟩
    · rintro ⟨hp, ht⟩
      exact ⟨⟨by linarith [hp.1], by linarith [hp.2]⟩, ht⟩
  have hi := (_root_.MeasureTheory.measurePreserving_add_right (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (ℝ × ℝ)) (-c)).setIntegral_preimage_emb
    (MeasurableEquiv.addRight (-c)).measurableEmbedding
      f (_root_.Set.Icc (0 : ℝ) h ×ˢ _root_.Set.Icc (0 : ℝ) 1)
  rw [hpre] at hi
  simpa only [c, Prod.add_def, Prod.neg_mk, neg_zero, add_zero, ← sub_eq_add_neg] using hi

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integral_rectangle_translate_fst
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integral_rectangle_translate_fst target :: scope.openDecls } }

theorem integral_normalized_polar_energy_attachThinAnnulus_eq
    (u v : ℂ → F) (r : F → F) {R h : ℝ} (hhR : h < R) :
    (∫ p in _root_.Set.Icc (R - h) R ×ˢ _root_.Set.Icc (0 : ℝ) 1,
      (‖fderiv ℝ (fun q : ℝ × ℝ => attachThinAnnulus u v r R h
          (Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi))) p (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (fun q : ℝ × ℝ => attachThinAnnulus u v r R h
          (Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi))) p (0, 1)‖ ^ 2) / 2) =
      ∫ p in _root_.Set.Icc (0 : ℝ) h ×ˢ _root_.Set.Icc (0 : ℝ) 1,
        (‖fderiv ℝ (r ∘ affineCylinderInterpolation h
            (fun t => v (circleMap 0 R (2 * Real.pi * t - Real.pi)))
            (fun t => u (circleMap 0 R (2 * Real.pi * t - Real.pi)))) p (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (r ∘ affineCylinderInterpolation h
            (fun t => v (circleMap 0 R (2 * Real.pi * t - Real.pi)))
            (fun t => u (circleMap 0 R (2 * Real.pi * t - Real.pi)))) p (0, 1)‖ ^ 2) / 2 := by
  let H : ℝ × ℝ → F := r ∘ affineCylinderInterpolation h
    (fun t => v (circleMap 0 R (2 * Real.pi * t - Real.pi)))
    (fun t => u (circleMap 0 R (2 * Real.pi * t - Real.pi)))
  let e : ℝ × ℝ → ℝ := fun p =>
    (‖fderiv ℝ H p (1, 0)‖ ^ 2 + ‖fderiv ℝ H p (0, 1)‖ ^ 2) / 2
  have hrad : ∀ᵐ p ∂volume.restrict (_root_.Set.Icc (R - h) R ×ˢ _root_.Set.Icc (0 : ℝ) 1),
      p.1 ∈ _root_.Set.Ioo (R - h) R := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    apply Measure.quasiMeasurePreserving_fst.ae
    rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    exact _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo
  trans ∫ p in _root_.Set.Icc (R - h) R ×ˢ _root_.Set.Icc (0 : ℝ) 1, e (p.1 - (R - h), p.2)
  · apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hrad] with p hp
    rw [fderiv_attachThinAnnulus_normalized_polar u v r hhR hp]
  · exact integral_rectangle_translate_fst e R h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_normalized_polar_energy_attachThinAnnulus_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_normalized_polar_energy_attachThinAnnulus_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_normalized_polar_energy_attachThinAnnulus_eq ``Submission.DifferentialGeometry.Analysis.integral_normalized_polar_energy_attachThinAnnulus_eq

end Normed

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem integral_annulus_energy_attachThinAnnulus_le
    (u v : ℂ → F) (r : F → F) {R h : ℝ} (hhR : h < R) {K : ℝ≥0}
    (hg : LipschitzWith K (attachThinAnnulus u v r R h)) :
    (∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc (R - h) R},
      (‖fderiv ℝ (attachThinAnnulus u v r R h) z 1‖ ^ 2 +
        ‖fderiv ℝ (attachThinAnnulus u v r R h) z Complex.I‖ ^ 2) / 2) ≤
      (2 * Real.pi) * _root_.Max.max R (((2 * Real.pi) ^ 2 * (R - h))⁻¹) *
        ∫ p in _root_.Set.Icc (0 : ℝ) h ×ˢ _root_.Set.Icc (0 : ℝ) 1,
          (‖fderiv ℝ (r ∘ affineCylinderInterpolation h
              (fun t => v (circleMap 0 R (2 * Real.pi * t - Real.pi)))
              (fun t => u (circleMap 0 R (2 * Real.pi * t - Real.pi)))) p (1, 0)‖ ^ 2 +
            ‖fderiv ℝ (r ∘ affineCylinderInterpolation h
              (fun t => v (circleMap 0 R (2 * Real.pi * t - Real.pi)))
              (fun t => u (circleMap 0 R (2 * Real.pi * t - Real.pi)))) p (0, 1)‖ ^ 2) / 2 := by
  have hi := integral_annulus_fderiv_energy_le hg (R := R) (sub_pos.mpr hhR)
  rw [integral_normalized_polar_energy_attachThinAnnulus_eq u v r hhR] at hi
  exact hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_annulus_energy_attachThinAnnulus_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_annulus_energy_attachThinAnnulus_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_annulus_energy_attachThinAnnulus_le ``Submission.DifferentialGeometry.Analysis.integral_annulus_energy_attachThinAnnulus_le

theorem integral_annulus_energy_attachThinAnnulus_le_of_lipschitz
    {u v : ℂ → F} {r : F → F} {R h : ℝ} {Ku Kv Kr : ℝ≥0}
    (hh : 0 < h) (hhR : h < R) (hu : LipschitzWith Ku u)
    (hv : LipschitzWith Kv v) (hr : LipschitzWith Kr r)
    (hru : ∀ z, ‖z‖ = R → r (u z) = u z)
    (hrv : ∀ z, ‖z‖ = R → r (v z) = v z) :
    (∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc (R - h) R},
      (‖fderiv ℝ (attachThinAnnulus u v r R h) z 1‖ ^ 2 +
        ‖fderiv ℝ (attachThinAnnulus u v r R h) z Complex.I‖ ^ 2) / 2) ≤
      (2 * Real.pi) * _root_.Max.max R (((2 * Real.pi) ^ 2 * (R - h))⁻¹) *
        ∫ p in _root_.Set.Icc (0 : ℝ) h ×ˢ _root_.Set.Icc (0 : ℝ) 1,
          (‖fderiv ℝ (r ∘ affineCylinderInterpolation h
              (fun t => v (circleMap 0 R (2 * Real.pi * t - Real.pi)))
              (fun t => u (circleMap 0 R (2 * Real.pi * t - Real.pi)))) p (1, 0)‖ ^ 2 +
            ‖fderiv ℝ (r ∘ affineCylinderInterpolation h
              (fun t => v (circleMap 0 R (2 * Real.pi * t - Real.pi)))
              (fun t => u (circleMap 0 R (2 * Real.pi * t - Real.pi)))) p (0, 1)‖ ^ 2) / 2 := by
  obtain ⟨K, hK⟩ := attachThinAnnulus_lipschitz hh hhR hu hv hr hru hrv
  exact integral_annulus_energy_attachThinAnnulus_le u v r hhR hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_annulus_energy_attachThinAnnulus_le_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_annulus_energy_attachThinAnnulus_le_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_annulus_energy_attachThinAnnulus_le_of_lipschitz ``Submission.DifferentialGeometry.Analysis.integral_annulus_energy_attachThinAnnulus_le_of_lipschitz

end InnerProduct

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.Metric _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open _root_.Submission.DifferentialGeometry.Topology
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

theorem attachThinAnnulus_eventuallyEq_inner
    (u v : ℂ → F) (r : F → F) (R h : ℝ) {z : ℂ} (hz : ‖z‖ < R - h) :
    attachThinAnnulus u v r R h =ᶠ[𝓝 z]
      (fun w => v ((R / (R - h)) • w)) := by
  have hnb : Metric.ball (0 : ℂ) (R - h) ∈ 𝓝 z :=
    isOpen_ball.mem_nhds (by simpa only [_root_.Metric.mem_ball, dist_zero_right] using hz)
  filter_upwards [hnb] with w hw
  exact attachThinAnnulus_inner u v r R h
    (le_of_lt (by simpa only [_root_.Metric.mem_ball, dist_zero_right] using hw))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachThinAnnulus_eventuallyEq_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachThinAnnulus_eventuallyEq_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachThinAnnulus_eventuallyEq_inner ``Submission.DifferentialGeometry.Analysis.attachThinAnnulus_eventuallyEq_inner

theorem attachThinAnnulus_eventuallyEq_outer
    (u v : ℂ → F) (r : F → F) {R h : ℝ} (hh : 0 < h)
    {z : ℂ} (hz : R < ‖z‖) : attachThinAnnulus u v r R h =ᶠ[𝓝 z] u := by
  have hnb : {w : ℂ | R < ‖w‖} ∈ 𝓝 z :=
    (continuous_norm.tendsto z) (isOpen_Ioi.mem_nhds hz)
  filter_upwards [hnb] with w hw
  exact attachThinAnnulus_outer u v r hh hw.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachThinAnnulus_eventuallyEq_outer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachThinAnnulus_eventuallyEq_outer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachThinAnnulus_eventuallyEq_outer ``Submission.DifferentialGeometry.Analysis.attachThinAnnulus_eventuallyEq_outer

theorem integral_quadratic_fderiv_attachThinAnnulus_inner
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (u v : ℂ → F) (r : F → F)
    {R h : ℝ} (hh : 0 < h) (hhR : h < R) :
    (∫ z in Metric.closedBall (0 : ℂ) (R - h),
      (A (attachThinAnnulus u v r R h z)
          (fderiv ℝ (attachThinAnnulus u v r R h) z 1)
          (fderiv ℝ (attachThinAnnulus u v r R h) z 1) +
        A (attachThinAnnulus u v r R h z)
          (fderiv ℝ (attachThinAnnulus u v r R h) z Complex.I)
          (fderiv ℝ (attachThinAnnulus u v r R h) z Complex.I)) / 2) =
      ∫ z in Metric.closedBall (0 : ℂ) R,
        (A (v z) (fderiv ℝ v z 1) (fderiv ℝ v z 1) +
          A (v z) (fderiv ℝ v z Complex.I) (fderiv ℝ v z Complex.I)) / 2 := by
  change (∫ z in Metric.closedBall (0 : ℂ) (R - h),
      quadraticPlaneEnergyDensity A (attachThinAnnulus u v r R h) z) =
    ∫ z in Metric.closedBall (0 : ℂ) R, quadraticPlaneEnergyDensity A v z
  trans ∫ z in Metric.closedBall (0 : ℂ) (R - h),
    quadraticPlaneEnergyDensity A (fun w => v ((R / (R - h)) • w)) z
  · apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [ae_mem_ball_of_measure_sphere_eq_zero
      (Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume (0 : ℂ) (R - h))] with z hz
    apply quadraticPlaneEnergyDensity_congr
    exact attachThinAnnulus_eventuallyEq_inner u v r R h
      (by simpa only [_root_.Metric.mem_ball, dist_zero_right] using hz)
  · exact integral_quadratic_fderiv_comp_smul_closedBall A v
      (sub_pos.mpr hhR) (hh.trans hhR)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachThinAnnulus_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachThinAnnulus_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachThinAnnulus_inner ``Submission.DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachThinAnnulus_inner

theorem integral_quadratic_fderiv_attachThinAnnulus_outer
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (u v : ℂ → F) (r : F → F)
    {R h : ℝ} (hh : 0 < h) (Q : ℝ) :
    (∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall (0 : ℂ) R,
      (A (attachThinAnnulus u v r R h z)
          (fderiv ℝ (attachThinAnnulus u v r R h) z 1)
          (fderiv ℝ (attachThinAnnulus u v r R h) z 1) +
        A (attachThinAnnulus u v r R h z)
          (fderiv ℝ (attachThinAnnulus u v r R h) z Complex.I)
          (fderiv ℝ (attachThinAnnulus u v r R h) z Complex.I)) / 2) =
      ∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall (0 : ℂ) R,
        (A (u z) (fderiv ℝ u z 1) (fderiv ℝ u z 1) +
          A (u z) (fderiv ℝ u z Complex.I) (fderiv ℝ u z Complex.I)) / 2 := by
  apply _root_.MeasureTheory.setIntegral_congr_fun (measurableSet_closedBall.diff measurableSet_closedBall)
  intro z hz
  apply quadraticPlaneEnergyDensity_congr
  exact attachThinAnnulus_eventuallyEq_outer u v r hh
    (lt_of_not_ge (by simpa only [_root_.Metric.mem_closedBall, dist_zero_right] using hz.2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachThinAnnulus_outer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachThinAnnulus_outer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachThinAnnulus_outer ``Submission.DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachThinAnnulus_outer

theorem integral_quadratic_fderiv_attachThinAnnulus_closedBall
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (u v : ℂ → F) (r : F → F)
    {R h Q : ℝ} (hh : 0 < h) (hhR : h < R) (hRQ : R ≤ Q)
    (hg : _root_.MeasureTheory.IntegrableOn (fun z =>
      (A (attachThinAnnulus u v r R h z)
          (fderiv ℝ (attachThinAnnulus u v r R h) z 1)
          (fderiv ℝ (attachThinAnnulus u v r R h) z 1) +
        A (attachThinAnnulus u v r R h z)
          (fderiv ℝ (attachThinAnnulus u v r R h) z Complex.I)
          (fderiv ℝ (attachThinAnnulus u v r R h) z Complex.I)) / 2)
      (Metric.closedBall (0 : ℂ) Q)) :
    let e : (ℂ → F) → ℂ → ℝ := fun f z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
    (∫ z in Metric.closedBall (0 : ℂ) Q, e (attachThinAnnulus u v r R h) z) =
      (∫ z in Metric.closedBall (0 : ℂ) R, e v z) +
        (∫ z in Metric.closedBall (0 : ℂ) R \ Metric.closedBall (0 : ℂ) (R - h),
          e (attachThinAnnulus u v r R h) z) +
        ∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall (0 : ℂ) R, e u z := by
  let e : (ℂ → F) → ℂ → ℝ := quadraticPlaneEnergyDensity A
  let g := attachThinAnnulus u v r R h
  change (∫ z in Metric.closedBall (0 : ℂ) Q, e g z) =
    (∫ z in Metric.closedBall (0 : ℂ) R, e v z) +
      (∫ z in Metric.closedBall (0 : ℂ) R \ Metric.closedBall (0 : ℂ) (R - h), e g z) +
      ∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall (0 : ℂ) R, e u z
  have hsubR : Metric.closedBall (0 : ℂ) R ⊆ Metric.closedBall (0 : ℂ) Q :=
    _root_.Metric.closedBall_subset_closedBall hRQ
  have hsuba : Metric.closedBall (0 : ℂ) (R - h) ⊆ Metric.closedBall (0 : ℂ) R :=
    _root_.Metric.closedBall_subset_closedBall (sub_le_self R hh.le)
  have hsplitR := _root_.MeasureTheory.setIntegral_sdiff measurableSet_closedBall hg hsubR
  have hsplita := _root_.MeasureTheory.setIntegral_sdiff measurableSet_closedBall (hg.mono_set hsubR) hsuba
  have hinner := integral_quadratic_fderiv_attachThinAnnulus_inner A u v r hh hhR
  have houter := integral_quadratic_fderiv_attachThinAnnulus_outer A u v r (R := R) hh Q
  change (∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall (0 : ℂ) R, e g z) =
    (∫ z in Metric.closedBall (0 : ℂ) Q, e g z) -
      ∫ z in Metric.closedBall (0 : ℂ) R, e g z at hsplitR
  change (∫ z in Metric.closedBall (0 : ℂ) R \ Metric.closedBall (0 : ℂ) (R - h), e g z) =
    (∫ z in Metric.closedBall (0 : ℂ) R, e g z) -
      ∫ z in Metric.closedBall (0 : ℂ) (R - h), e g z at hsplita
  change (∫ z in Metric.closedBall (0 : ℂ) (R - h), e g z) =
    ∫ z in Metric.closedBall (0 : ℂ) R, e v z at hinner
  change (∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall (0 : ℂ) R, e g z) =
    ∫ z in Metric.closedBall (0 : ℂ) Q \ Metric.closedBall (0 : ℂ) R, e u z at houter
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachThinAnnulus_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachThinAnnulus_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachThinAnnulus_closedBall ``Submission.DifferentialGeometry.Analysis.integral_quadratic_fderiv_attachThinAnnulus_closedBall

end DifferentialGeometry.Analysis

end
