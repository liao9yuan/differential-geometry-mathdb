-- Modified 2026-04-28: updated internal import paths for project namespace
-- Modified 2026-05-16: style-warning cleanup
import Submission.DifferentialGeometry.External.DeGiorgi.BallScaling
import Submission.DifferentialGeometry.External.DeGiorgi.BallExtension
import Submission.DifferentialGeometry.External.DeGiorgi.PositivePart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Chapter 06: Localization Helpers

This file exposes reusable local restriction and simple transport lemmas for
subsolutions, supersolutions, and solutions on balls. These results are used
throughout the Harnack and Holder arguments.
-/

noncomputable section

open _root_.MeasureTheory

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

namespace EllipticCoeff

/-- Restrict an elliptic coefficient field to a smaller domain by keeping the
same coefficient matrix and constants and shrinking the a.e. coercivity domain.
-/
noncomputable def restrict
    {Ω Ω' : Set E} (A : EllipticCoeff d Ω) (hsub : Ω' ⊆ Ω) :
    EllipticCoeff d Ω' where
  a := A.a
  lam := A.lam
  Λ := A.Λ
  measurable_comp := A.measurable_comp
  hlam := A.hlam
  hΛ := A.hΛ
  coercive := _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub A.coercive
  coercive_inv := _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub A.coercive_inv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.restrict then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.restrict ``Submission.DeGiorgi.EllipticCoeff.restrict

@[simp] theorem restrict_a
    {Ω Ω' : Set E} (A : EllipticCoeff d Ω) (hsub : Ω' ⊆ Ω) :
    (A.restrict hsub).a = A.a := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.restrict_a then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.restrict_a"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.restrict_a ``Submission.DeGiorgi.EllipticCoeff.restrict_a

@[simp] theorem restrict_lam
    {Ω Ω' : Set E} (A : EllipticCoeff d Ω) (hsub : Ω' ⊆ Ω) :
    (A.restrict hsub).lam = A.lam := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.restrict_lam then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.restrict_lam"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.restrict_lam ``Submission.DeGiorgi.EllipticCoeff.restrict_lam

@[simp] theorem restrict_Λ
    {Ω Ω' : Set E} (A : EllipticCoeff d Ω) (hsub : Ω' ⊆ Ω) :
    (A.restrict hsub).Λ = A.Λ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.restrict_Λ then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.restrict_Λ"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.restrict_Λ ``Submission.DeGiorgi.EllipticCoeff.restrict_Λ

end EllipticCoeff

namespace NormalizedEllipticCoeff

/-- Restrict a normalized elliptic coefficient field to a smaller domain. -/
  noncomputable def restrict
    {Ω Ω' : Set E} (A : NormalizedEllipticCoeff d Ω) (hsub : Ω' ⊆ Ω) :
    NormalizedEllipticCoeff d Ω' := by
  refine ⟨A.1.restrict hsub, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.NormalizedEllipticCoeff.restrict then
    throwError "Refusing to shadow existing declaration DeGiorgi.NormalizedEllipticCoeff.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.NormalizedEllipticCoeff.restrict ``Submission.DeGiorgi.NormalizedEllipticCoeff.restrict

end NormalizedEllipticCoeff

omit [NeZero d] in
theorem affine_preimage_ball_mul
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) :
    (fun z : E => x₀ + R • z) ⁻¹' Metric.ball x₀ (R * ρ) = Metric.ball (0 : E) ρ := by
  ext z
  simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
  constructor
  · intro hz
    have hsub : x₀ + R • z - x₀ = R • z := by
      abel
    rw [hsub, norm_smul, Real.norm_of_nonneg hR.le] at hz
    have hiff : R * ‖z‖ < R * ρ ↔ ‖z‖ < ρ := by
      constructor
      · intro hh
        nlinarith
      · intro hh
        nlinarith
    simpa [sub_zero] using hiff.mp hz
  · intro hz
    have hsub : x₀ + R • z - x₀ = R • z := by
      abel
    rw [hsub, norm_smul, Real.norm_of_nonneg hR.le]
    have hiff : R * ‖z‖ < R * ρ ↔ ‖z‖ < ρ := by
      constructor
      · intro hh
        nlinarith
      · intro hh
        nlinarith
    have hz' : ‖z‖ < ρ := by
      simpa [sub_zero] using hz
    exact hiff.mpr hz'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.affine_preimage_ball_mul then
    throwError "Refusing to shadow existing declaration DeGiorgi.affine_preimage_ball_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.affine_preimage_ball_mul ``Submission.DeGiorgi.affine_preimage_ball_mul

omit [NeZero d] in
private theorem affine_map_restrict_ball_mul
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) :
    Measure.map (fun z : E => x₀ + R • z) (volume.restrict (Metric.ball (0 : E) ρ)) =
      ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
        (volume.restrict (Metric.ball x₀ (R * ρ))) := by
  have hmeas : Measurable (fun z : E => x₀ + R • z) :=
    (_root_.MeasurableAdd.measurable_const_add x₀).comp (_root_.MeasurableConstSMul.measurable_const_smul R)
  calc
    Measure.map (fun z : E => x₀ + R • z) (volume.restrict (Metric.ball (0 : E) ρ))
        = Measure.map (fun z : E => x₀ + R • z)
            (volume.restrict ((fun z : E => x₀ + R • z) ⁻¹' Metric.ball x₀ (R * ρ))) := by
              rw [affine_preimage_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := ρ) hR]
    _ = (Measure.map (fun z : E => x₀ + R • z) _root_.MeasureTheory.MeasureSpace.volume).restrict (Metric.ball x₀ (R * ρ)) := by
          rw [Measure.restrict_map hmeas measurableSet_ball]
    _ = (ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)).restrict
          (Metric.ball x₀ (R * ρ)) := by
            rw [show (fun z : E => x₀ + R • z) = (fun z => x₀ + z) ∘ (fun z => R • z) from rfl]
            rw [← Measure.map_map (_root_.MeasurableAdd.measurable_const_add x₀) (_root_.MeasurableConstSMul.measurable_const_smul R)]
            rw [Measure.map_addHaar_smul _root_.MeasureTheory.MeasureSpace.volume hR.ne']
            rw [Measure.map_smul, (_root_.MeasureTheory.measurePreserving_add_left _root_.MeasureTheory.MeasureSpace.volume x₀).map_eq, abs_inv]
    _ = ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
          (volume.restrict (Metric.ball x₀ (R * ρ))) := by
            rw [Measure.restrict_smul]

run_cmd do
  let target := ``Submission.DeGiorgi.affine_map_restrict_ball_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.affine_map_restrict_ball_mul target :: scope.openDecls } }

omit [NeZero d] in
private theorem affine_scale_measure_ne_zero
    {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) ≠ 0 := by
  rw [ENNReal.ofReal_ne_zero_iff]
  have hpow_ne : R ^ Module.finrank ℝ E ≠ 0 := by
    exact pow_ne_zero _ hR.ne'
  have habs_pos : 0 < |R ^ Module.finrank ℝ E| := by
    exact abs_pos.mpr hpow_ne
  exact inv_pos.mpr habs_pos

run_cmd do
  let target := ``Submission.DeGiorgi.affine_scale_measure_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.affine_scale_measure_ne_zero target :: scope.openDecls } }

omit [NeZero d] in
private theorem affineMeasurableEmbedding
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    MeasurableEmbedding (fun z : E => x₀ + R • z) :=
  ((MeasurableEquiv.addLeft x₀).measurableEmbedding).comp
    ((Homeomorph.smulOfNeZero R hR.ne').toMeasurableEquiv.measurableEmbedding)

run_cmd do
  let target := ``Submission.DeGiorgi.affineMeasurableEmbedding
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.affineMeasurableEmbedding target :: scope.openDecls } }

-- essSup rescaling: pushforward measure equality plus essSup-as-sInf manipulation
omit [NeZero d] in
theorem essSup_rescale_halfBall
    {x₀ : E} {R : ℝ} (hR : 0 < R) {u : E → ℝ} :
    essSup (fun z : E => u (x₀ + R • z))
        (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))) =
      essSup u (volume.restrict (Metric.ball x₀ (R / 2 : ℝ))) := by
  let μsrc : _root_.MeasureTheory.Measure E := volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))
  let μdst : _root_.MeasureTheory.Measure E := volume.restrict (Metric.ball x₀ (R / 2 : ℝ))
  let T : E → E := fun z => x₀ + R • z
  have hmap :
      Measure.map T μsrc =
        ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • μdst := by
    have h := affine_map_restrict_ball_mul (d := d) (x₀ := x₀) (R := R)
      (ρ := (1 / 2 : ℝ)) hR
    rw [show R * (1 / 2 : ℝ) = R / 2 by ring] at h
    simpa [μsrc, μdst, T] using h
  have hiff :
      ∀ a : ℝ,
        (∀ᵐ z ∂μsrc, u (T z) ≤ a) ↔ ∀ᵐ x ∂μdst, u x ≤ a := by
    intro a
    constructor
    · intro h
      have hmap_ae : ∀ᵐ x ∂ Measure.map T μsrc, u x ≤ a :=
        (affineMeasurableEmbedding (d := d) (x₀ := x₀) (R := R) hR).ae_map_iff.2 h
      rw [hmap, Measure.ae_ennreal_smul_measure_eq
        (affine_scale_measure_ne_zero (d := d) hR)] at hmap_ae
      exact hmap_ae
    · intro h
      have hmap_ae : ∀ᵐ x ∂ Measure.map T μsrc, u x ≤ a := by
        rw [hmap]
        rw [Measure.ae_ennreal_smul_measure_eq
          (affine_scale_measure_ne_zero (d := d) hR)]
        exact h
      exact (affineMeasurableEmbedding (d := d) (x₀ := x₀) (R := R) hR).ae_map_iff.1 hmap_ae
  rw [essSup_eq_sInf, essSup_eq_sInf]
  congr 1
  ext a
  simpa [μsrc, μdst, T, _root_.MeasureTheory.ae_iff, not_le] using hiff a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.essSup_rescale_halfBall then
    throwError "Refusing to shadow existing declaration DeGiorgi.essSup_rescale_halfBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.essSup_rescale_halfBall ``Submission.DeGiorgi.essSup_rescale_halfBall

-- essInf rescaling: pushforward measure equality plus essInf-as-sSup manipulation
omit [NeZero d] in
theorem essInf_rescale_halfBall
    {x₀ : E} {R : ℝ} (hR : 0 < R) {u : E → ℝ} :
    essInf (fun z : E => u (x₀ + R • z))
        (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))) =
      essInf u (volume.restrict (Metric.ball x₀ (R / 2 : ℝ))) := by
  let μsrc : _root_.MeasureTheory.Measure E := volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))
  let μdst : _root_.MeasureTheory.Measure E := volume.restrict (Metric.ball x₀ (R / 2 : ℝ))
  let T : E → E := fun z => x₀ + R • z
  have hmap :
      Measure.map T μsrc =
        ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • μdst := by
    have h := affine_map_restrict_ball_mul (d := d) (x₀ := x₀) (R := R)
      (ρ := (1 / 2 : ℝ)) hR
    rw [show R * (1 / 2 : ℝ) = R / 2 by ring] at h
    simpa [μsrc, μdst, T] using h
  have hiff :
      ∀ a : ℝ,
        (∀ᵐ z ∂μsrc, a ≤ u (T z)) ↔ ∀ᵐ x ∂μdst, a ≤ u x := by
    intro a
    constructor
    · intro h
      have hmap_ae : ∀ᵐ x ∂ Measure.map T μsrc, a ≤ u x :=
        (affineMeasurableEmbedding (d := d) (x₀ := x₀) (R := R) hR).ae_map_iff.2 h
      rw [hmap, Measure.ae_ennreal_smul_measure_eq
        (affine_scale_measure_ne_zero (d := d) hR)] at hmap_ae
      exact hmap_ae
    · intro h
      have hmap_ae : ∀ᵐ x ∂ Measure.map T μsrc, a ≤ u x := by
        rw [hmap]
        rw [Measure.ae_ennreal_smul_measure_eq
          (affine_scale_measure_ne_zero (d := d) hR)]
        exact h
      exact (affineMeasurableEmbedding (d := d) (x₀ := x₀) (R := R) hR).ae_map_iff.1 hmap_ae
  rw [essInf_eq_sSup, essInf_eq_sSup]
  congr 1
  ext a
  simpa [μsrc, μdst, T, _root_.MeasureTheory.ae_iff, not_le] using hiff a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.essInf_rescale_halfBall then
    throwError "Refusing to shadow existing declaration DeGiorgi.essInf_rescale_halfBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.essInf_rescale_halfBall ``Submission.DeGiorgi.essInf_rescale_halfBall

omit [NeZero d] in
private lemma ball_indicator_support_subset_closedBall
    {c : E} {r : ℝ} {φ : E → ℝ} :
    Function.support ((Metric.ball c r).indicator φ) ⊆ Metric.closedBall c r := by
  intro x hx
  by_contra hx_closed
  have hxball : x ∉ Metric.ball c r := by
    intro hxball
    exact hx_closed (Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hxball)))
  have hzero : (Metric.ball c r).indicator φ x = 0 := by
    simp [hxball]
  exact hx hzero

run_cmd do
  let target := ``Submission.DeGiorgi.ball_indicator_support_subset_closedBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.ball_indicator_support_subset_closedBall target :: scope.openDecls } }

omit [NeZero d] in
private lemma ball_indicator_tsupport_subset_closedBall
    {c : E} {r : ℝ} {φ : E → ℝ} :
    tsupport ((Metric.ball c r).indicator φ) ⊆ Metric.closedBall c r := by
  calc
    tsupport ((Metric.ball c r).indicator φ)
        ⊆ closure (Function.support ((Metric.ball c r).indicator φ)) := by
          simp [tsupport]
    _ ⊆ closure (Metric.closedBall c r) := by
          exact closure_mono
            (ball_indicator_support_subset_closedBall (c := c) (r := r) (φ := φ))
    _ = Metric.closedBall c r := by
          rw [(Metric.isClosed_closedBall : IsClosed (Metric.closedBall c r)).closure_eq]

run_cmd do
  let target := ``Submission.DeGiorgi.ball_indicator_tsupport_subset_closedBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.ball_indicator_tsupport_subset_closedBall target :: scope.openDecls } }

theorem memH01_indicator_ball_of_closedBall_subset
    {Ω : Set E} (hΩ : IsOpen Ω)
    {c : E} {r : ℝ} (_hr : 0 < r)
    (hsub : Metric.closedBall c r ⊆ Ω)
    {φ : E → ℝ} (hφ0 : MemH01 φ (Metric.ball c r)) :
    MemH01 ((Metric.ball c r).indicator φ) Ω := by
  let _ := _hr
  let hφ0_real : MemW01p (ENNReal.ofReal (2 : ℝ)) φ (Metric.ball c r) := by
    simpa using hφ0
  have hball0 : MemW01p 2 ((Metric.ball c r).indicator φ) Set.univ := by
    simpa using
      (zeroExtend_memW01p_p (d := d) Metric.isOpen_ball
        (p := 2) (by norm_num : (1 : ℝ) < 2) hφ0_real)
  let hballw : MemW1pWitness 2 ((Metric.ball c r).indicator φ) Set.univ :=
    MemW1p.someWitness (MemW01p.memW1p hball0)
  have hball_memW1p_Ω :
      MemW1p (ENNReal.ofReal (2 : ℝ)) ((Metric.ball c r).indicator φ) Ω := by
    simpa using (hballw.restrict hΩ (by intro x hx; simp)).memW1p
  have hcompact :
      HasCompactSupport ((Metric.ball c r).indicator φ) := by
    refine HasCompactSupport.intro'
      (_root_.ProperSpace.isCompact_closedBall c r) Metric.isClosed_closedBall ?_
    intro x hx
    have hxball : x ∉ Metric.ball c r := by
      intro hxball
      exact hx (Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hxball)))
    simp [hxball]
  have htsub : tsupport ((Metric.ball c r).indicator φ) ⊆ Ω := by
    exact (ball_indicator_tsupport_subset_closedBall (c := c) (r := r) (φ := φ)).trans hsub
  simpa using
    (memW01p_of_memW1p_of_tsupport_subset
      (d := d) hΩ (by norm_num : (1 : ℝ) < 2) hball_memW1p_Ω hcompact htsub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.memH01_indicator_ball_of_closedBall_subset then
    throwError "Refusing to shadow existing declaration DeGiorgi.memH01_indicator_ball_of_closedBall_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.memH01_indicator_ball_of_closedBall_subset ``Submission.DeGiorgi.memH01_indicator_ball_of_closedBall_subset

noncomputable def ballIndicatorWitnessOn
    {Ω : Set E} (hΩ : IsOpen Ω)
    {c : E} {r : ℝ} {φ : E → ℝ}
    (hφ0 : MemH01 φ (Metric.ball c r))
    (hφ : MemW1pWitness 2 φ (Metric.ball c r)) :
    MemW1pWitness 2 ((Metric.ball c r).indicator φ) Ω := by
  let hφ0_real : MemW01p (ENNReal.ofReal (2 : ℝ)) φ (Metric.ball c r) := by
    simpa using hφ0
  let hφ_real : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) φ (Metric.ball c r) := by
    refine
      { memLp := ?_
        weakGrad := hφ.weakGrad
        weakGrad_component_memLp := ?_
        isWeakGrad := hφ.isWeakGrad }
    · simpa using hφ.memLp
    · intro i
      simpa using hφ.weakGrad_component_memLp i
  let hφExtUniv : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) ((Metric.ball c r).indicator φ) Set.univ :=
    zeroExtendMemW1pWitnessP (d := d) Metric.isOpen_ball
      (p := 2) (by norm_num : (1 : ℝ) < 2) hφ0_real hφ_real
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by
    norm_num
  simpa [htwo] using hφExtUniv.restrict hΩ (by intro x hx; simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.ballIndicatorWitnessOn then
    throwError "Refusing to shadow existing declaration DeGiorgi.ballIndicatorWitnessOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.ballIndicatorWitnessOn ``Submission.DeGiorgi.ballIndicatorWitnessOn

omit [NeZero d] in
private lemma cast_MemW1pWitness_weakGrad
    {p q : ENNReal} {Ω : Set E} {f : E → ℝ}
    (hpq : p = q) (h : MemW1pWitness p f Ω) :
    (cast (by cases hpq; rfl : MemW1pWitness p f Ω = MemW1pWitness q f Ω) h).weakGrad =
      h.weakGrad := by
  cases hpq
  rfl

run_cmd do
  let target := ``Submission.DeGiorgi.cast_MemW1pWitness_weakGrad
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.cast_MemW1pWitness_weakGrad target :: scope.openDecls } }

@[simp] private lemma ballIndicatorWitnessOn_weakGrad_apply
    {Ω : Set E} (hΩ : IsOpen Ω)
    {c : E} {r : ℝ} {φ : E → ℝ}
    (hφ0 : MemH01 φ (Metric.ball c r))
    (hφ : MemW1pWitness 2 φ (Metric.ball c r))
    (x : E) (i : Fin d) :
    (ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ).weakGrad x i =
      (Metric.ball c r).indicator (fun y => hφ.weakGrad y i) x := by
  let hφ0_real : MemW01p (ENNReal.ofReal (2 : ℝ)) φ (Metric.ball c r) := by
    simpa using hφ0
  let hφ_real : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) φ (Metric.ball c r) := by
    refine
      { memLp := ?_
        weakGrad := hφ.weakGrad
        weakGrad_component_memLp := ?_
        isWeakGrad := hφ.isWeakGrad }
    · simpa using hφ.memLp
    · intro j
      simpa using hφ.weakGrad_component_memLp j
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by
    norm_num
  let hφExtUniv : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) ((Metric.ball c r).indicator φ) Set.univ :=
    zeroExtendMemW1pWitnessP (d := d) Metric.isOpen_ball
      (p := 2) (by norm_num : (1 : ℝ) < 2) hφ0_real hφ_real
  let hφExt : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) ((Metric.ball c r).indicator φ) Ω :=
    hφExtUniv.restrict hΩ (by intro y hy; simp)
  have hcast :
      (ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ).weakGrad = hφExt.weakGrad := by
    unfold ballIndicatorWitnessOn
    simpa [htwo, hφExtUniv, hφExt] using
      cast_MemW1pWitness_weakGrad htwo hφExt
  have hraw :
      hφExt.weakGrad x i = (Metric.ball c r).indicator (fun y => hφ.weakGrad y i) x := by
    simp [hφExt, hφExtUniv, zeroExtendMemW1pWitnessP, MemW1pWitness.restrict, hφ_real]
  simpa [hcast] using hraw

run_cmd do
  let target := ``Submission.DeGiorgi.ballIndicatorWitnessOn_weakGrad_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.ballIndicatorWitnessOn_weakGrad_apply target :: scope.openDecls } }

theorem bilinForm_ball_restrict_eq_zeroExtend
    {Ω : Set E} (hΩ : IsOpen Ω)
    (A : EllipticCoeff d Ω)
    {c : E} {r : ℝ} (_hr : 0 < r)
    (hsub : Metric.closedBall c r ⊆ Ω)
    {u : E → ℝ}
    (hu : MemW1pWitness 2 u Ω)
    {φ : E → ℝ}
    (hφ0 : MemH01 φ (Metric.ball c r))
    (hφ : MemW1pWitness 2 φ (Metric.ball c r)) :
    bilinFormOfCoeff (A.restrict (Metric.ball_subset_closedBall.trans hsub))
        (hu.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)) hφ =
      bilinFormOfCoeff A hu (ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ) := by
  let _ := _hr
  let hφExt : MemW1pWitness 2 ((Metric.ball c r).indicator φ) Ω :=
    ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ
  let A' : EllipticCoeff d (Metric.ball c r) :=
    A.restrict (Metric.ball_subset_closedBall.trans hsub)
  let hu' : MemW1pWitness 2 u (Metric.ball c r) :=
    hu.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)
  let fsmall : E → ℝ := fun x => bilinFormIntegrandOfCoeff A' hu' hφ x
  have hball_sub : Metric.ball c r ⊆ Ω := by
    intro x hx
    exact hsub (Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hx)))
  have hEq_ae :
      (fun x => (Metric.ball c r).indicator fsmall x) =ᵐ[volume.restrict Ω]
        fun x => bilinFormIntegrandOfCoeff A hu hφExt x := by
    filter_upwards with x
    by_cases hx : x ∈ Metric.ball c r
    · have hgradφ : hφExt.weakGrad x = hφ.weakGrad x := by
        apply PiLp.ext
        intro i
        simp [hφExt, ballIndicatorWitnessOn_weakGrad_apply, hx]
      simp [A', hu', fsmall, hφExt, hgradφ, EllipticCoeff.restrict,
        MemW1pWitness.restrict, hx, bilinFormIntegrandOfCoeff]
    · have hgradφ : hφExt.weakGrad x = 0 := by
        apply PiLp.ext
        intro i
        simp [hφExt, ballIndicatorWitnessOn_weakGrad_apply, hx]
      simp [A', hu', fsmall, hφExt, hgradφ, EllipticCoeff.restrict,
        MemW1pWitness.restrict, hx, bilinFormIntegrandOfCoeff]
  calc
    bilinFormOfCoeff A' hu' hφ
      = ∫ x in Metric.ball c r, fsmall x ∂(volume.restrict Ω) := by
          simp [bilinFormOfCoeff, fsmall, Measure.restrict_restrict_of_subset hball_sub]
    _ = ∫ x, (Metric.ball c r).indicator fsmall x ∂(volume.restrict Ω) := by
          symm
          exact _root_.MeasureTheory.integral_indicator measurableSet_ball
    _ = ∫ x, bilinFormIntegrandOfCoeff A hu hφExt x ∂(volume.restrict Ω) := by
          exact _root_.MeasureTheory.integral_congr_ae hEq_ae
    _ = bilinFormOfCoeff A hu hφExt := by
          rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.bilinForm_ball_restrict_eq_zeroExtend then
    throwError "Refusing to shadow existing declaration DeGiorgi.bilinForm_ball_restrict_eq_zeroExtend"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.bilinForm_ball_restrict_eq_zeroExtend ``Submission.DeGiorgi.bilinForm_ball_restrict_eq_zeroExtend

noncomputable def MemW1pWitness.ofAeEq
    {Ω : Set E} {f g : E → ℝ}
    (hfg : f =ᵐ[volume.restrict Ω] g)
    (hw : MemW1pWitness 2 f Ω) :
    MemW1pWitness 2 g Ω := by
  refine
    { memLp := (_root_.MeasureTheory.memLp_congr_ae hfg).1 hw.memLp
      weakGrad := hw.weakGrad
      weakGrad_component_memLp := hw.weakGrad_component_memLp
      isWeakGrad := ?_ }
  intro i φ hφ hφ_supp hφ_sub
  have hweak := hw.isWeakGrad i φ hφ hφ_supp hφ_sub
  have hcongr :
      (fun x => g x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =ᵐ[volume.restrict Ω]
        (fun x => f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
    filter_upwards [hfg] with x hx
    simp [hx]
  calc
    ∫ x in Ω, g x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)
        = ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
            exact _root_.MeasureTheory.integral_congr_ae hcongr
    _ = -∫ x in Ω, hw.weakGrad x i * φ x := hweak

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.MemW1pWitness.ofAeEq then
    throwError "Refusing to shadow existing declaration DeGiorgi.MemW1pWitness.ofAeEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.MemW1pWitness.ofAeEq ``Submission.DeGiorgi.MemW1pWitness.ofAeEq

theorem IsSubsolution.congr_ae
    {Ω : Set E} {A : EllipticCoeff d Ω} {u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict Ω] v)
    (hsub : IsSubsolution A u) :
    IsSubsolution A v := by
  refine ⟨(MemW1pWitness.ofAeEq huv (MemW1p.someWitness hsub.1)).memW1p, ?_⟩
  intro hv φ hφ hφw hφ_nonneg
  let hu : MemW1pWitness 2 u Ω := MemW1pWitness.ofAeEq huv.symm hv
  have hineq : bilinFormOfCoeff A hu hφw ≤ 0 := hsub.2 hu φ hφ hφw hφ_nonneg
  change bilinFormOfCoeff A hv hφw ≤ 0 at hineq
  exact hineq

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DeGiorgi.IsSubsolution
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSubsolution.congr_ae then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSubsolution.congr_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSubsolution.congr_ae ``Submission.DeGiorgi.IsSubsolution.congr_ae

theorem IsSupersolution.congr_ae
    {Ω : Set E} {A : EllipticCoeff d Ω} {u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict Ω] v)
    (hsuper : IsSupersolution A u) :
    IsSupersolution A v := by
  refine ⟨(MemW1pWitness.ofAeEq huv (MemW1p.someWitness hsuper.1)).memW1p, ?_⟩
  intro hv φ hφ hφw hφ_nonneg
  let hu : MemW1pWitness 2 u Ω := MemW1pWitness.ofAeEq huv.symm hv
  have hineq : 0 ≤ bilinFormOfCoeff A hu hφw := hsuper.2 hu φ hφ hφw hφ_nonneg
  change 0 ≤ bilinFormOfCoeff A hv hφw at hineq
  exact hineq

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DeGiorgi.IsSupersolution
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSupersolution.congr_ae then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSupersolution.congr_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSupersolution.congr_ae ``Submission.DeGiorgi.IsSupersolution.congr_ae

theorem IsSolution.congr_ae
    {Ω : Set E} {A : EllipticCoeff d Ω} {u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict Ω] v)
    (hsol : IsSolution A u) :
    IsSolution A v := by
  exact ⟨hsol.1.congr_ae huv, hsol.2.congr_ae huv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSolution.congr_ae then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSolution.congr_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSolution.congr_ae ``Submission.DeGiorgi.IsSolution.congr_ae

theorem IsSubsolution.restrict_ball
    {Ω : Set E} (hΩ : IsOpen Ω)
    {c : E} {r : ℝ} (hr : 0 < r)
    {A : EllipticCoeff d Ω} {u : E → ℝ}
    (hsub : Metric.closedBall c r ⊆ Ω)
    (hu : IsSubsolution A u) :
    IsSubsolution (A.restrict (Metric.ball_subset_closedBall.trans hsub)) u := by
  rcases hu with ⟨hu_mem, hu_sub⟩
  let huw : MemW1pWitness 2 u Ω := MemW1p.someWitness hu_mem
  refine ⟨(huw.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)).memW1p, ?_⟩
  intro hu' φ hφ0 hφ hφ_nonneg
  have hφ0_big :
      MemH01 ((Metric.ball c r).indicator φ) Ω :=
    memH01_indicator_ball_of_closedBall_subset (d := d) hΩ hr hsub hφ0
  let hφBig : MemW1pWitness 2 ((Metric.ball c r).indicator φ) Ω :=
    ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ
  have hbig :
      bilinFormOfCoeff A huw hφBig ≤ 0 := by
    exact hu_sub huw _ hφ0_big hφBig (by
      intro x
      by_cases hx : x ∈ Metric.ball c r
      · simpa [hx] using hφ_nonneg x
      · simp [hx])
  calc
    bilinFormOfCoeff (A.restrict (Metric.ball_subset_closedBall.trans hsub)) hu' hφ
      = bilinFormOfCoeff (A.restrict (Metric.ball_subset_closedBall.trans hsub))
          (huw.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)) hφ := by
            exact bilinFormOfCoeff_eq_left Metric.isOpen_ball
              (A.restrict (Metric.ball_subset_closedBall.trans hsub)) hu'
              (huw.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)) hφ
    _ = bilinFormOfCoeff A huw
          (ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ) := by
          exact bilinForm_ball_restrict_eq_zeroExtend (d := d) hΩ A hr hsub huw hφ0 hφ
    _ ≤ 0 := hbig

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSubsolution.restrict_ball then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSubsolution.restrict_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSubsolution.restrict_ball ``Submission.DeGiorgi.IsSubsolution.restrict_ball

theorem IsSupersolution.restrict_ball
    {Ω : Set E} (hΩ : IsOpen Ω)
    {c : E} {r : ℝ} (hr : 0 < r)
    {A : EllipticCoeff d Ω} {u : E → ℝ}
    (hsub : Metric.closedBall c r ⊆ Ω)
    (hu : IsSupersolution A u) :
    IsSupersolution (A.restrict (Metric.ball_subset_closedBall.trans hsub)) u := by
  rcases hu with ⟨hu_mem, hu_super⟩
  let huw : MemW1pWitness 2 u Ω := MemW1p.someWitness hu_mem
  refine ⟨(huw.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)).memW1p, ?_⟩
  intro hu' φ hφ0 hφ hφ_nonneg
  have hφ0_big :
      MemH01 ((Metric.ball c r).indicator φ) Ω :=
    memH01_indicator_ball_of_closedBall_subset (d := d) hΩ hr hsub hφ0
  let hφBig : MemW1pWitness 2 ((Metric.ball c r).indicator φ) Ω :=
    ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ
  have hbig :
      0 ≤ bilinFormOfCoeff A huw hφBig := by
    exact hu_super huw _ hφ0_big hφBig (by
      intro x
      by_cases hx : x ∈ Metric.ball c r
      · simpa [hx] using hφ_nonneg x
      · simp [hx])
  calc
    0 ≤ bilinFormOfCoeff A huw
          (ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ) := by
          exact hbig
    _ = bilinFormOfCoeff (A.restrict (Metric.ball_subset_closedBall.trans hsub))
          (huw.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)) hφ := by
          symm
          exact bilinForm_ball_restrict_eq_zeroExtend (d := d) hΩ A hr hsub huw hφ0 hφ
    _ = bilinFormOfCoeff (A.restrict (Metric.ball_subset_closedBall.trans hsub)) hu' hφ := by
          symm
          exact bilinFormOfCoeff_eq_left Metric.isOpen_ball
            (A.restrict (Metric.ball_subset_closedBall.trans hsub))
            hu' (huw.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)) hφ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSupersolution.restrict_ball then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSupersolution.restrict_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSupersolution.restrict_ball ``Submission.DeGiorgi.IsSupersolution.restrict_ball

theorem IsSolution.restrict_ball
    {Ω : Set E} (hΩ : IsOpen Ω)
    {c : E} {r : ℝ} (hr : 0 < r)
    {A : EllipticCoeff d Ω} {u : E → ℝ}
    (hsub : Metric.closedBall c r ⊆ Ω)
    (hu : IsSolution A u) :
    IsSolution (A.restrict (Metric.ball_subset_closedBall.trans hsub)) u := by
  exact ⟨hu.1.restrict_ball (d := d) hΩ hr hsub, hu.2.restrict_ball (d := d) hΩ hr hsub⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSolution.restrict_ball then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSolution.restrict_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSolution.restrict_ball ``Submission.DeGiorgi.IsSolution.restrict_ball

theorem IsSubsolution.sub_const_ball
    {c : E} {r : ℝ} (_hr : 0 < r)
    {A : EllipticCoeff d (Metric.ball c r)} {u : E → ℝ}
    (hsub : IsSubsolution A u) (k : ℝ) :
    IsSubsolution A (fun x => u x - k) := by
  let _ := _hr
  have : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (Metric.ball c r)) := by
    rw [MeasureTheory.isFiniteMeasure_iff]
    simpa using (_root_.MeasureTheory.measure_ball_lt_top (μ := _root_.MeasureTheory.MeasureSpace.volume) (x := c) (r := r))
  let hu : MemW1pWitness 2 u (Metric.ball c r) := MemW1p.someWitness hsub.1
  let huShift : MemW1pWitness 2 (fun x => u x - k) (Metric.ball c r) :=
    hu.subConst Metric.isOpen_ball k
  refine ⟨huShift.memW1p, ?_⟩
  intro hv φ hφ0 hφ hφ_nonneg
  let huBackRaw : MemW1pWitness 2 (fun x => (u x - k) - (-k)) (Metric.ball c r) :=
    hv.subConst Metric.isOpen_ball (-k)
  let huBack : MemW1pWitness 2 u (Metric.ball c r) :=
    MemW1pWitness.ofAeEq (Ω := Metric.ball c r)
      (Filter.Eventually.of_forall fun x => by ring) huBackRaw
  have hineq : bilinFormOfCoeff A huBack hφ ≤ 0 := hsub.2 huBack φ hφ0 hφ hφ_nonneg
  change bilinFormOfCoeff A hv hφ ≤ 0 at hineq
  exact hineq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSubsolution.sub_const_ball then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSubsolution.sub_const_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSubsolution.sub_const_ball ``Submission.DeGiorgi.IsSubsolution.sub_const_ball

theorem IsSupersolution.sub_const_ball
    {c : E} {r : ℝ} (_hr : 0 < r)
    {A : EllipticCoeff d (Metric.ball c r)} {u : E → ℝ}
    (hsuper : IsSupersolution A u) (k : ℝ) :
    IsSupersolution A (fun x => u x - k) := by
  let _ := _hr
  have : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (Metric.ball c r)) := by
    rw [MeasureTheory.isFiniteMeasure_iff]
    simpa using (_root_.MeasureTheory.measure_ball_lt_top (μ := _root_.MeasureTheory.MeasureSpace.volume) (x := c) (r := r))
  let hu : MemW1pWitness 2 u (Metric.ball c r) := MemW1p.someWitness hsuper.1
  let huShift : MemW1pWitness 2 (fun x => u x - k) (Metric.ball c r) :=
    hu.subConst Metric.isOpen_ball k
  refine ⟨huShift.memW1p, ?_⟩
  intro hv φ hφ0 hφ hφ_nonneg
  let huBackRaw : MemW1pWitness 2 (fun x => (u x - k) - (-k)) (Metric.ball c r) :=
    hv.subConst Metric.isOpen_ball (-k)
  let huBack : MemW1pWitness 2 u (Metric.ball c r) :=
    MemW1pWitness.ofAeEq (Ω := Metric.ball c r)
      (Filter.Eventually.of_forall fun x => by ring) huBackRaw
  have hineq : 0 ≤ bilinFormOfCoeff A huBack hφ := hsuper.2 huBack φ hφ0 hφ hφ_nonneg
  change 0 ≤ bilinFormOfCoeff A hv hφ at hineq
  exact hineq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSupersolution.sub_const_ball then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSupersolution.sub_const_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSupersolution.sub_const_ball ``Submission.DeGiorgi.IsSupersolution.sub_const_ball

theorem IsSolution.sub_const_ball
    {c : E} {r : ℝ} (hr : 0 < r)
    {A : EllipticCoeff d (Metric.ball c r)} {u : E → ℝ}
    (hsol : IsSolution A u) (k : ℝ) :
    IsSolution A (fun x => u x - k) := by
  exact ⟨hsol.1.sub_const_ball (d := d) hr k, hsol.2.sub_const_ball (d := d) hr k⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSolution.sub_const_ball then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSolution.sub_const_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSolution.sub_const_ball ``Submission.DeGiorgi.IsSolution.sub_const_ball

theorem IsSubsolution.neg_ball
    {c : E} {r : ℝ} (_hr : 0 < r)
    {A : EllipticCoeff d (Metric.ball c r)} {u : E → ℝ}
    (hsub : IsSubsolution A u) :
    IsSupersolution A (fun x => -u x) := by
  let _ := _hr
  let hu : MemW1pWitness 2 u (Metric.ball c r) := MemW1p.someWitness hsub.1
  let hneg : MemW1pWitness 2 (fun x => -u x) (Metric.ball c r) := by
    simpa using hu.smul (-1)
  refine ⟨hneg.memW1p, ?_⟩
  intro hv φ hφ0 hφ hφ_nonneg
  let huBackRaw : MemW1pWitness 2 (fun x => (-1 : ℝ) * (-u x)) (Metric.ball c r) := hv.smul (-1)
  let huBack : MemW1pWitness 2 u (Metric.ball c r) :=
    MemW1pWitness.ofAeEq (Ω := Metric.ball c r)
      (Filter.Eventually.of_forall fun x => by ring) huBackRaw
  have hineq : bilinFormOfCoeff A huBack hφ ≤ 0 := hsub.2 huBack φ hφ0 hφ hφ_nonneg
  have hsmul : bilinFormOfCoeff A huBack hφ = -bilinFormOfCoeff A hv hφ := by
    calc
      bilinFormOfCoeff A huBack hφ = bilinFormOfCoeff A (hv.smul (-1)) hφ := rfl
      _ = (-1 : ℝ) * bilinFormOfCoeff A hv hφ :=
        bilinFormOfCoeff_smul_left (-1) A hv hφ
      _ = -bilinFormOfCoeff A hv hφ := neg_one_mul _
  rw [hsmul] at hineq
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSubsolution.neg_ball then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSubsolution.neg_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSubsolution.neg_ball ``Submission.DeGiorgi.IsSubsolution.neg_ball

theorem IsSupersolution.neg_ball
    {c : E} {r : ℝ} (_hr : 0 < r)
    {A : EllipticCoeff d (Metric.ball c r)} {u : E → ℝ}
    (hsuper : IsSupersolution A u) :
    IsSubsolution A (fun x => -u x) := by
  let _ := _hr
  let hu : MemW1pWitness 2 u (Metric.ball c r) := MemW1p.someWitness hsuper.1
  let hneg : MemW1pWitness 2 (fun x => -u x) (Metric.ball c r) := by
    simpa using hu.smul (-1)
  refine ⟨hneg.memW1p, ?_⟩
  intro hv φ hφ0 hφ hφ_nonneg
  let huBackRaw : MemW1pWitness 2 (fun x => (-1 : ℝ) * (-u x)) (Metric.ball c r) := hv.smul (-1)
  let huBack : MemW1pWitness 2 u (Metric.ball c r) :=
    MemW1pWitness.ofAeEq (Ω := Metric.ball c r)
      (Filter.Eventually.of_forall fun x => by ring) huBackRaw
  have hineq : 0 ≤ bilinFormOfCoeff A huBack hφ := hsuper.2 huBack φ hφ0 hφ hφ_nonneg
  have hsmul : bilinFormOfCoeff A huBack hφ = -bilinFormOfCoeff A hv hφ := by
    calc
      bilinFormOfCoeff A huBack hφ = bilinFormOfCoeff A (hv.smul (-1)) hφ := rfl
      _ = (-1 : ℝ) * bilinFormOfCoeff A hv hφ :=
        bilinFormOfCoeff_smul_left (-1) A hv hφ
      _ = -bilinFormOfCoeff A hv hφ := neg_one_mul _
  rw [hsmul] at hineq
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSupersolution.neg_ball then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSupersolution.neg_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSupersolution.neg_ball ``Submission.DeGiorgi.IsSupersolution.neg_ball

theorem IsSolution.neg_ball
    {c : E} {r : ℝ} (hr : 0 < r)
    {A : EllipticCoeff d (Metric.ball c r)} {u : E → ℝ}
    (hsol : IsSolution A u) :
    IsSolution A (fun x => -u x) := by
  exact ⟨hsol.2.neg_ball (d := d) hr, hsol.1.neg_ball (d := d) hr⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSolution.neg_ball then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSolution.neg_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSolution.neg_ball ``Submission.DeGiorgi.IsSolution.neg_ball

end DeGiorgi
