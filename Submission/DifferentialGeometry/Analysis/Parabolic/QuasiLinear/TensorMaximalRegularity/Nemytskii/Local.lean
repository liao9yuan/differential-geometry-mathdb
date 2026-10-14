import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.Forcing
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.LocallyLipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {T : ℝ}

def aeSetLift {S : Set X} (hzero : (0 : X) ∈ S) (f : timeL2 X T) : ℝ → S :=
  by
    classical
    exact fun t => if ht : f t ∈ S then ⟨f t, ht⟩ else ⟨0, hzero⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.aeSetLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.aeSetLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.aeSetLift ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.aeSetLift

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem aeSetLift_coe_ae {S : Set X} (hzero : (0 : X) ∈ S)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    (fun t => ((aeSetLift hzero f t : S) : X)) =ᵐ[timeMeasure T] fun t => f t := by
  filter_upwards [hf] with t ht
  simp only [aeSetLift, dif_pos ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.aeSetLift_coe_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.aeSetLift_coe_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.aeSetLift_coe_ae ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.aeSetLift_coe_ae

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem aeSetLift_aesm {S : Set X} (hzero : (0 : X) ∈ S)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    AEStronglyMeasurable (aeSetLift hzero f) (timeMeasure T) := by
  apply (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).mp
  exact (Lp.aestronglyMeasurable f).congr
    (aeSetLift_coe_ae hzero f hf).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.aeSetLift_aesm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.aeSetLift_aesm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.aeSetLift_aesm ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.aeSetLift_aesm

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem memLp_on {S : Set X} (hzero : (0 : X) ∈ S)
    {N : S → Y} {L : ℝ≥0} (hN : LipschitzWith L N)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    MemLp (fun t => N (aeSetLift hzero f t)) 2 (timeMeasure T) := by
  let z : S := ⟨0, hzero⟩
  have hlift := aeSetLift_aesm hzero f hf
  have hshiftMeas : _root_.MeasureTheory.AEStronglyMeasurable
      (fun t => N (aeSetLift hzero f t) - N z) (timeMeasure T) :=
    (hN.continuous.comp_aestronglyMeasurable hlift).sub
      _root_.MeasureTheory.aestronglyMeasurable_const
  have hshift : _root_.MeasureTheory.MemLp (fun t => N (aeSetLift hzero f t) - N z) 2
      (timeMeasure T) := by
    refine (Lp.memLp f).of_le_mul (c := (L : ℝ)) hshiftMeas ?_
    filter_upwards [hf] with t ht
    have hdist := hN.dist_le_mul (aeSetLift hzero f t) z
    rw [dist_eq_norm] at hdist
    simpa only [aeSetLift, dif_pos ht, z, Subtype.dist_eq, dist_zero_right] using hdist
  have hconst : _root_.MeasureTheory.MemLp (fun _ : ℝ => N z) 2 (timeMeasure T) :=
    _root_.MeasureTheory.memLp_const (N z)
  have hsum := hshift.add hconst
  have hfun : (fun t => N (aeSetLift hzero f t)) =
      fun t => (N (aeSetLift hzero f t) - N z) + N z := by
    funext t
    abel
  rw [hfun]
  exact hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_on ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_on

def nemytskiiOn {S : Set X} (hzero : (0 : X) ∈ S)
    {N : S → Y} {L : ℝ≥0} (hN : LipschitzWith L N)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    timeL2 Y T :=
  (memLp_on hzero hN f hf).toLp (fun t => N (aeSetLift hzero f t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiOn ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiOn

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem nemytskiiOn_coeFn {S : Set X} (hzero : (0 : X) ∈ S)
    {N : S → Y} {L : ℝ≥0} (hN : LipschitzWith L N)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    nemytskiiOn hzero hN f hf =ᵐ[timeMeasure T]
      fun t => N (aeSetLift hzero f t) :=
  (memLp_on hzero hN f hf).coeFn_toLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiOn_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiOn_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiOn_coeFn ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiOn_coeFn

omit [NormedSpace ℝ X] [CompleteSpace X] in
omit [NormedSpace ℝ Y] [CompleteSpace Y] in
theorem nemytskiiOn_zero_le {S : Set X} (hzero : (0 : X) ∈ S)
    {N : S → Y} {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ}
    (hf : ∀ᵐ t ∂(timeMeasure T), ((0 : timeL2 X T) t) ∈ S) :
    ‖nemytskiiOn hzero hN (0 : timeL2 X T) hf‖ ≤
      Real.sqrt T * ‖N ⟨0, hzero⟩‖ := by
  refine timeL2_norm_le_of_ae_bound _ (norm_nonneg _) ?_
  have hcoe := nemytskiiOn_coeFn hzero hN (0 : timeL2 X T) hf
  have hzeroFn := Lp.coeFn_zero (E := X) (p := 2) (μ := timeMeasure T)
  filter_upwards [hcoe, hzeroFn, hf] with t ht htz hmem
  rw [ht]
  simp only [aeSetLift, dif_pos hmem]
  have hval : ((0 : timeL2 X T) t) = (0 : X) := by
    simpa only [Pi.zero_apply] using htz
  have hsub : (⟨(0 : timeL2 X T) t, hmem⟩ : S) = ⟨0, hzero⟩ :=
    Subtype.ext hval
  rw [hsub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiOn_zero_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiOn_zero_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiOn_zero_le ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiOn_zero_le

omit [NormedSpace ℝ X] [CompleteSpace X] [NormedSpace ℝ Y] [CompleteSpace Y] in
theorem timeL2_norm_le_four
    {Z W V : Type*}
    [NormedAddCommGroup Z]
    [NormedAddCommGroup W]
    [NormedAddCommGroup V]
    (h : timeL2 X T) (p : timeL2 Y T) (q : timeL2 Z T)
    (r : timeL2 W T) (s : timeL2 V T) {A B C D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbound : ∀ᵐ t ∂(timeMeasure T),
      ‖h t‖ ≤ A * ‖p t‖ + B * ‖q t‖ + C * ‖r t‖ + D * ‖s t‖) :
    ‖h‖ ≤ A * ‖p‖ + B * ‖q‖ + C * ‖r‖ + D * ‖s‖ := by
  let Pf : ℝ → ℝ := fun t => ‖(p : ℝ → Y) t‖
  let Qf : ℝ → ℝ := fun t => ‖(q : ℝ → Z) t‖
  let Rf : ℝ → ℝ := fun t => ‖(r : ℝ → W) t‖
  let Sf : ℝ → ℝ := fun t => ‖(s : ℝ → V) t‖
  have hPm : _root_.MeasureTheory.AEStronglyMeasurable Pf (timeMeasure T) := (Lp.aestronglyMeasurable p).norm
  have hQm : _root_.MeasureTheory.AEStronglyMeasurable Qf (timeMeasure T) := (Lp.aestronglyMeasurable q).norm
  have hRm : _root_.MeasureTheory.AEStronglyMeasurable Rf (timeMeasure T) := (Lp.aestronglyMeasurable r).norm
  have hSm : _root_.MeasureTheory.AEStronglyMeasurable Sf (timeMeasure T) := (Lp.aestronglyMeasurable s).norm
  have hAPm : _root_.MeasureTheory.AEStronglyMeasurable (A • Pf) (timeMeasure T) := hPm.const_smul A
  have hBQm : _root_.MeasureTheory.AEStronglyMeasurable (B • Qf) (timeMeasure T) := hQm.const_smul B
  have hCRm : _root_.MeasureTheory.AEStronglyMeasurable (C • Rf) (timeMeasure T) := hRm.const_smul C
  have hDSm : _root_.MeasureTheory.AEStronglyMeasurable (D • Sf) (timeMeasure T) := hSm.const_smul D
  let major : ℝ → ℝ := A • Pf + B • Qf + C • Rf + D • Sf
  have hmono : _root_.MeasureTheory.eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      eLpNorm major 2 (timeMeasure T) := by
    refine _root_.MeasureTheory.eLpNorm_mono_ae ?_
    filter_upwards [hbound] with t ht
    have happ : major t =
        A * ‖p t‖ + B * ‖q t‖ + C * ‖r t‖ + D * ‖s t‖ := by
      simp only [major, Pf, Qf, Rf, Sf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hnonneg : 0 ≤ major t := by
      rw [happ]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, happ]
    exact ht
  have htri₁ : _root_.MeasureTheory.eLpNorm major 2 (timeMeasure T) ≤
      _root_.MeasureTheory.eLpNorm (A • Pf + B • Qf + C • Rf) 2 (timeMeasure T) +
        eLpNorm (D • Sf) 2 (timeMeasure T) := by
    exact _root_.MeasureTheory.eLpNorm_add_le ((hAPm.add hBQm).add hCRm) hDSm (by norm_num)
  have htri₂ : _root_.MeasureTheory.eLpNorm (A • Pf + B • Qf + C • Rf) 2 (timeMeasure T) ≤
      _root_.MeasureTheory.eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) +
        eLpNorm (C • Rf) 2 (timeMeasure T) := by
    exact _root_.MeasureTheory.eLpNorm_add_le (hAPm.add hBQm) hCRm (by norm_num)
  have htri₃ : _root_.MeasureTheory.eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) ≤
      _root_.MeasureTheory.eLpNorm (A • Pf) 2 (timeMeasure T) +
        eLpNorm (B • Qf) 2 (timeMeasure T) :=
    _root_.MeasureTheory.eLpNorm_add_le hAPm hBQm (by norm_num)
  have hscaleP : _root_.MeasureTheory.eLpNorm (A • Pf) 2 (timeMeasure T) =
      ENNReal.ofReal A * _root_.MeasureTheory.eLpNorm (p : ℝ → Y) 2 (timeMeasure T) := by
    rw [_root_.MeasureTheory.eLpNorm_const_smul, _root_.MeasureTheory.eLpNorm_norm, Real.enorm_eq_ofReal hA]
  have hscaleQ : _root_.MeasureTheory.eLpNorm (B • Qf) 2 (timeMeasure T) =
      ENNReal.ofReal B * _root_.MeasureTheory.eLpNorm (q : ℝ → Z) 2 (timeMeasure T) := by
    rw [_root_.MeasureTheory.eLpNorm_const_smul, _root_.MeasureTheory.eLpNorm_norm, Real.enorm_eq_ofReal hB]
  have hscaleR : _root_.MeasureTheory.eLpNorm (C • Rf) 2 (timeMeasure T) =
      ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm (r : ℝ → W) 2 (timeMeasure T) := by
    rw [_root_.MeasureTheory.eLpNorm_const_smul, _root_.MeasureTheory.eLpNorm_norm, Real.enorm_eq_ofReal hC]
  have hscaleS : _root_.MeasureTheory.eLpNorm (D • Sf) 2 (timeMeasure T) =
      ENNReal.ofReal D * _root_.MeasureTheory.eLpNorm (s : ℝ → V) 2 (timeMeasure T) := by
    rw [_root_.MeasureTheory.eLpNorm_const_smul, _root_.MeasureTheory.eLpNorm_norm, Real.enorm_eq_ofReal hD]
  have hfinal : _root_.MeasureTheory.eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      ENNReal.ofReal A * _root_.MeasureTheory.eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
        ENNReal.ofReal B * _root_.MeasureTheory.eLpNorm (q : ℝ → Z) 2 (timeMeasure T) +
        ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm (r : ℝ → W) 2 (timeMeasure T) +
        ENNReal.ofReal D * _root_.MeasureTheory.eLpNorm (s : ℝ → V) 2 (timeMeasure T) := by
    calc
      eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤ _root_.MeasureTheory.eLpNorm major 2 (timeMeasure T) := hmono
      _ ≤ _root_.MeasureTheory.eLpNorm (A • Pf + B • Qf + C • Rf) 2 (timeMeasure T) +
          eLpNorm (D • Sf) 2 (timeMeasure T) := htri₁
      _ ≤ (_root_.MeasureTheory.eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) +
            _root_.MeasureTheory.eLpNorm (C • Rf) 2 (timeMeasure T)) +
          eLpNorm (D • Sf) 2 (timeMeasure T) :=
        add_le_add htri₂ le_rfl
      _ ≤ ((_root_.MeasureTheory.eLpNorm (A • Pf) 2 (timeMeasure T) +
              _root_.MeasureTheory.eLpNorm (B • Qf) 2 (timeMeasure T)) +
            _root_.MeasureTheory.eLpNorm (C • Rf) 2 (timeMeasure T)) +
          eLpNorm (D • Sf) 2 (timeMeasure T) :=
        add_le_add (add_le_add htri₃ le_rfl) le_rfl
      _ = _ := by rw [hscaleP, hscaleQ, hscaleR, hscaleS]
  have hp_top : _root_.MeasureTheory.eLpNorm (p : ℝ → Y) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp p).2.ne
  have hq_top : _root_.MeasureTheory.eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp q).2.ne
  have hr_top : _root_.MeasureTheory.eLpNorm (r : ℝ → W) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp r).2.ne
  have hs_top : _root_.MeasureTheory.eLpNorm (s : ℝ → V) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp s).2.ne
  have hp_mul : ENNReal.ofReal A * _root_.MeasureTheory.eLpNorm (p : ℝ → Y) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top
  have hq_mul : ENNReal.ofReal B * _root_.MeasureTheory.eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq_top
  have hr_mul : ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm (r : ℝ → W) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hr_top
  have hs_mul : ENNReal.ofReal D * _root_.MeasureTheory.eLpNorm (s : ℝ → V) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs_top
  have hrhs_ne :
      ENNReal.ofReal A * _root_.MeasureTheory.eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
        ENNReal.ofReal B * _root_.MeasureTheory.eLpNorm (q : ℝ → Z) 2 (timeMeasure T) +
        ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm (r : ℝ → W) 2 (timeMeasure T) +
        ENNReal.ofReal D * _root_.MeasureTheory.eLpNorm (s : ℝ → V) 2 (timeMeasure T) ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hp_mul, hq_mul⟩, hr_mul⟩, hs_mul⟩
  change (_root_.MeasureTheory.eLpNorm (h : ℝ → X) 2 (timeMeasure T)).toReal ≤
    A * (_root_.MeasureTheory.eLpNorm (p : ℝ → Y) 2 (timeMeasure T)).toReal +
      B * (_root_.MeasureTheory.eLpNorm (q : ℝ → Z) 2 (timeMeasure T)).toReal +
      C * (_root_.MeasureTheory.eLpNorm (r : ℝ → W) 2 (timeMeasure T)).toReal +
      D * (_root_.MeasureTheory.eLpNorm (s : ℝ → V) 2 (timeMeasure T)).toReal
  refine le_trans (ENNReal.toReal_mono hrhs_ne hfinal) ?_
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨hp_mul, hq_mul⟩, hr_mul⟩) hs_mul,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hp_mul, hq_mul⟩) hr_mul,
    ENNReal.toReal_add hp_mul hq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hB,
    ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal hD]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeL2_norm_le_four then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeL2_norm_le_four"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeL2_norm_le_four ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeL2_norm_le_four

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
omit [CompleteSpace X] in
theorem memLp_tame {S : Set X} (hzero : (0 : X) ∈ S) {R : ℝ} (hR : 0 ≤ R)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (N : S → Y) (hN : Continuous N) (A B C : ℝ≥0)
    (htame : ∀ u v : S,
      ‖N u - N v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    MemLp (fun t => N (aeSetLift hzero f t)) 2 (timeMeasure T) := by
  let z : S := ⟨0, hzero⟩
  let K : ℝ := (A : ℝ) * R + (C : ℝ) * R
  let Q : ℝ := (B : ℝ) * R + ‖N z‖
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hlift := aeSetLift_aesm hzero f hf
  have hmeas : _root_.MeasureTheory.AEStronglyMeasurable
      (fun t => N (aeSetLift hzero f t)) (timeMeasure T) :=
    hN.comp_aestronglyMeasurable hlift
  let major : ℝ → ℝ := fun t => K * ‖f t‖ + Q
  have hmajor : _root_.MeasureTheory.MemLp major 2 (timeMeasure T) := by
    have hnorm : _root_.MeasureTheory.MemLp (fun t => ‖f t‖) 2 (timeMeasure T) := (Lp.memLp f).norm
    have hscaled : _root_.MeasureTheory.MemLp (K • fun t => ‖f t‖) 2 (timeMeasure T) := hnorm.const_smul K
    have hconst : _root_.MeasureTheory.MemLp (fun _ : ℝ => Q) 2 (timeMeasure T) := _root_.MeasureTheory.memLp_const Q
    have hadd := hscaled.add hconst
    apply (_root_.MeasureTheory.memLp_congr_ae ?_).1 hadd
    filter_upwards with t
    rfl
  refine hmajor.of_le hmeas ?_
  filter_upwards [hf] with t ht
  let u : S := ⟨f t, ht⟩
  have huJ : ‖J (f t)‖ ≤ R := by
    simpa only [u] using hstate u
  have hdiff : ‖N u - N z‖ ≤ K * ‖f t‖ + (B : ℝ) * R := by
    have hraw := htame u z
    have hraw' : ‖N u - N z‖ ≤
        (A : ℝ) * R * ‖f t‖ + (B : ℝ) * ‖J (f t)‖ +
          (C : ℝ) * ‖f t‖ * ‖J (f t)‖ := by
      simpa only [u, z, Subtype.coe_mk, sub_zero, map_zero, norm_zero, add_zero] using hraw
    calc
      ‖N u - N z‖ ≤
          (A : ℝ) * R * ‖f t‖ + (B : ℝ) * ‖J (f t)‖ +
            (C : ℝ) * ‖f t‖ * ‖J (f t)‖ := hraw'
      _ ≤ (A : ℝ) * R * ‖f t‖ + (B : ℝ) * R +
            (C : ℝ) * ‖f t‖ * R := by
        gcongr
      _ = K * ‖f t‖ + (B : ℝ) * R := by
        dsimp only [K]
        ring
  have hn : ‖N u‖ ≤ major t := by
    calc
      ‖N u‖ = ‖(N u - N z) + N z‖ := by rw [sub_add_cancel]
      _ ≤ ‖N u - N z‖ + ‖N z‖ := norm_add_le _ _
      _ ≤ (K * ‖f t‖ + (B : ℝ) * R) + ‖N z‖ :=
        add_le_add hdiff le_rfl
      _ = major t := by
        dsimp only [major, Q]
        ring
  have hmajor0 : 0 ≤ major t := by
    dsimp only [major]
    exact add_nonneg (mul_nonneg hK (norm_nonneg _)) hQ
  change ‖N (aeSetLift hzero f t)‖ ≤ ‖major t‖
  have hu : aeSetLift hzero f t = u := by
    simp only [aeSetLift, dif_pos ht, u]
  rw [hu, Real.norm_eq_abs, abs_of_nonneg hmajor0]
  exact hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_tame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_tame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_tame ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_tame

def nemytskiiTameOn {S : Set X} (hzero : (0 : X) ∈ S) {R : ℝ} (hR : 0 ≤ R)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    {N : S → Y} (hN : Continuous N) {A B C : ℝ≥0}
    (htame : ∀ u v : S,
      ‖N u - N v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    timeL2 Y T :=
  (memLp_tame hzero hR J hstate N hN A B C htame f hf).toLp
    (fun t => N (aeSetLift hzero f t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiTameOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiTameOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiTameOn ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiTameOn

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
omit [CompleteSpace X] in
theorem nemytskiiTameOn_coeFn {S : Set X} (hzero : (0 : X) ∈ S) {R : ℝ}
    (hR : 0 ≤ R) {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    {N : S → Y} (hN : Continuous N) {A B C : ℝ≥0}
    (htame : ∀ u v : S,
      ‖N u - N v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    nemytskiiTameOn hzero hR J hstate hN htame f hf =ᵐ[timeMeasure T]
      fun t => N (aeSetLift hzero f t) :=
  (memLp_tame hzero hR J hstate N hN A B C htame f hf).coeFn_toLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiTameOn_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiTameOn_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiTameOn_coeFn ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiTameOn_coeFn

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end

section
noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

theorem ae_residual_lift_of_ball_imp
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y]
    [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T r outer : ℝ} (K : X →L[ℝ] Z)
    (hzero : (0 : X) ∈ {v | ‖K v‖ ≤ r}) (N : ℝ → {v : X | ‖K v‖ ≤ r} → Y)
    (field : timeL2 X T) (force : timeL2 Y T) (W : ℝ → X) (f₀ : X)
    (F : ℝ → X → Y) (hrOuter : r ≤ outer)
    (hfield : field =ᵐ[timeMeasure T] (fun t => W t - f₀))
    (hstate : ∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖K v‖ ≤ r})
    (hforce : ∀ᵐ t ∂(timeMeasure T), ‖K (W t - f₀)‖ ≤ outer → force t = F t (W t))
    (hN : ∀ t (hW : ‖K (W t - f₀)‖ ≤ r), F t (W t) = N t ⟨W t - f₀, hW⟩) :
    force =ᵐ[timeMeasure T] (fun t => N t (aeSetLift hzero field t)) := by
  filter_upwards [hforce, hfield, hstate, aeSetLift_coe_ae hzero field hstate] with
    t hf hfieldt hstatet hlift
  have hW : ‖K (W t - f₀)‖ ≤ r := by
    rw [← hfieldt]
    exact hstatet
  have houter : ‖K (W t - f₀)‖ ≤ outer := hW.trans hrOuter
  have hNval := hN t hW
  have heqLift : aeSetLift hzero field t = ⟨W t - f₀, hW⟩ := by
    apply Subtype.ext
    exact hlift.trans hfieldt
  rw [hf houter, hNval, heqLift]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.ae_residual_lift_of_ball_imp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.ae_residual_lift_of_ball_imp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.ae_residual_lift_of_ball_imp ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.ae_residual_lift_of_ball_imp

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end
end
