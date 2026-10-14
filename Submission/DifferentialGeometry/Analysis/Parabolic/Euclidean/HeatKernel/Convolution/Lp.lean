import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Real
open scoped _root_.ENNReal _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section KernelOperator

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

def lpTranslate (y : V) (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) :=
  DomAddAct.mk (-y) +ᵥ u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpTranslate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.lpTranslate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpTranslate ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.lpTranslate

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem lpTranslate_cont (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    Continuous (fun y : V => lpTranslate y u) := by
  unfold lpTranslate
  fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpTranslate_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.lpTranslate_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpTranslate_cont ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.lpTranslate_cont

omit [NormedSpace ℝ F] [CompleteSpace F] [Fact (1 ≤ p)] [Fact (p ≠ ∞)] in
@[simp] theorem lpTranslate_norm (y : V) (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    ‖lpTranslate y u‖ = ‖u‖ := by
  simp [lpTranslate]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpTranslate_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.lpTranslate_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpTranslate_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.lpTranslate_norm

def lpKernel (η : V → ℝ) (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) :=
  ∫ y, η y • lpTranslate y u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel

omit [CompleteSpace F] in
theorem lpKernel_integrable {η : V → ℝ} (hη : _root_.MeasureTheory.Integrable η)
    (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    Integrable (fun y : V => η y • lpTranslate y u) := by
  refine (hη.norm.mul_const ‖u‖).mono' ?_ ?_
  · exact hη.aestronglyMeasurable.smul (lpTranslate_cont u).aestronglyMeasurable
  · filter_upwards with y
    rw [norm_smul, lpTranslate_norm, Real.norm_eq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel_integrable ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel_integrable

omit [CompleteSpace F] [Fact (p ≠ ∞)] in
theorem lpKernel_norm_le {η : V → ℝ} (hη : _root_.MeasureTheory.Integrable η)
    (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    ‖lpKernel η u‖ ≤ (∫ y, ‖η y‖) * ‖u‖ := by
  unfold lpKernel
  calc
    ‖∫ y, η y • lpTranslate y u‖
        ≤ ∫ y, ‖η y‖ * ‖u‖ :=
      _root_.MeasureTheory.norm_integral_le_of_norm_le (hη.norm.mul_const ‖u‖)
        (Filter.Eventually.of_forall fun y => by
          rw [norm_smul, lpTranslate_norm, Real.norm_eq_abs])
    _ = (∫ y, ‖η y‖) * ‖u‖ := by rw [_root_.MeasureTheory.integral_mul_const]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel_norm_le

omit [CompleteSpace F] [Fact (p ≠ ∞)] in
theorem lpKernel_contract {η : V → ℝ} (hη : _root_.MeasureTheory.Integrable η)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∫ y, η y = 1)
    (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    ‖lpKernel η u‖ ≤ ‖u‖ := by
  refine (lpKernel_norm_le hη u).trans_eq ?_
  have habs : (fun y : V => ‖η y‖) = η := by
    funext y
    simp [Real.norm_eq_abs, abs_of_nonneg (hη0 y)]
  rw [habs, hη1, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel_contract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel_contract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel_contract ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.lpKernel_contract

end KernelOperator

section OperatorKernel

variable {V F G : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

def liftLp : (F →L[ℝ] G) →L[ℝ]
    (_root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) →L[ℝ] _root_.MeasureTheory.Lp G p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :=
  LinearMap.mkContinuous
    { toFun := fun A => A.compLpL p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)
      map_add' := fun A B => ContinuousLinearMap.add_compLpL A B
      map_smul' := fun c A => ContinuousLinearMap.smul_compLpL c A }
    1
    (fun A => by
      simpa only [one_mul] using!
        (ContinuousLinearMap.norm_compLpL_le (p := p) (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) A))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.liftLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.liftLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.liftLp ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.liftLp

omit [CompleteSpace F] [CompleteSpace G] [Fact (p ≠ ∞)] in
@[simp] theorem liftLp_apply (A : F →L[ℝ] G) :
    liftLp (V := V) (p := p) A = A.compLpL p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.liftLp_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.liftLp_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.liftLp_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.liftLp_apply

omit [CompleteSpace F] [CompleteSpace G] [Fact (p ≠ ∞)] in
theorem liftLp_norm_le (A : F →L[ℝ] G) :
    ‖liftLp (V := V) (p := p) A‖ ≤ ‖A‖ := by
  simpa [liftLp_apply] using
    (ContinuousLinearMap.norm_compLpL_le (p := p) (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.liftLp_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.liftLp_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.liftLp_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.liftLp_norm_le

def lpOpIntegrand (K : V → F →L[ℝ] G)
    (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) (y : V) :
    Lp G p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) :=
  (liftLp (V := V) (p := p) (K y)) (lpTranslate y u)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpIntegrand ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpIntegrand

def lpOpKernel (K : V → F →L[ℝ] G)
    (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    Lp G p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) :=
  ∫ y, lpOpIntegrand K u y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpKernel

omit [CompleteSpace F] [CompleteSpace G] in
theorem lpOpIntegrand_aesm {K : V → F →L[ℝ] G} (hK : _root_.MeasureTheory.AEStronglyMeasurable K)
    (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    AEStronglyMeasurable (lpOpIntegrand K u) := by
  have hKl : _root_.MeasureTheory.AEStronglyMeasurable
      (fun y : V => liftLp (V := V) (p := p) (K y)) :=
    (liftLp (V := V) (p := p)).continuous.comp_aestronglyMeasurable hK
  have htr : _root_.MeasureTheory.AEStronglyMeasurable (fun y : V => lpTranslate y u) :=
    (lpTranslate_cont u).aestronglyMeasurable
  have h := (ContinuousLinearMap.apply ℝ (_root_.MeasureTheory.Lp G p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V))).aestronglyMeasurable_comp₂
    htr hKl
  simpa only [lpOpIntegrand, ContinuousLinearMap.apply_apply] using! h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpIntegrand_aesm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpIntegrand_aesm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpIntegrand_aesm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpIntegrand_aesm

omit [CompleteSpace F] [CompleteSpace G] [Fact (p ≠ ∞)] in
theorem lpOpIntegrand_norm (K : V → F →L[ℝ] G)
    (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) (y : V) :
    ‖lpOpIntegrand K u y‖ ≤ ‖K y‖ * ‖u‖ := by
  calc
    ‖lpOpIntegrand K u y‖
        ≤ ‖liftLp (V := V) (p := p) (K y)‖ * ‖lpTranslate y u‖ :=
      (liftLp (V := V) (p := p) (K y)).le_opNorm _
    _ ≤ ‖K y‖ * ‖u‖ := by
      rw [lpTranslate_norm]
      exact mul_le_mul_of_nonneg_right (liftLp_norm_le (V := V) (p := p) (K y))
        (norm_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpIntegrand_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpIntegrand_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpIntegrand_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpIntegrand_norm

omit [CompleteSpace F] [CompleteSpace G] in
theorem lpOpKernel_int {K : V → F →L[ℝ] G} (hK : _root_.MeasureTheory.Integrable K)
    (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    Integrable (lpOpIntegrand K u) := by
  refine (hK.norm.mul_const ‖u‖).mono' (lpOpIntegrand_aesm hK.aestronglyMeasurable u) ?_
  filter_upwards with y
  exact lpOpIntegrand_norm K u y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpKernel_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpKernel_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpKernel_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpKernel_int

omit [CompleteSpace F] [CompleteSpace G] [Fact (p ≠ ∞)] in
theorem lpOpKernel_norm {K : V → F →L[ℝ] G} (hK : _root_.MeasureTheory.Integrable K)
    (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    ‖lpOpKernel K u‖ ≤ (∫ y, ‖K y‖) * ‖u‖ := by
  unfold lpOpKernel
  calc
    ‖∫ y, lpOpIntegrand K u y‖
        ≤ ∫ y, ‖K y‖ * ‖u‖ :=
      _root_.MeasureTheory.norm_integral_le_of_norm_le (hK.norm.mul_const ‖u‖)
        (Filter.Eventually.of_forall fun y => lpOpIntegrand_norm K u y)
    _ = (∫ y, ‖K y‖) * ‖u‖ := by rw [_root_.MeasureTheory.integral_mul_const]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpKernel_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpKernel_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpKernel_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.lpOpKernel_norm

end OperatorKernel

section Gaussian

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

theorem gauss_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : V => Real.exp (-a * ‖x‖ ^ 2)) := by
  apply (_root_.MeasureTheory.integrable_fun_norm_addHaar (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)
    (f := fun r : ℝ => Real.exp (-a * r ^ 2))).2
  have h := integrableOn_rpow_mul_exp_neg_mul_sq ha
    (s := ((Module.finrank ℝ V - 1 : ℕ) : ℝ))
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
  simpa only [smul_eq_mul, Real.rpow_natCast] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.gauss_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.gauss_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.gauss_integrable ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.gauss_integrable

theorem gaussMoment_int (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : V => ‖x‖ ^ k * Real.exp (-a * ‖x‖ ^ 2)) := by
  apply (_root_.MeasureTheory.integrable_fun_norm_addHaar (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)
    (f := fun r : ℝ => r ^ k * Real.exp (-a * r ^ 2))).2
  have h := integrableOn_rpow_mul_exp_neg_mul_sq ha
    (s := ((Module.finrank ℝ V - 1 + k : ℕ) : ℝ))
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
  simpa only [smul_eq_mul, Real.rpow_natCast, pow_add, mul_assoc] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussMoment_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussMoment_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussMoment_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussMoment_int

def baseHeatMass (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    : ℝ :=
  (Real.pi / (4 : ℝ)⁻¹) ^ (Module.finrank ℝ V / 2 : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeatMass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeatMass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeatMass ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeatMass

def baseHeat (x : V) : ℝ :=
  (baseHeatMass V)⁻¹ * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseHeatMass_pos : 0 < baseHeatMass V := by
  unfold baseHeatMass
  exact Real.rpow_pos_of_pos (div_pos Real.pi_pos (by positivity)) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeatMass_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeatMass_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeatMass_pos ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeatMass_pos

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseHeat_nonneg (x : V) : 0 ≤ baseHeat x := by
  exact mul_nonneg (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)
    (Real.exp_pos _).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat_nonneg

theorem baseHeat_int : _root_.MeasureTheory.Integrable (baseHeat : V → ℝ) := by
  unfold baseHeat
  exact (gauss_integrable (V := V) (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat_int

omit [Nontrivial V] in
theorem integral_baseHeat : ∫ x : V, baseHeat x = 1 := by
  unfold baseHeat
  rw [_root_.MeasureTheory.integral_const_mul,
    GaussianFourier.integral_rexp_neg_mul_sq_norm
      (V := V) (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)]
  exact inv_mul_cancel₀ (baseHeatMass_pos (V := V)).ne'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_baseHeat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_baseHeat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_baseHeat ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_baseHeat

def heatScale (t : ℝ) : ℝ := Real.sqrt t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale

def heatKernel (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
    baseHeat ((heatScale t)⁻¹ • x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel

theorem heatScale_pos {t : ℝ} (ht : 0 < t) : 0 < heatScale t := by
  simpa [heatScale] using Real.sqrt_pos.2 ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale_pos ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale_pos

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatKernel_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatKernel t x := by
  unfold heatKernel
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
    (baseHeat_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel_nonneg

theorem heatKernel_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatKernel t : V → ℝ) := by
  unfold heatKernel
  exact (baseHeat_int (V := V)).comp_smul (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel_int

omit [Nontrivial V] in
theorem integral_heatKernel {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatKernel t x = 1 := by
  let r := heatScale t
  have hr : 0 < r := heatScale_pos ht
  unfold heatKernel
  rw [_root_.MeasureTheory.integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) baseHeat hr.le,
    integral_baseHeat]
  simp only [smul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ hr.ne')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatKernel

end Gaussian

section GaussianDeriv

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

def baseD1 (v x : V) : ℝ :=
  -(2 : ℝ)⁻¹ * ⟪x, v⟫ * baseHeat x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1 ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1

def baseD2 (v w x : V) : ℝ :=
  ((4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ -
      (2 : ℝ)⁻¹ * ⟪v, w⟫) * baseHeat x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2 ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD2_comm (v w x : V) :
    baseD2 v w x = baseD2 w v x := by
  unfold baseD2
  rw [real_inner_comm v w]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2_comm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2_comm

def baseD1Map (x : V) : V →L[ℝ] ℝ :=
  (-(2 : ℝ)⁻¹ * baseHeat x) • innerSL ℝ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Map ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Map

def baseD2Map (v x : V) : V →L[ℝ] ℝ :=
  ((4 : ℝ)⁻¹ * ⟪x, v⟫ * baseHeat x) • innerSL ℝ x -
    ((2 : ℝ)⁻¹ * baseHeat x) • innerSL ℝ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Map ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Map

def baseD2CurriedMap (x : V) : V →L[ℝ] (V →L[ℝ] ℝ) :=
  (innerSL ℝ x).smulRight
      (((4 : ℝ)⁻¹ * baseHeat x) • innerSL ℝ x) -
    ((2 : ℝ)⁻¹ * baseHeat x) •
      (innerSL ℝ (E := V)).toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2CurriedMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2CurriedMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2CurriedMap ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2CurriedMap

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
@[simp] theorem baseD1Map_apply (x v : V) :
    baseD1Map x v = baseD1 v x := by
  simp [baseD1Map, baseD1]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Map_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Map_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Map_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Map_apply

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
@[simp] theorem baseD2Map_apply (v x w : V) :
    baseD2Map v x w = baseD2 v w x := by
  simp [baseD2Map, baseD2]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Map_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Map_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Map_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Map_apply

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
@[simp] theorem baseD2CurriedMap_apply (x w v : V) :
    baseD2CurriedMap x w v = baseD2 v w x := by
  simp only [baseD2CurriedMap, baseD2, sub_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  have hinner :
      ((innerSL ℝ (E := V)).toContinuousLinearMap w) v = ⟪w, v⟫ := rfl
  rw [hinner, real_inner_comm w v]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2CurriedMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2CurriedMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2CurriedMap_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2CurriedMap_apply

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseHeat_hasFDeriv (x : V) :
    HasFDerivAt (baseHeat : V → ℝ) (baseD1Map x) x := by
  have hq := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-(4 : ℝ)⁻¹)
  have he := hq.exp
  have hc := he.const_mul (baseHeatMass V)⁻¹
  have hc' := hc.congr_fderiv (g' := baseD1Map x) (by
    ext v
    simp [baseD1Map, baseHeat]
    ring)
  simpa only [baseHeat] using! hc'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat_hasFDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat_hasFDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat_hasFDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseHeat_hasFDeriv

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD1_hasFDeriv (v x : V) :
    HasFDerivAt (baseD1 v) (baseD2Map v x) x := by
  have hi : HasFDerivAt (fun y : V => ⟪y, v⟫) (innerSL ℝ v) x := by
    simpa [real_inner_comm] using (innerSL ℝ v).hasFDerivAt
  have h := (hi.mul (baseHeat_hasFDeriv x)).const_mul (-(2 : ℝ)⁻¹)
  have h' := h.congr_fderiv (g' := baseD2Map v x) (by
    ext w
    simp only [baseD1Map, baseD2Map, sub_apply, add_apply, smul_apply,
      innerSL_apply_apply, smul_eq_mul]
    ring
    )
  have hfun : baseD1 v =
      fun y => -(2 : ℝ)⁻¹ * (⟪y, v⟫ * baseHeat y) := by
    funext y
    simp only [baseD1]
    ring
  rw [hfun]
  exact h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1_hasFDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1_hasFDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1_hasFDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1_hasFDeriv

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD1Map_hasFDeriv (x : V) :
    HasFDerivAt (baseD1Map (V := V)) (baseD2CurriedMap x) x := by
  have hc := (baseHeat_hasFDeriv (V := V) x).const_mul (-(2 : ℝ)⁻¹)
  have hi : HasFDerivAt
      (fun y : V => (innerSL ℝ (E := V)).toContinuousLinearMap y)
      (innerSL ℝ (E := V)).toContinuousLinearMap x :=
    (innerSL ℝ (E := V)).toContinuousLinearMap.hasFDerivAt
  have h := hc.smul hi
  have h' := h.congr_fderiv (g' := baseD2CurriedMap x) (by
    ext w v
    simp only [baseD2CurriedMap, sub_apply, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
    have hinner :
        ((innerSL ℝ (E := V)).toContinuousLinearMap w) v = ⟪w, v⟫ := rfl
    have hinnerX :
        ((innerSL ℝ (E := V)).toContinuousLinearMap x) v = ⟪x, v⟫ := rfl
    rw [hinner, hinnerX, baseD1Map_apply]
    unfold baseD1
    ring)
  simpa only [baseD1Map] using! h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Map_hasFDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Map_hasFDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Map_hasFDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Map_hasFDeriv

def baseD1Maj (x : V) : ℝ :=
  (2 : ℝ)⁻¹ * ‖x‖ * baseHeat x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Maj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Maj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Maj ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Maj

def baseD2Maj (x : V) : ℝ :=
  ((4 : ℝ)⁻¹ * ‖x‖ ^ 2 + (2 : ℝ)⁻¹) * baseHeat x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Maj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Maj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Maj ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Maj

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD1Maj_nonneg (x : V) : 0 ≤ baseD1Maj x := by
  unfold baseD1Maj
  exact mul_nonneg (mul_nonneg (by positivity) (norm_nonneg x)) (baseHeat_nonneg x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Maj_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Maj_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Maj_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Maj_nonneg

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD2Maj_nonneg (x : V) : 0 ≤ baseD2Maj x := by
  unfold baseD2Maj
  exact mul_nonneg (add_nonneg (mul_nonneg (by positivity) (sq_nonneg ‖x‖)) (by positivity))
    (baseHeat_nonneg x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Maj_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Maj_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Maj_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Maj_nonneg

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD1_bound (v x : V) :
    ‖baseD1 v x‖ ≤ ‖v‖ * baseD1Maj x := by
  rw [baseD1, baseD1Maj, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹),
    abs_of_nonneg (baseHeat_nonneg x)]
  calc
    (2 : ℝ)⁻¹ * |⟪x, v⟫| * baseHeat x
        ≤ (2 : ℝ)⁻¹ * (‖x‖ * ‖v‖) * baseHeat x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x v) (by positivity))
        (baseHeat_nonneg x)
    _ = ‖v‖ * ((2 : ℝ)⁻¹ * ‖x‖ * baseHeat x) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1_bound

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD2_bound (v w x : V) :
    ‖baseD2 v w x‖ ≤ ‖v‖ * ‖w‖ * baseD2Maj x := by
  rw [baseD2, baseD2Maj, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (baseHeat_nonneg x)]
  have htri :
      |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ - (2 : ℝ)⁻¹ * ⟪v, w⟫| ≤
        (4 : ℝ)⁻¹ * |⟪x, v⟫| * |⟪x, w⟫| +
          (2 : ℝ)⁻¹ * |⟪v, w⟫| := by
    calc
      |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ - (2 : ℝ)⁻¹ * ⟪v, w⟫|
          = |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ +
              -((2 : ℝ)⁻¹ * ⟪v, w⟫)| := by ring_nf
      _ ≤ |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫| +
            |-((2 : ℝ)⁻¹ * ⟪v, w⟫)| := abs_add_le _ _
      _ = (4 : ℝ)⁻¹ * |⟪x, v⟫| * |⟪x, w⟫| +
            (2 : ℝ)⁻¹ * |⟪v, w⟫| := by
        rw [abs_mul, abs_mul, abs_neg, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 : ℝ)⁻¹),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
  calc
    |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ - (2 : ℝ)⁻¹ * ⟪v, w⟫| * baseHeat x
        ≤ ((4 : ℝ)⁻¹ * |⟪x, v⟫| * |⟪x, w⟫| +
            (2 : ℝ)⁻¹ * |⟪v, w⟫|) * baseHeat x := by
          exact mul_le_mul_of_nonneg_right htri (baseHeat_nonneg x)
    _ ≤ ((4 : ℝ)⁻¹ * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) +
            (2 : ℝ)⁻¹ * (‖v‖ * ‖w‖)) * baseHeat x := by
          apply mul_le_mul_of_nonneg_right _ (baseHeat_nonneg x)
          apply add_le_add
          · have hp : |⟪x, v⟫| * |⟪x, w⟫| ≤
                (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) :=
              mul_le_mul (abs_real_inner_le_norm x v) (abs_real_inner_le_norm x w)
                (abs_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg v))
            calc
              (4 : ℝ)⁻¹ * |⟪x, v⟫| * |⟪x, w⟫|
                  = (4 : ℝ)⁻¹ * (|⟪x, v⟫| * |⟪x, w⟫|) := by ring
              _ ≤ (4 : ℝ)⁻¹ * ((‖x‖ * ‖v‖) * (‖x‖ * ‖w‖)) :=
                mul_le_mul_of_nonneg_left hp (by positivity)
              _ = (4 : ℝ)⁻¹ * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) := by ring
          · exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm v w) (by positivity)
    _ = ‖v‖ * ‖w‖ *
          (((4 : ℝ)⁻¹ * ‖x‖ ^ 2 + (2 : ℝ)⁻¹) * baseHeat x) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2_bound

theorem baseD1Maj_int : _root_.MeasureTheory.Integrable (baseD1Maj : V → ℝ) := by
  have h := (gaussMoment_int (V := V) 1
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have heq : baseD1Maj = fun x : V =>
      ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
        (‖x‖ ^ 1 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseD1Maj baseHeat
    ring
  rw [heq]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Maj_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Maj_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Maj_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD1Maj_int

theorem baseD2Maj_int : _root_.MeasureTheory.Integrable (baseD2Maj : V → ℝ) := by
  have h2 := (gaussMoment_int (V := V) 2
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((4 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have h0 := (gaussMoment_int (V := V) 0
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have heq : baseD2Maj = fun x : V =>
      ((4 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 2 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) +
        ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 0 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseD2Maj baseHeat
    ring
  rw [heq]
  exact h2.add h0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Maj_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Maj_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Maj_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Maj_int

def heatC1 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  ∫ x : V, baseD1Maj x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC1 ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC1

def heatC2 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  ∫ x : V, baseD2Maj x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2 ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2

omit [Nontrivial V] in
theorem heatC1_nonneg : 0 ≤ heatC1 V :=
  _root_.MeasureTheory.integral_nonneg baseD1Maj_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC1_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC1_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC1_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC1_nonneg

omit [Nontrivial V] in
theorem heatC2_nonneg : 0 ≤ heatC2 V :=
  _root_.MeasureTheory.integral_nonneg baseD2Maj_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2_nonneg

def heatD1Maj (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
    baseD1Maj ((heatScale t)⁻¹ • x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Maj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Maj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Maj ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Maj

def heatD2Maj (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ * (heatScale t)⁻¹ *
    baseD2Maj ((heatScale t)⁻¹ • x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Maj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Maj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Maj ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Maj

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD1Maj_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatD1Maj t x := by
  unfold heatD1Maj
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
      (inv_nonneg.mpr (heatScale_pos ht).le))
    (baseD1Maj_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Maj_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Maj_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Maj_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Maj_nonneg

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2Maj_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatD2Maj t x := by
  unfold heatD2Maj
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
        (inv_nonneg.mpr (heatScale_pos ht).le))
      (inv_nonneg.mpr (heatScale_pos ht).le))
    (baseD2Maj_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Maj_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Maj_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Maj_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Maj_nonneg

theorem heatD1Maj_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatD1Maj t : V → ℝ) := by
  unfold heatD1Maj
  exact (baseD1Maj_int (V := V)).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Maj_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Maj_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Maj_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Maj_int

theorem heatD2Maj_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatD2Maj t : V → ℝ) := by
  unfold heatD2Maj
  exact (baseD2Maj_int (V := V)).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Maj_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Maj_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Maj_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Maj_int

omit [Nontrivial V] in
theorem integral_heatD1Maj {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatD1Maj t x = (heatScale t)⁻¹ * heatC1 V := by
  have hr : 0 < heatScale t := heatScale_pos ht
  unfold heatD1Maj heatC1
  rw [_root_.MeasureTheory.integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) baseD1Maj hr.le]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatD1Maj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatD1Maj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatD1Maj ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatD1Maj

omit [Nontrivial V] in
theorem integral_heatD2Maj {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatD2Maj t x = t⁻¹ * heatC2 V := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hsqrt : heatScale t ^ 2 = t := by
    simpa [heatScale] using Real.sq_sqrt ht.le
  unfold heatD2Maj heatC2
  rw [_root_.MeasureTheory.integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) baseD2Maj hr.le]
  simp only [smul_eq_mul]
  have hscale : (heatScale t)⁻¹ * (heatScale t)⁻¹ = t⁻¹ := by
    field_simp [hr.ne', ht.ne']
    nlinarith [hsqrt]
  calc
    (heatScale t ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
          (heatScale t)⁻¹ *
          (heatScale t ^ Module.finrank ℝ V * ∫ x : V, baseD2Maj x)
        = ((heatScale t)⁻¹ * (heatScale t)⁻¹) *
            ∫ x : V, baseD2Maj x := by
          field_simp [hr.ne']
    _ = t⁻¹ * ∫ x : V, baseD2Maj x := by rw [hscale]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatD2Maj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatD2Maj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatD2Maj ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatD2Maj

def heatD1 (t : ℝ) (v x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
    baseD1 v ((heatScale t)⁻¹ • x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1 ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1

def heatD2 (t : ℝ) (v w x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ * (heatScale t)⁻¹ *
    baseD2 v w ((heatScale t)⁻¹ • x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2 ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2_comm (t : ℝ) (v w x : V) :
    heatD2 t v w x = heatD2 t w v x := by
  unfold heatD2
  rw [baseD2_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_comm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_comm

def heatD1Map (t : ℝ) (x : V) : V →L[ℝ] ℝ :=
  (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹) •
    baseD1Map ((heatScale t)⁻¹ • x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map

def heatD2Map (t : ℝ) (v x : V) : V →L[ℝ] ℝ :=
  (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
      (heatScale t)⁻¹) •
    baseD2Map v ((heatScale t)⁻¹ • x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Map ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Map

def heatD2CurriedMap (t : ℝ) (x : V) : V →L[ℝ] (V →L[ℝ] ℝ) :=
  (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
      (heatScale t)⁻¹) •
    baseD2CurriedMap ((heatScale t)⁻¹ • x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2CurriedMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2CurriedMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2CurriedMap ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2CurriedMap

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
@[simp] theorem heatD1Map_apply (t : ℝ) (x v : V) :
    heatD1Map t x v = heatD1 t v x := by
  simp [heatD1Map, heatD1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map_apply

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
@[simp] theorem heatD2Map_apply (t : ℝ) (v x w : V) :
    heatD2Map t v x w = heatD2 t v w x := by
  simp [heatD2Map, heatD2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Map_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Map_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Map_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Map_apply

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
@[simp] theorem heatD2CurriedMap_apply (t : ℝ) (x w v : V) :
    heatD2CurriedMap t x w v = heatD2 t v w x := by
  simp only [heatD2CurriedMap, smul_apply, smul_eq_mul,
    baseD2CurriedMap_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2CurriedMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2CurriedMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2CurriedMap_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2CurriedMap_apply

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatKernel_hasFDeriv {t : ℝ} (x : V) :
    HasFDerivAt (heatKernel t) (heatD1Map t x) x := by
  let S : V →L[ℝ] V := (heatScale t)⁻¹ • ContinuousLinearMap.id ℝ V
  have hS : HasFDerivAt (fun y : V => (heatScale t)⁻¹ • y) S x := by
    simpa [S] using! S.hasFDerivAt
  have h := ((baseHeat_hasFDeriv ((heatScale t)⁻¹ • x)).comp x hS).const_mul
    (((heatScale t) ^ Module.finrank ℝ V)⁻¹)
  have h' := h.congr_fderiv (g' := heatD1Map t x) (by
    ext v
    simp [heatD1Map, S, baseD1Map]
    ring)
  simpa only [heatKernel] using! h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel_hasFDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel_hasFDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel_hasFDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatKernel_hasFDeriv

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD1_hasFDeriv {t : ℝ} (v x : V) :
    HasFDerivAt (heatD1 t v) (heatD2Map t v x) x := by
  let S : V →L[ℝ] V := (heatScale t)⁻¹ • ContinuousLinearMap.id ℝ V
  have hS : HasFDerivAt (fun y : V => (heatScale t)⁻¹ • y) S x := by
    simpa [S] using! S.hasFDerivAt
  have h := ((baseD1_hasFDeriv v ((heatScale t)⁻¹ • x)).comp x hS).const_mul
    (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹)
  have h' := h.congr_fderiv (g' := heatD2Map t v x) (by
    ext w
    simp [heatD2Map, S, baseD2Map]
    ring)
  simpa only [heatD1] using! h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1_hasFDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1_hasFDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1_hasFDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1_hasFDeriv

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD1Map_hasFDeriv (t : ℝ) (x : V) :
    HasFDerivAt (heatD1Map (V := V) t) (heatD2CurriedMap t x) x := by
  let S : V →L[ℝ] V := (heatScale t)⁻¹ • ContinuousLinearMap.id ℝ V
  have hS : HasFDerivAt (fun y : V => (heatScale t)⁻¹ • y) S x := by
    simpa [S] using! S.hasFDerivAt
  have hb : HasFDerivAt (baseD1Map (V := V))
      (baseD2CurriedMap ((heatScale t)⁻¹ • x)) ((heatScale t)⁻¹ • x) :=
    baseD1Map_hasFDeriv _
  have h := (hb.comp x hS).const_smul
    (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹)
  have h' := h.congr_fderiv (g' := heatD2CurriedMap t x) (by
    ext w v
    simp only [heatD2CurriedMap, S, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_smul,
      smul_eq_mul]
    ring)
  simpa only [heatD1Map] using! h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map_hasFDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map_hasFDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map_hasFDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map_hasFDeriv

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD1_bound {t : ℝ} (ht : 0 < t) (v x : V) :
    ‖heatD1 t v x‖ ≤ ‖v‖ * heatD1Maj t x := by
  unfold heatD1 heatD1Maj
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _)),
    abs_of_nonneg (inv_nonneg.mpr (heatScale_pos ht).le)]
  calc
    ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
        ‖baseD1 v ((heatScale t)⁻¹ • x)‖
      ≤ ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
          (‖v‖ * baseD1Maj ((heatScale t)⁻¹ • x)) := by
        exact mul_le_mul_of_nonneg_left (baseD1_bound v _)
          (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
            (inv_nonneg.mpr (heatScale_pos ht).le))
    _ = ‖v‖ * (((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹ * baseD1Maj ((heatScale t)⁻¹ • x)) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1_bound

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2_bound {t : ℝ} (ht : 0 < t) (v w x : V) :
    ‖heatD2 t v w x‖ ≤ ‖v‖ * ‖w‖ * heatD2Maj t x := by
  unfold heatD2 heatD2Maj
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  simp only [abs_inv, abs_pow, abs_of_nonneg (heatScale_pos ht).le]
  calc
    ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ * (heatScale t)⁻¹ *
        ‖baseD2 v w ((heatScale t)⁻¹ • x)‖
      ≤ ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ * (heatScale t)⁻¹ *
          (‖v‖ * ‖w‖ * baseD2Maj ((heatScale t)⁻¹ • x)) := by
        exact mul_le_mul_of_nonneg_left (baseD2_bound v w _)
          (mul_nonneg
            (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
              (inv_nonneg.mpr (heatScale_pos ht).le))
            (inv_nonneg.mpr (heatScale_pos ht).le))
    _ = ‖v‖ * ‖w‖ * (((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹ * (heatScale t)⁻¹ *
          baseD2Maj ((heatScale t)⁻¹ • x)) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_bound

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD1Map_norm_le {t : Real} (ht : 0 < t) (x : V) :
    ‖heatD1Map t x‖ ≤ heatD1Maj t x := by
  apply ContinuousLinearMap.opNorm_le_bound (heatD1Map t x)
    (heatD1Maj_nonneg ht x)
  intro v
  rw [heatD1Map_apply]
  exact (heatD1_bound ht v x).trans_eq (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Map_norm_le

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2Map_norm_le {t : Real} (ht : 0 < t) (v x : V) :
    ‖heatD2Map t v x‖ ≤ ‖v‖ * heatD2Maj t x := by
  apply ContinuousLinearMap.opNorm_le_bound (heatD2Map t v x)
    (mul_nonneg (norm_nonneg v) (heatD2Maj_nonneg ht x))
  intro w
  rw [heatD2Map_apply]
  exact (heatD2_bound ht v w x).trans_eq (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Map_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Map_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Map_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Map_norm_le

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2CurriedMap_norm_le {t : Real} (ht : 0 < t) (x : V) :
    ‖heatD2CurriedMap t x‖ ≤ heatD2Maj t x := by
  apply ContinuousLinearMap.opNorm_le_bound (heatD2CurriedMap t x)
    (heatD2Maj_nonneg ht x)
  intro w
  apply ContinuousLinearMap.opNorm_le_bound (heatD2CurriedMap t x w)
    (mul_nonneg (heatD2Maj_nonneg ht x) (norm_nonneg w))
  intro v
  rw [heatD2CurriedMap_apply]
  exact (heatD2_bound ht v w x).trans_eq (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2CurriedMap_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2CurriedMap_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2CurriedMap_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2CurriedMap_norm_le

theorem heatD1_int {t : ℝ} (ht : 0 < t) (v : V) :
    Integrable (heatD1 t v : V → ℝ) := by
  refine ((heatD1Maj_int (V := V) ht).const_mul ‖v‖).mono'
    (by
      apply Continuous.aestronglyMeasurable
      unfold heatD1 baseD1 baseHeat baseHeatMass heatScale
      fun_prop) ?_
  filter_upwards with x
  exact heatD1_bound ht v x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1_int

theorem heatD2_int {t : ℝ} (ht : 0 < t) (v w : V) :
    Integrable (heatD2 t v w : V → ℝ) := by
  refine (((heatD2Maj_int (V := V) ht).const_mul ‖w‖).const_mul ‖v‖).mono'
    (by
      apply Continuous.aestronglyMeasurable
      unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
      fun_prop) ?_
  filter_upwards with x
  simpa [mul_assoc] using heatD2_bound ht v w x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_int

theorem integral_norm_D1 {t : ℝ} (ht : 0 < t) (v : V) :
    (∫ x : V, ‖heatD1 t v x‖) ≤
      ‖v‖ * (heatScale t)⁻¹ * heatC1 V := by
  calc
    (∫ x : V, ‖heatD1 t v x‖)
        ≤ ∫ x : V, ‖v‖ * heatD1Maj t x := by
      exact _root_.MeasureTheory.integral_mono (heatD1_int ht v).norm
        ((heatD1Maj_int (V := V) ht).const_mul ‖v‖)
        (fun x => heatD1_bound ht v x)
    _ = ‖v‖ * ((heatScale t)⁻¹ * heatC1 V) := by
      rw [_root_.MeasureTheory.integral_const_mul, integral_heatD1Maj ht]
    _ = ‖v‖ * (heatScale t)⁻¹ * heatC1 V := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_norm_D1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_norm_D1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_norm_D1 ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_norm_D1

theorem integral_norm_D2 {t : ℝ} (ht : 0 < t) (v w : V) :
    (∫ x : V, ‖heatD2 t v w x‖) ≤
      ‖v‖ * ‖w‖ * t⁻¹ * heatC2 V := by
  calc
    (∫ x : V, ‖heatD2 t v w x‖)
        ≤ ∫ x : V, (‖v‖ * ‖w‖) * heatD2Maj t x := by
      exact _root_.MeasureTheory.integral_mono (heatD2_int ht v w).norm
        ((heatD2Maj_int (V := V) ht).const_mul (‖v‖ * ‖w‖))
        (fun x => by simpa [mul_assoc] using heatD2_bound ht v w x)
    _ = (‖v‖ * ‖w‖) * (t⁻¹ * heatC2 V) := by
      rw [_root_.MeasureTheory.integral_const_mul, integral_heatD2Maj ht]
    _ = ‖v‖ * ‖w‖ * t⁻¹ * heatC2 V := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_norm_D2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_norm_D2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_norm_D2 ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_norm_D2

end GaussianDeriv

section HeatLp

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

def heatLp (t : ℝ) (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) :=
  lpKernel (heatKernel t) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatLp ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatLp

omit [CompleteSpace F] [Fact (p ≠ ∞)] in
theorem heatLp_contract {t : ℝ} (ht : 0 < t)
    (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    ‖heatLp t u‖ ≤ ‖u‖ := by
  exact lpKernel_contract (heatKernel_int ht) (heatKernel_nonneg ht)
    (integral_heatKernel ht) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatLp_contract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatLp_contract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatLp_contract ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatLp_contract

def heatD1Lp (t : ℝ) (v : V) (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) :=
  lpKernel (heatD1 t v) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Lp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Lp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Lp ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Lp

def heatD2Lp (t : ℝ) (v w : V) (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) :=
  lpKernel (heatD2 t v w) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Lp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Lp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Lp ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Lp

omit [CompleteSpace F] [Fact (p ≠ ∞)] in
theorem heatD1Lp_norm {t : ℝ} (ht : 0 < t) (v : V)
    (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    ‖heatD1Lp t v u‖ ≤
      (‖v‖ * (heatScale t)⁻¹ * heatC1 V) * ‖u‖ := by
  refine (lpKernel_norm_le (heatD1_int ht v) u).trans ?_
  exact mul_le_mul_of_nonneg_right (integral_norm_D1 ht v) (norm_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Lp_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Lp_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Lp_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Lp_norm

omit [CompleteSpace F] [Fact (p ≠ ∞)] in
theorem heatD2Lp_norm {t : ℝ} (ht : 0 < t) (v w : V)
    (u : _root_.MeasureTheory.Lp F p (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) :
    ‖heatD2Lp t v w u‖ ≤
      (‖v‖ * ‖w‖ * t⁻¹ * heatC2 V) * ‖u‖ := by
  refine (lpKernel_norm_le (heatD2_int ht v w) u).trans ?_
  exact mul_le_mul_of_nonneg_right (integral_norm_D2 ht v w) (norm_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Lp_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Lp_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Lp_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Lp_norm

end HeatLp

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry
