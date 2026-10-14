import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Duhamel.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Real _root_.Set
open scoped _root_.ENNReal _root_.NNReal _root_.RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

def baseD2Holder (alpha : NNReal) (x : V) : Real :=
  ‖x‖ ^ (alpha : Real) * baseD2Maj x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD2Holder_nonneg (alpha : NNReal) (x : V) :
    0 ≤ baseD2Holder alpha x :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg x) _) (baseD2Maj_nonneg x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder_nonneg

theorem baseD2Holder_int {alpha : NNReal} (halpha : alpha ≤ 1) :
    Integrable (baseD2Holder alpha : V → Real) := by
  have hmajor : _root_.MeasureTheory.Integrable (fun x : V => (1 + ‖x‖) * baseD2Maj x) := by
    have hfirst : _root_.MeasureTheory.Integrable (fun x : V => ‖x‖ * baseD2Maj x) := by
      have h3 := (gaussMoment_int (V := V) 3
        (by positivity : (0 : Real) < (4 : Real)⁻¹)).const_mul
          ((4 : Real)⁻¹ * (baseHeatMass V)⁻¹)
      have h1 := (gaussMoment_int (V := V) 1
        (by positivity : (0 : Real) < (4 : Real)⁻¹)).const_mul
          ((2 : Real)⁻¹ * (baseHeatMass V)⁻¹)
      have heq : (fun x : V => ‖x‖ * baseD2Maj x) = fun x : V =>
          ((4 : Real)⁻¹ * (baseHeatMass V)⁻¹) *
              (‖x‖ ^ 3 * Real.exp (-(4 : Real)⁻¹ * ‖x‖ ^ 2)) +
            ((2 : Real)⁻¹ * (baseHeatMass V)⁻¹) *
              (‖x‖ ^ 1 * Real.exp (-(4 : Real)⁻¹ * ‖x‖ ^ 2)) := by
        funext x
        unfold baseD2Maj baseHeat
        ring
      rw [heq]
      exact h3.add h1
    have h := (baseD2Maj_int (V := V)).add hfirst
    have heq : (fun x : V => (1 + ‖x‖) * baseD2Maj x) =
        fun x : V => baseD2Maj x + ‖x‖ * baseD2Maj x := by
      funext x
      ring
    rw [heq]
    exact h
  refine hmajor.mono' ?_ ?_
  · have hpow : Continuous (fun x : V => ‖x‖ ^ (alpha : Real)) :=
      continuous_norm.rpow_const (fun _ => Or.inr alpha.coe_nonneg)
    have hmaj : Continuous (baseD2Maj : V → Real) := by
      unfold baseD2Maj baseHeat baseHeatMass
      fun_prop
    exact (hpow.mul hmaj).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (baseD2Holder_nonneg alpha x)]
  have hrpow : ‖x‖ ^ (alpha : Real) ≤ 1 + ‖x‖ := by
    by_cases hx : ‖x‖ ≤ 1
    · exact (Real.rpow_le_one (norm_nonneg x) hx alpha.coe_nonneg).trans
        (le_add_of_nonneg_right (norm_nonneg x))
    · have hx' : 1 ≤ ‖x‖ := le_of_not_ge hx
      exact (Real.rpow_le_self_of_one_le hx' (by exact_mod_cast halpha)).trans
        (le_add_of_nonneg_left zero_le_one)
  exact mul_le_mul_of_nonneg_right hrpow (baseD2Maj_nonneg x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder_int

def heatC2Holder (alpha : NNReal) : Real :=
  ∫ x : V, baseD2Holder alpha x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2Holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2Holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2Holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2Holder

omit [Nontrivial V] in
theorem heatC2Holder_nonneg (alpha : NNReal) : 0 ≤ heatC2Holder (V := V) alpha :=
  _root_.MeasureTheory.integral_nonneg (baseD2Holder_nonneg alpha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2Holder_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2Holder_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2Holder_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2Holder_nonneg

def heatD2Holder (alpha : NNReal) (t : Real) (x : V) : Real :=
  ((heatScale t) ^ Module.finrank Real V)⁻¹ * t⁻¹ *
    (heatScale t) ^ (alpha : Real) *
      baseD2Holder alpha ((heatScale t)⁻¹ • x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2Holder_nonneg (alpha : NNReal) {t : Real} (ht : 0 < t) (x : V) :
    0 ≤ heatD2Holder alpha t x := by
  unfold heatD2Holder
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
        (inv_nonneg.mpr ht.le))
      (Real.rpow_nonneg (heatScale_pos ht).le _))
    (baseD2Holder_nonneg alpha _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_nonneg

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem heatD2Holder_eq (alpha : NNReal) {t : Real} (ht : 0 < t) (x : V) :
    heatD2Holder alpha t x = ‖x‖ ^ (alpha : Real) * heatD2Maj t x := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hx : x = heatScale t • ((heatScale t)⁻¹ • x) := by
    simp [hr.ne']
  have hrpow : ‖x‖ ^ (alpha : Real) =
      (heatScale t) ^ (alpha : Real) *
        ‖(heatScale t)⁻¹ • x‖ ^ (alpha : Real) := by
    calc
      ‖x‖ ^ (alpha : Real) =
          ‖heatScale t • ((heatScale t)⁻¹ • x)‖ ^ (alpha : Real) :=
        congrArg (fun z : V => ‖z‖ ^ (alpha : Real)) hx
      _ = (heatScale t * ‖(heatScale t)⁻¹ • x‖) ^ (alpha : Real) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ = (heatScale t) ^ (alpha : Real) *
          ‖(heatScale t)⁻¹ • x‖ ^ (alpha : Real) :=
        Real.mul_rpow hr.le (norm_nonneg _)
  have hsquare : heatScale t ^ 2 = t := by
    simpa [heatScale] using Real.sq_sqrt ht.le
  have hscale : t⁻¹ = (heatScale t)⁻¹ * (heatScale t)⁻¹ := by
    field_simp [hr.ne', ht.ne']
    nlinarith [hsquare]
  unfold heatD2Holder heatD2Maj baseD2Holder
  rw [hrpow, hscale]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_eq

theorem heatD2Holder_int {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) :
    Integrable (heatD2Holder (V := V) alpha t) := by
  unfold heatD2Holder
  exact (baseD2Holder_int (V := V) halpha).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_int

omit [Nontrivial V] in
theorem integral_heatD2Holder (alpha : NNReal) {t : Real} (ht : 0 < t) :
    ∫ x : V, heatD2Holder alpha t x =
      t⁻¹ * (heatScale t) ^ (alpha : Real) * heatC2Holder (V := V) alpha := by
  have hr : 0 < heatScale t := heatScale_pos ht
  unfold heatD2Holder heatC2Holder
  rw [_root_.MeasureTheory.integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V) (baseD2Holder alpha) hr.le]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatD2Holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatD2Holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatD2Holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_heatD2Holder

def holderHeatScale (alpha : NNReal) (t : Real) : Real :=
  t ^ ((alpha : Real) / 2 - 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem holderHeatScale_eq (alpha : NNReal) {t : Real} (ht : 0 < t) :
    t⁻¹ * (heatScale t) ^ (alpha : Real) = holderHeatScale alpha t := by
  unfold holderHeatScale heatScale
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one,
    ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  congr 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale_eq

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2_holder_bound (alpha : NNReal) {t : Real} (ht : 0 < t)
    (v w x : V) :
    ‖heatD2 t v w x‖ * ‖x‖ ^ (alpha : Real) ≤
      ‖v‖ * ‖w‖ * heatD2Holder alpha t x := by
  rw [heatD2Holder_eq alpha ht]
  calc
    ‖heatD2 t v w x‖ * ‖x‖ ^ (alpha : Real) ≤
        (‖v‖ * ‖w‖ * heatD2Maj t x) * ‖x‖ ^ (alpha : Real) :=
      mul_le_mul_of_nonneg_right (heatD2_bound ht v w x)
        (Real.rpow_nonneg (norm_nonneg x) _)
    _ = ‖v‖ * ‖w‖ * (‖x‖ ^ (alpha : Real) * heatD2Maj t x) := by
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_holder_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_holder_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_holder_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2_holder_bound

theorem integral_holderD2 {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (v w : V) :
    (∫ x : V, ‖heatD2 t v w x‖ * ‖x‖ ^ (alpha : Real)) ≤
      ‖v‖ * ‖w‖ * holderHeatScale alpha t * heatC2Holder (V := V) alpha := by
  have hmajor : _root_.MeasureTheory.Integrable
      (fun x : V => (‖v‖ * ‖w‖) * heatD2Holder alpha t x) :=
    (heatD2Holder_int (V := V) halpha ht).const_mul _
  have hleft : _root_.MeasureTheory.Integrable
      (fun x : V => ‖heatD2 t v w x‖ * ‖x‖ ^ (alpha : Real)) := by
    refine hmajor.mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have hpow : Continuous (fun x : V => ‖x‖ ^ (alpha : Real)) :=
        continuous_norm.rpow_const (fun _ => Or.inr alpha.coe_nonneg)
      have hd2 : Continuous (fun x : V => heatD2 t v w x) := by
        unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
        fun_prop
      exact hd2.norm.mul hpow
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg x) _))]
    exact heatD2_holder_bound alpha ht v w x
  calc
    (∫ x : V, ‖heatD2 t v w x‖ * ‖x‖ ^ (alpha : Real)) ≤
        ∫ x : V, (‖v‖ * ‖w‖) * heatD2Holder alpha t x :=
      _root_.MeasureTheory.integral_mono hleft hmajor (fun x => heatD2_holder_bound alpha ht v w x)
    _ = (‖v‖ * ‖w‖) *
        (t⁻¹ * (heatScale t) ^ (alpha : Real) * heatC2Holder (V := V) alpha) := by
      rw [_root_.MeasureTheory.integral_const_mul, integral_heatD2Holder alpha ht]
    _ = ‖v‖ * ‖w‖ * holderHeatScale alpha t * heatC2Holder (V := V) alpha := by
      rw [holderHeatScale_eq alpha ht]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_holderD2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_holderD2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_holderD2 ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.integral_holderD2

section Cancellation

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

omit [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedSpace Real F] [CompleteSpace F] in
private theorem holder_bound {alpha K : NNReal} {f : V → F}
    (hf : HolderWith K alpha f) (x y : V) :
    ‖f (x - y) - f x‖ ≤ (K : Real) * ‖y‖ ^ (alpha : Real) := by
  have hxy : _root_.Dist.dist (x - y) x = ‖y‖ := by
    rw [dist_eq_norm]
    have : (x - y) - x = -y := by abel
    rw [this, norm_neg]
  have h := hf.dist_le (x - y) x
  rw [dist_eq_norm, hxy] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.holder_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Euclidean.holder_bound target :: scope.openDecls } }

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
private theorem cancel_bound_of_holder {alpha K : NNReal} {t : Real} (ht : 0 < t)
    {f : V → F} (hf : HolderWith K alpha f) (v w x y : V) :
    ‖heatD2 t v w y • (f (x - y) - f x)‖ ≤
      (‖v‖ * ‖w‖ * (K : Real)) * heatD2Holder alpha t y := by
  calc
    ‖heatD2 t v w y • (f (x - y) - f x)‖ =
        ‖heatD2 t v w y‖ * ‖f (x - y) - f x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖heatD2 t v w y‖ * ((K : Real) * ‖y‖ ^ (alpha : Real)) :=
      mul_le_mul_of_nonneg_left (holder_bound hf x y) (norm_nonneg _)
    _ ≤ (‖v‖ * ‖w‖ * heatD2Maj t y) *
        ((K : Real) * ‖y‖ ^ (alpha : Real)) := by
      gcongr
      exact heatD2_bound ht v w y
    _ = (‖v‖ * ‖w‖ * (K : Real)) * heatD2Holder alpha t y := by
      rw [heatD2Holder_eq alpha ht]
      ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.cancel_bound_of_holder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Euclidean.cancel_bound_of_holder target :: scope.openDecls } }

omit [CompleteSpace F] in
theorem heatD2Cancel_int_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (v w x : V) :
    Integrable (fun y : V => heatD2 t v w y • (f (x - y) - f x)) := by
  have hfcont : Continuous f := hf.continuous halpha0
  have hmajor : _root_.MeasureTheory.Integrable
      (fun y : V => (‖v‖ * ‖w‖ * (K : Real)) * heatD2Holder alpha t y) :=
    (heatD2Holder_int (V := V) halpha1 ht).const_mul _
  refine hmajor.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
    fun_prop
  filter_upwards with y
  exact cancel_bound_of_holder ht hf v w x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Cancel_int_of_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Cancel_int_of_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Cancel_int_of_holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Cancel_int_of_holder

omit [CompleteSpace F] in
theorem heatD2Convolution_int_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (v w x : V) :
    Integrable (fun y : V => heatD2 t v w y • f (x - y)) := by
  have hcancel := heatD2Cancel_int_of_holder halpha0 halpha1 ht hf v w x
  have hconst := (heatD2_int ht v w).smul_const (f x)
  refine (hcancel.add hconst).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, smul_sub, sub_add_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_int_of_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_int_of_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_int_of_holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_int_of_holder

theorem heatD2Convolution_eq_cancel_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (v w x : V) :
    heatD2Convolution t v w f x = heatD2Cancel t v w f x := by
  have hcancel := heatD2Cancel_int_of_holder halpha0 halpha1 ht hf v w x
  have hconst := (heatD2_int ht v w).smul_const (f x)
  unfold heatD2Convolution heatD2Cancel
  calc
    (∫ y : V, heatD2 t v w y • f (x - y)) =
        ∫ y : V, heatD2 t v w y • (f (x - y) - f x) +
          heatD2 t v w y • f x := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards with y
      simp only [smul_sub, sub_add_cancel]
    _ = (∫ y : V, heatD2 t v w y • (f (x - y) - f x)) +
          ∫ y : V, heatD2 t v w y • f x := _root_.MeasureTheory.integral_add hcancel hconst
    _ = ∫ y : V, heatD2 t v w y • (f (x - y) - f x) := by
      rw [integral_smul_const, integral_heatD2_zero ht, zero_smul, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_eq_cancel_of_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_eq_cancel_of_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_eq_cancel_of_holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_eq_cancel_of_holder

omit [CompleteSpace F] in
theorem heatD2Cancel_norm_of_holder {alpha K : NNReal}
    (halpha : alpha ≤ 1) {t : Real} (ht : 0 < t)
    {f : V → F} (hf : HolderWith K alpha f) (v w x : V) :
    ‖heatD2Cancel t v w f x‖ ≤
      ‖v‖ * ‖w‖ * (K : Real) * holderHeatScale alpha t *
        heatC2Holder (V := V) alpha := by
  unfold heatD2Cancel
  calc
    ‖∫ y : V, heatD2 t v w y • (f (x - y) - f x)‖ ≤
        ∫ y : V, (‖v‖ * ‖w‖ * (K : Real)) * heatD2Holder alpha t y :=
      _root_.MeasureTheory.norm_integral_le_of_norm_le
        ((heatD2Holder_int (V := V) halpha ht).const_mul _)
        (Filter.Eventually.of_forall fun y => cancel_bound_of_holder ht hf v w x y)
    _ = (‖v‖ * ‖w‖ * (K : Real)) *
        (t⁻¹ * (heatScale t) ^ (alpha : Real) * heatC2Holder (V := V) alpha) := by
      rw [_root_.MeasureTheory.integral_const_mul, integral_heatD2Holder alpha ht]
    _ = ‖v‖ * ‖w‖ * (K : Real) * holderHeatScale alpha t *
        heatC2Holder (V := V) alpha := by
      rw [holderHeatScale_eq alpha ht]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Cancel_norm_of_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Cancel_norm_of_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Cancel_norm_of_holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Cancel_norm_of_holder

end Cancellation

theorem holderHeatScale_intble {alpha : NNReal} (halpha : 0 < alpha)
    {t : Real} :
    IntervalIntegrable (fun s : Real => holderHeatScale alpha (t - s)) _root_.MeasureTheory.MeasureSpace.volume 0 t := by
  have hpow : IntervalIntegrable
      (fun u : Real => u ^ ((alpha : Real) / 2 - 1)) _root_.MeasureTheory.MeasureSpace.volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by
      have : 0 < (alpha : Real) := by exact_mod_cast halpha
      linarith)
  have href := hpow.symm.comp_sub_left t
  simpa only [holderHeatScale, sub_self, sub_zero] using href

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale_intble then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale_intble"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale_intble ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale_intble

theorem timeHolderHeatScale_int {alpha : NNReal} (halpha : 0 < alpha)
    {t : Real} :
    ∫ s : Real in 0..t, holderHeatScale alpha (t - s) =
      (2 / (alpha : Real)) * t ^ ((alpha : Real) / 2) := by
  unfold holderHeatScale
  rw [intervalIntegral.integral_comp_sub_left
    (fun u : Real => u ^ ((alpha : Real) / 2 - 1)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by
    have : 0 < (alpha : Real) := by exact_mod_cast halpha
    linarith))]
  have halpha_real : (alpha : Real) ≠ 0 := by exact_mod_cast halpha.ne'
  have hexp : (alpha : Real) / 2 - 1 + 1 = (alpha : Real) / 2 := by ring
  rw [hexp, Real.zero_rpow (by positivity)]
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.timeHolderHeatScale_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.timeHolderHeatScale_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.timeHolderHeatScale_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.timeHolderHeatScale_int

section Duhamel

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def d2DuhamelHolderConst (alpha : NNReal) (v w : V) (K : NNReal) : Real :=
  ‖v‖ * ‖w‖ * (K : Real) * heatC2Holder (V := V) alpha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderConst ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderConst

def d2DuhamelHolderMajor (alpha : NNReal) (v w : V) (K : NNReal)
    (t s : Real) : Real :=
  d2DuhamelHolderConst alpha v w K * holderHeatScale alpha (t - s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderMajor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderMajor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderMajor ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderMajor

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
theorem d2DuhamelHolderMajor_intble {alpha : NNReal} (halpha : 0 < alpha)
    {t : Real} (v w : V) (K : NNReal) :
    IntervalIntegrable (d2DuhamelHolderMajor alpha v w K t) _root_.MeasureTheory.MeasureSpace.volume 0 t :=
  (holderHeatScale_intble halpha).const_mul (d2DuhamelHolderConst alpha v w K)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderMajor_intble then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderMajor_intble"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderMajor_intble ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderMajor_intble

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
theorem d2DuhamelHolderMajor_int {alpha : NNReal} (halpha : 0 < alpha)
    {t : Real} (v w : V) (K : NNReal) :
    ∫ s : Real in 0..t, d2DuhamelHolderMajor alpha v w K t s =
      d2DuhamelHolderConst alpha v w K *
        ((2 / (alpha : Real)) * t ^ ((alpha : Real) / 2)) := by
  unfold d2DuhamelHolderMajor
  rw [intervalIntegral.integral_const_mul, timeHolderHeatScale_int halpha]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderMajor_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderMajor_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderMajor_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelHolderMajor_int

theorem heatD2Duhamel_int_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (f : Real → V → F)
    (hf : ∀ s ∈ Set.Icc (0 : Real) t, HolderWith K alpha (f s))
    (v w x : V)
    (hmeas : _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : Real => heatD2Convolution (t - s) v w (f s) x)
      (volume.restrict (Set.uIoc (0 : Real) t))) :
    IntervalIntegrable
      (fun s : Real => heatD2Convolution (t - s) v w (f s) x) _root_.MeasureTheory.MeasureSpace.volume 0 t := by
  apply (d2DuhamelHolderMajor_intble (V := V) halpha0 v w K).mono_fun' hmeas
  have hne : ∀ᵐ s ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure Real), s ≠ t := by
    simp [_root_.MeasureTheory.ae_iff, _root_.MeasureTheory.NullSingletonClass.measure_singleton]
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := Set.uIoc (0 : Real) t) hne] with s hs hst
  rw [Set.uIoc_of_le ht.le] at hs
  have hstlt : s < t := lt_of_le_of_ne hs.2 hst
  rw [heatD2Convolution_eq_cancel_of_holder halpha0 halpha1 (sub_pos.mpr hstlt)
    (hf s ⟨hs.1.le, hs.2⟩) v w x]
  refine (heatD2Cancel_norm_of_holder halpha1 (sub_pos.mpr hstlt)
    (hf s ⟨hs.1.le, hs.2⟩) v w x).trans_eq ?_
  unfold d2DuhamelHolderMajor d2DuhamelHolderConst
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_int_of_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_int_of_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_int_of_holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_int_of_holder

theorem heatD2Duhamel_norm_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (f : Real → V → F)
    (hf : ∀ s ∈ Set.Icc (0 : Real) t, HolderWith K alpha (f s))
    (v w x : V)
    (hmeas : _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : Real => heatD2Convolution (t - s) v w (f s) x)
      (volume.restrict (Set.uIoc (0 : Real) t))) :
    ‖heatD2Duhamel t v w f x‖ ≤
      d2DuhamelHolderConst alpha v w K *
        ((2 / (alpha : Real)) * t ^ ((alpha : Real) / 2)) := by
  have hint := heatD2Duhamel_int_of_holder halpha0 halpha1 ht f hf v w x hmeas
  unfold heatD2Duhamel
  calc
    ‖∫ s : Real in 0..t, heatD2Convolution (t - s) v w (f s) x‖ ≤
        ∫ s : Real in 0..t, ‖heatD2Convolution (t - s) v w (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ s : Real in 0..t, d2DuhamelHolderMajor alpha v w K t s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint.norm
        (d2DuhamelHolderMajor_intble (V := V) halpha0 v w K)
      intro s hs
      rw [heatD2Convolution_eq_cancel_of_holder halpha0 halpha1 (sub_pos.mpr hs.2)
        (hf s ⟨hs.1.le, hs.2.le⟩) v w x]
      refine (heatD2Cancel_norm_of_holder halpha1 (sub_pos.mpr hs.2)
        (hf s ⟨hs.1.le, hs.2.le⟩) v w x).trans_eq ?_
      unfold d2DuhamelHolderMajor d2DuhamelHolderConst
      ring
    _ = d2DuhamelHolderConst alpha v w K *
        ((2 / (alpha : Real)) * t ^ ((alpha : Real) / 2)) :=
      d2DuhamelHolderMajor_int (V := V) halpha0 v w K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_norm_of_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_norm_of_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_norm_of_holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_norm_of_holder

end Duhamel

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem baseD2Holder_one_half (x : V) :
    baseD2Holder (1 / 2 : NNReal) x = baseD2Half x := by
  simp [baseD2Holder, baseD2Half, Real.sqrt_eq_rpow]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder_one_half then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder_one_half"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder_one_half ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.baseD2Holder_one_half

omit [Nontrivial V] in
theorem heatC2Holder_one_half :
    heatC2Holder (V := V) (1 / 2 : NNReal) = heatC2Half V := by
  unfold heatC2Holder heatC2Half
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  exact baseD2Holder_one_half x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2Holder_one_half then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2Holder_one_half"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2Holder_one_half ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatC2Holder_one_half

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2Holder_one_half (t : Real) (x : V) :
    heatD2Holder (1 / 2 : NNReal) t x = heatD2Half t x := by
  unfold heatD2Holder heatD2Half
  rw [baseD2Holder_one_half]
  norm_num [Real.sqrt_eq_rpow]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_one_half then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_one_half"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_one_half ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Holder_one_half

theorem holderHeatScale_one_half (t : Real) :
    holderHeatScale (1 / 2 : NNReal) t = heatScale34 t := by
  norm_num [holderHeatScale, heatScale34]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale_one_half then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale_one_half"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale_one_half ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.holderHeatScale_one_half

end DifferentialGeometry.Analysis.Parabolic.Euclidean
