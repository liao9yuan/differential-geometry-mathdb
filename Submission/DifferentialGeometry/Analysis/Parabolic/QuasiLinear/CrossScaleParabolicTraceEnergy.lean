import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTrace
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactResolvent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.intervalIntegral
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

namespace CrossScaleField

variable (u : CrossScaleField (I := I) (M := M) g r s a T)

omit [NeZero (Module.finrank ℝ E)] in
theorem perMode_energyIdentity
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i 0) ^ 2 +
        ∫ τ in (0 : ℝ)..t,
          2 * (tensorSobolevWeight (I := I) (M := M) i (a + 1) *
            ((u.coeffFun i τ) * (u.lowRegularity.deriv τ).coeff i)) := by
  have h0 : (0 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  set w := tensorSobolevWeight (I := I) (M := M) i (a + 1) with hw_def
  rw [u.coeffFun_sq_eq i h0 ht, mul_add]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.perMode_energyIdentity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.perMode_energyIdentity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.perMode_energyIdentity ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.perMode_energyIdentity

private lemma countable_eigenIdx :
    Countable (TensorEigenIdx (I := I) (M := M) g r s) :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.countable_tensorEigenIdx
    (I := I) (M := M) (g := g) (r := r) (s := s)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.countable_eigenIdx
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.countable_eigenIdx target :: scope.openDecls } }

def energyIntegrand
    (i : TensorEigenIdx (I := I) (M := M) g r s) (τ : ℝ) : ℝ :=
  2 * (tensorSobolevWeight (I := I) (M := M) i (a + 1) *
    ((u.coeffFun i τ) * (u.lowRegularity.deriv τ).coeff i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.energyIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.energyIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.energyIntegrand ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.energyIntegrand

omit [NeZero (Module.finrank ℝ E)] in
lemma tsum_energyIntegrand_eq (τ : ℝ) :
    ∑' i, u.energyIntegrand i τ =
      2 * ∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
        ((u.coeffFun i τ) * (u.lowRegularity.deriv τ).coeff i) := by
  unfold energyIntegrand
  rw [← tsum_mul_left]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.tsum_energyIntegrand_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.tsum_energyIntegrand_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.tsum_energyIntegrand_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.tsum_energyIntegrand_eq

omit [NeZero (Module.finrank ℝ E)] in
lemma ae_finset_abs_energyIntegrand_le :
    ∀ᵐ τ ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ S : Finset (TensorEigenIdx (I := I) (M := M) g r s),
      ∑ i ∈ S, |u.energyIntegrand i τ| ≤ 2 * (‖u.highRegularity τ‖ * ‖u.lowRegularity.deriv τ‖) := by
  filter_upwards [u.ae_coeffFun_eq_hiL2] with τ hτ S
  set f : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a + 2)) * |u.coeffFun i τ|
      with hf_def
  set d : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a) * |(u.lowRegularity.deriv τ).coeff i|
      with hd_def
  have hsummand : ∀ i, |u.energyIntegrand i τ| = 2 * (f i * d i) := by
    intro i
    unfold energyIntegrand
    rw [hf_def, hd_def, abs_mul, abs_mul,
      show |(2 : ℝ)| = 2 from by norm_num,
      abs_of_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 1)),
      tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a, abs_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsummand i), ← Finset.mul_sum]
  have hCS : (∑ i ∈ S, f i * d i) ^ 2 ≤ (∑ i ∈ S, (f i) ^ 2) * ∑ i ∈ S, (d i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S f d
  have hfsq : ∑ i ∈ S, (f i) ^ 2 ≤ ‖u.highRegularity τ‖ ^ 2 := by
    have heq : ∑ i ∈ S, (f i) ^ 2 =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 2) * ((u.highRegularity τ).coeff i) ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hf_def, mul_pow, Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)),
        sq_abs, hτ i]
    rw [heq, TensorHs.norm_sq_eq_tsum]
    refine Summable.sum_le_tsum S (fun i _ => ?_) (u.highRegularity τ).weighted_summable
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)) (sq_nonneg _)
  have hdsq : ∑ i ∈ S, (d i) ^ 2 ≤ ‖u.lowRegularity.deriv τ‖ ^ 2 := by
    have heq : ∑ i ∈ S, (d i) ^ 2 =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i a * ((u.lowRegularity.deriv τ).coeff i) ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hd_def, mul_pow, Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i a), sq_abs]
    rw [heq, TensorHs.norm_sq_eq_tsum]
    refine Summable.sum_le_tsum S (fun i _ => ?_) (u.lowRegularity.deriv τ).weighted_summable
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i a) (sq_nonneg _)
  have hsumfd_nonneg : 0 ≤ ∑ i ∈ S, f i * d i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)))
  have hsq_le : (∑ i ∈ S, f i * d i) ^ 2 ≤ (‖u.highRegularity τ‖ * ‖u.lowRegularity.deriv τ‖) ^ 2 := by
    refine le_trans hCS ?_
    rw [mul_pow]
    exact mul_le_mul hfsq hdsq (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (sq_nonneg _)
  have hfd_le : ∑ i ∈ S, f i * d i ≤ ‖u.highRegularity τ‖ * ‖u.lowRegularity.deriv τ‖ := by
    have := abs_le_of_sq_le_sq hsq_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rwa [abs_of_nonneg hsumfd_nonneg] at this
  linarith [hfd_le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.ae_finset_abs_energyIntegrand_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.ae_finset_abs_energyIntegrand_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.ae_finset_abs_energyIntegrand_le ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.ae_finset_abs_energyIntegrand_le

omit [NeZero (Module.finrank ℝ E)] in
lemma integrableOn_energyIntegrand
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    IntegrableOn (u.energyIntegrand i) (Set.Ioc (0 : ℝ) t) volume := by
  have h0 : (0 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  have hcoeff_cont : ContinuousOn (u.coeffFun i) (Set.Icc (0 : ℝ) t) :=
    (u.continuousOn_coeffFun i).mono (fun x hx => ⟨hx.1, le_trans hx.2 ht.2⟩)
  have hderiv_int : _root_.MeasureTheory.IntegrableOn (fun τ => (u.lowRegularity.deriv τ).coeff i)
      (Set.Ioc (0 : ℝ) t) volume := by
    have h := u.intervalIntegrable_deriv_coeffFun i h0 ht
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1] at h
    exact h
  have hsubIcc : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) t :=
    fun x hx => ⟨le_of_lt hx.1, hx.2⟩
  have hprod : _root_.MeasureTheory.IntegrableOn
      (fun τ => (u.coeffFun i τ) * (u.lowRegularity.deriv τ).coeff i) (Set.Ioc (0 : ℝ) t) volume :=
    MeasureTheory.IntegrableOn.continuousOn_mul_of_subset hcoeff_cont hderiv_int
      _root_.CompactIccSpace.isCompact_Icc measurableSet_Ioc hsubIcc
  have heq : (u.energyIntegrand i) = fun τ =>
      (2 * tensorSobolevWeight (I := I) (M := M) i (a + 1)) *
        ((u.coeffFun i τ) * (u.lowRegularity.deriv τ).coeff i) := by
    funext τ; unfold energyIntegrand; ring
  rw [heq]
  exact hprod.const_mul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.integrableOn_energyIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.integrableOn_energyIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.integrableOn_energyIntegrand ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.integrableOn_energyIntegrand

omit [NeZero (Module.finrank ℝ E)] in
lemma integrableOn_energyBound :
    IntegrableOn (fun s => 2 * (‖u.highRegularity s‖ * ‖u.lowRegularity.deriv s‖)) (Set.Icc (0 : ℝ) T) volume :=
  u.integrableOn_normMul.const_mul 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.integrableOn_energyBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.integrableOn_energyBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.integrableOn_energyBound ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.integrableOn_energyBound

theorem tsum_intervalIntegral_energyIntegrand_eq
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    ∑' i, (∫ s in (0 : ℝ)..t, u.energyIntegrand i s) =
      ∫ s in (0 : ℝ)..t, ∑' i, u.energyIntegrand i s := by
  have : Countable (TensorEigenIdx (I := I) (M := M) g r s) :=
    CrossScaleField.countable_eigenIdx (I := I) (M := M) (g := g) (r := r) (s := s)
  set μ : _root_.MeasureTheory.Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t) with hμ
  have hF_int : ∀ i, _root_.MeasureTheory.Integrable (u.energyIntegrand i) μ := fun i =>
    u.integrableOn_energyIntegrand i ht
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 ht.2⟩
  have hbound_int : _root_.MeasureTheory.Integrable (fun s => 2 * (‖u.highRegularity s‖ * ‖u.lowRegularity.deriv s‖)) μ :=
    u.integrableOn_energyBound.mono_set hsub
  have haebnd := _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := _root_.MeasureTheory.MeasureSpace.volume) hsub
    u.ae_finset_abs_energyIntegrand_le
  have hF_sum : Summable (fun i => ∫ s, ‖u.energyIntegrand i s‖ ∂μ) := by
    refine summable_of_sum_le (c := ∫ s, (2 * (‖u.highRegularity s‖ * ‖u.lowRegularity.deriv s‖)) ∂μ)
      (fun i => _root_.MeasureTheory.integral_nonneg (fun s => norm_nonneg _)) ?_
    intro S
    have hfin_int : ∀ i ∈ S, _root_.MeasureTheory.Integrable (fun s => ‖u.energyIntegrand i s‖) μ :=
      fun i _ => (hF_int i).norm
    rw [← MeasureTheory.integral_finsetSum S hfin_int]
    refine _root_.MeasureTheory.integral_mono_ae (MeasureTheory.integrable_finsetSum S hfin_int) hbound_int ?_
    filter_upwards [haebnd] with s hs
    calc ∑ i ∈ S, ‖u.energyIntegrand i s‖
        = ∑ i ∈ S, |u.energyIntegrand i s| := by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [Real.norm_eq_abs]
      _ ≤ 2 * (‖u.highRegularity s‖ * ‖u.lowRegularity.deriv s‖) := hs S
  have hinterchange :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum
  rw [intervalIntegral.integral_of_le ht.1]
  rw [show (∫ s in Set.Ioc (0 : ℝ) t, ∑' i, u.energyIntegrand i s ∂volume) =
        ∫ s, ∑' i, u.energyIntegrand i s ∂μ from rfl]
  rw [← hinterchange]
  refine tsum_congr (fun i => ?_)
  rw [intervalIntegral.integral_of_le ht.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.tsum_intervalIntegral_energyIntegrand_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.tsum_intervalIntegral_energyIntegrand_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.tsum_intervalIntegral_energyIntegrand_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.tsum_intervalIntegral_energyIntegrand_eq

omit [NeZero (Module.finrank ℝ E)] in
lemma summable_integral_norm_energyIntegrand {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    Summable (fun i => ∫ s, ‖u.energyIntegrand i s‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) := by
  set μ : _root_.MeasureTheory.Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t) with hμ
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 ht.2⟩
  have hbound_int : _root_.MeasureTheory.Integrable (fun s => 2 * (‖u.highRegularity s‖ * ‖u.lowRegularity.deriv s‖)) μ :=
    u.integrableOn_energyBound.mono_set hsub
  have haebnd := _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := _root_.MeasureTheory.MeasureSpace.volume) hsub
    u.ae_finset_abs_energyIntegrand_le
  refine summable_of_sum_le (c := ∫ s, (2 * (‖u.highRegularity s‖ * ‖u.lowRegularity.deriv s‖)) ∂μ)
    (fun i => _root_.MeasureTheory.integral_nonneg (fun s => norm_nonneg _)) ?_
  intro S
  have hfin_int : ∀ i ∈ S, _root_.MeasureTheory.Integrable (fun s => ‖u.energyIntegrand i s‖) μ :=
    fun i _ => (u.integrableOn_energyIntegrand i ht).norm
  rw [← MeasureTheory.integral_finsetSum S hfin_int]
  refine _root_.MeasureTheory.integral_mono_ae (MeasureTheory.integrable_finsetSum S hfin_int) hbound_int ?_
  filter_upwards [haebnd] with s hs
  calc ∑ i ∈ S, ‖u.energyIntegrand i s‖
      = ∑ i ∈ S, |u.energyIntegrand i s| := by
        refine Finset.sum_congr rfl (fun i _ => ?_); rw [Real.norm_eq_abs]
    _ ≤ 2 * (‖u.highRegularity s‖ * ‖u.lowRegularity.deriv s‖) := hs S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.summable_integral_norm_energyIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.summable_integral_norm_energyIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.summable_integral_norm_energyIntegrand ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.summable_integral_norm_energyIntegrand

omit [NeZero (Module.finrank ℝ E)] in
lemma summable_intervalIntegral_energyIntegrand {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    Summable (fun i => ∫ s in (0 : ℝ)..t, u.energyIntegrand i s) := by
  refine (u.summable_integral_norm_energyIntegrand ht).of_norm_bounded ?_
  intro i
  rw [intervalIntegral.integral_of_le ht.1, Real.norm_eq_abs]
  refine (MeasureTheory.abs_integral_le_integral_abs).trans (le_of_eq ?_)
  refine _root_.MeasureTheory.integral_congr_ae (_root_.MeasureTheory.ae_of_all _ (fun s => (Real.norm_eq_abs _).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.summable_intervalIntegral_energyIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.summable_intervalIntegral_energyIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.summable_intervalIntegral_energyIntegrand ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.summable_intervalIntegral_energyIntegrand

omit [NeZero (Module.finrank ℝ E)] in
theorem energyIdentity (hT : 0 < T) {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    ‖u.repr t‖ ^ 2 = ‖u.repr 0‖ ^ 2 +
      ∑' i, ∫ s in (0 : ℝ)..t, u.energyIntegrand i s := by
  have h0 : (0 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  have hnorm_t := u.normSq_repr hT ht
  have hnorm_0 := u.normSq_repr hT h0
  have hsum_initial : Summable
      (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i 0) ^ 2) :=
    u.summable_coeffFun_sq hT h0
  have hsum_int := u.summable_intervalIntegral_energyIntegrand ht
  rw [hnorm_t]
  have hpermode : (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 1) *
      (u.coeffFun i t) ^ 2) =
      (fun i => (tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i 0) ^ 2) +
        ∫ s in (0 : ℝ)..t, u.energyIntegrand i s) := by
    funext i
    rw [u.perMode_energyIdentity i ht]
    rfl
  rw [hpermode, hsum_initial.tsum_add hsum_int, ← hnorm_0]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.energyIdentity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.energyIdentity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.energyIdentity ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.energyIdentity

omit [NeZero (Module.finrank ℝ E)] in
theorem normSq_repr_le_initial_add_integral (hT : 0 < T) {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    ‖u.repr t‖ ^ 2 ≤ ‖u.repr 0‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, 2 * (‖u.highRegularity s‖ * ‖u.lowRegularity.deriv s‖) := by
  rw [u.energyIdentity hT ht]
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 ht.2⟩
  have hbound_eq : (∫ s in (0 : ℝ)..t, 2 * (‖u.highRegularity s‖ * ‖u.lowRegularity.deriv s‖)) =
      ∫ s, (2 * (‖u.highRegularity s‖ * ‖u.lowRegularity.deriv s‖)) ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    rw [intervalIntegral.integral_of_le ht.1]
  rw [hbound_eq]
  set μ : _root_.MeasureTheory.Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t) with hμ
  have hbound_int : _root_.MeasureTheory.Integrable (fun s => 2 * (‖u.highRegularity s‖ * ‖u.lowRegularity.deriv s‖)) μ :=
    u.integrableOn_energyBound.mono_set hsub
  have haebnd := _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := _root_.MeasureTheory.MeasureSpace.volume) hsub
    u.ae_finset_abs_energyIntegrand_le
  have hpartial : ∀ S : Finset (TensorEigenIdx (I := I) (M := M) g r s),
      ∑ i ∈ S, (∫ s in (0 : ℝ)..t, u.energyIntegrand i s) ≤
        ∫ s, (2 * (‖u.highRegularity s‖ * ‖u.lowRegularity.deriv s‖)) ∂μ := by
    intro S
    have hfin_int : ∀ i ∈ S, _root_.MeasureTheory.Integrable (u.energyIntegrand i) μ :=
      fun i _ => u.integrableOn_energyIntegrand i ht
    have hrw : ∀ i, (∫ s in (0 : ℝ)..t, u.energyIntegrand i s) =
        ∫ s, u.energyIntegrand i s ∂μ := fun i => intervalIntegral.integral_of_le ht.1
    rw [Finset.sum_congr rfl (fun i _ => hrw i),
      ← MeasureTheory.integral_finsetSum S hfin_int]
    refine _root_.MeasureTheory.integral_mono_ae (MeasureTheory.integrable_finsetSum S hfin_int) hbound_int ?_
    filter_upwards [haebnd] with s hs
    calc ∑ i ∈ S, u.energyIntegrand i s
        ≤ ∑ i ∈ S, |u.energyIntegrand i s| :=
          Finset.sum_le_sum (fun i _ => le_abs_self _)
      _ ≤ 2 * (‖u.highRegularity s‖ * ‖u.lowRegularity.deriv s‖) := hs S
  have htsum_le := (u.summable_intervalIntegral_energyIntegrand ht).tsum_le_of_sum_le hpartial
  linarith [htsum_le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.normSq_repr_le_initial_add_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.normSq_repr_le_initial_add_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.normSq_repr_le_initial_add_integral ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.normSq_repr_le_initial_add_integral

omit [NeZero (Module.finrank ℝ E)] in
lemma continuousOn_intervalIntegral_energyIntegrand
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, u.energyIntegrand i s) (_root_.Set.Icc (0 : ℝ) T) := by
  rcases le_or_gt 0 T with hT' | hT'
  · have hint : _root_.MeasureTheory.IntegrableOn (u.energyIntegrand i) (_root_.Set.uIcc (0 : ℝ) T) volume := by
      rw [_root_.Set.uIcc_of_le hT']
      exact (u.integrableOn_energyIntegrand i ⟨hT', le_rfl⟩).congr_set_ae
        (_root_.MeasureTheory.Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := T) (μ := _root_.MeasureTheory.MeasureSpace.volume)).symm
    have hcont := _root_.intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := T)
      (f := u.energyIntegrand i) (μ := _root_.MeasureTheory.MeasureSpace.volume) hint
    rwa [_root_.Set.uIcc_of_le hT'] at hcont
  · rw [_root_.Set.Icc_eq_empty (by linarith)]; exact continuousOn_empty _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.continuousOn_intervalIntegral_energyIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.continuousOn_intervalIntegral_energyIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.continuousOn_intervalIntegral_energyIntegrand ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.continuousOn_intervalIntegral_energyIntegrand

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_intervalIntegral_energyIntegrand_le (hT : 0 < T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    ‖∫ s in (0 : ℝ)..t, u.energyIntegrand i s‖ ≤
      ∫ s, ‖u.energyIntegrand i s‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) T)) := by
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ioc (0 : ℝ) T :=
    fun x hx => ⟨hx.1, le_trans hx.2 ht.2⟩
  rw [intervalIntegral.integral_of_le ht.1]
  calc ‖∫ s in Set.Ioc (0 : ℝ) t, u.energyIntegrand i s‖
      ≤ ∫ s in Set.Ioc (0 : ℝ) t, ‖u.energyIntegrand i s‖ :=
        _root_.MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ s in Set.Ioc (0 : ℝ) T, ‖u.energyIntegrand i s‖ := by
        refine _root_.MeasureTheory.setIntegral_mono_set
          ((u.integrableOn_energyIntegrand i ⟨hT.le, le_rfl⟩).norm)
          (_root_.MeasureTheory.ae_of_all _ (fun s => norm_nonneg _)) (LE.le.eventuallyLE hsub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.norm_intervalIntegral_energyIntegrand_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.norm_intervalIntegral_energyIntegrand_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.norm_intervalIntegral_energyIntegrand_le ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.norm_intervalIntegral_energyIntegrand_le

omit [NeZero (Module.finrank ℝ E)] in
theorem continuousOn_normSq_repr (hT : 0 < T) :
    ContinuousOn (fun t => ‖u.repr t‖ ^ 2) (_root_.Set.Icc (0 : ℝ) T) := by
  have hT' : (0 : ℝ) ≤ T := hT.le
  have hcont_tsum : ContinuousOn
      (fun t => ∑' i, ∫ s in (0 : ℝ)..t, u.energyIntegrand i s) (_root_.Set.Icc (0 : ℝ) T) :=
    continuousOn_tsum
      (fun i => u.continuousOn_intervalIntegral_energyIntegrand i)
      (u.summable_integral_norm_energyIntegrand (t := T) ⟨hT', le_rfl⟩)
      (fun i t ht => u.norm_intervalIntegral_energyIntegrand_le hT i ht)
  have hcont : ContinuousOn
      (fun t => ‖u.repr 0‖ ^ 2 + ∑' i, ∫ s in (0 : ℝ)..t, u.energyIntegrand i s)
      (_root_.Set.Icc (0 : ℝ) T) :=
    continuousOn_const.add hcont_tsum
  refine hcont.congr (fun t ht => ?_)
  rw [u.energyIdentity hT ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.continuousOn_normSq_repr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.continuousOn_normSq_repr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.continuousOn_normSq_repr ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.continuousOn_normSq_repr

end CrossScaleField

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry
