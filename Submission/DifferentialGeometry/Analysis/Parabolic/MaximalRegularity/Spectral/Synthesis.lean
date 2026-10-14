import Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Spectral.Plancherel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace MaximalRegularity

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

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_tensorHsBasisVec {σ : ℝ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i‖ =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) := by
  classical
  rw [TensorHs.norm_eq_sqrt_tsum]
  congr 1
  have hfun : (fun j => tensorSobolevWeight (I := I) (M := M) j σ *
        ((tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i).coeff j) ^ 2)
      = fun j => if j = i then tensorSobolevWeight (I := I) (M := M) j σ else 0 := by
    funext j
    rw [tensorHsBasisVec_coeff]
    by_cases hj : j = i
    · rw [if_pos hj, if_pos hj, one_pow, mul_one]
    · rw [if_neg hj, if_neg hj, zero_pow (by norm_num), _root_.MulZeroClass.mul_zero]
  rw [hfun, tsum_ite_eq i (fun j => tensorSobolevWeight (I := I) (M := M) j σ)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_tensorHsBasisVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_tensorHsBasisVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_tensorHsBasisVec ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_tensorHsBasisVec

def singleModeCLM {σ : ℝ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ℝ →L[ℝ] TensorHs (I := I) (M := M) g r s σ :=
  LinearMap.mkContinuous
    { toFun := fun c => c • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i
      map_add' := fun c d => by rw [add_smul]
      map_smul' := fun a c => by rw [smul_smul]; rfl }
    (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))
    (fun c => by
      change ‖c • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i‖ ≤ _
      rw [norm_smul, norm_tensorHsBasisVec (I := I) (M := M) i, Real.norm_eq_abs]
      exact le_of_eq (mul_comm _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeCLM

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem singleModeCLM_apply {σ : ℝ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) (c : ℝ) :
    singleModeCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i c =
      c • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeCLM_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeCLM_apply

open scoped _root_.Classical in
omit [NeZero (Module.finrank ℝ E)] in
theorem singleModeCLM_coeff {σ : ℝ}
    (i j : TensorEigenIdx (I := I) (M := M) g r s) (c : ℝ) :
    (singleModeCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i c).coeff j =
      (if j = i then c else 0) := by
  classical
  rw [singleModeCLM_apply]
  simp only [TensorHs.smul_coeff, tensorHsBasisVec_coeff]
  by_cases hj : j = i
  · rw [if_pos hj, if_pos hj, mul_one]
  · rw [if_neg hj, if_neg hj, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeCLM_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeCLM_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeCLM_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeCLM_coeff

variable {σ : ℝ} {T : ℝ}

def singleModeTimeL2 {σ : ℝ}
    {T : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeL2 ℝ T →L[ℝ] timeL2 (TensorHs (I := I) (M := M) g r s σ) T :=
  (singleModeCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i).compLpL 2 (timeMeasure T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeTimeL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeTimeL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeTimeL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeTimeL2

omit [NeZero (Module.finrank ℝ E)] in
theorem singleModeTimeL2_coeFn (i : TensorEigenIdx (I := I) (M := M) g r s)
    (gf : timeL2 ℝ T) :
    singleModeTimeL2 (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i gf =ᵐ[timeMeasure T]
      fun t => (gf t) • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i := by
  have h := (singleModeCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) gf
  exact h.trans (Eventually.of_forall fun t => singleModeCLM_apply (I := I) (M := M) i (gf t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeTimeL2_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeTimeL2_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeTimeL2_coeFn ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeTimeL2_coeFn

open scoped _root_.Classical in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeModeCoeff_singleModeTimeL2
    (i j : TensorEigenIdx (I := I) (M := M) g r s) (gf : timeL2 ℝ T) :
    timeModeCoeff (I := I) (M := M)
        (singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf) j =
      (if j = i then gf else 0) := by
  classical
  refine Lp.ext ?_
  have hlhs := timeModeCoeff_coeFn (I := I) (M := M)
    (singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf) j
  have hsm := singleModeTimeL2_coeFn (I := I) (M := M)
    (σ := σ) i gf
  have hcoord : ∀ t,
      (((gf t) • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i).coeff j)
        = (if j = i then gf t else 0) := by
    intro t
    simp only [TensorHs.smul_coeff, tensorHsBasisVec_coeff]
    by_cases hj : j = i
    · rw [if_pos hj, if_pos hj, mul_one]
    · rw [if_neg hj, if_neg hj, _root_.MulZeroClass.mul_zero]
  by_cases hj : j = i
  · filter_upwards [hlhs, hsm] with t ht hsmt
    rw [ht, hsmt, hcoord t, if_pos hj, if_pos hj]
  · have hzero := Lp.coeFn_zero (E := ℝ) (p := 2) (μ := timeMeasure T)
    filter_upwards [hlhs, hsm, hzero] with t ht hsmt hzt
    rw [ht, hsmt, hcoord t, if_neg hj, if_neg hj, hzt]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeModeCoeff_singleModeTimeL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeModeCoeff_singleModeTimeL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeModeCoeff_singleModeTimeL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeModeCoeff_singleModeTimeL2

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_singleModeTimeL2_sq (i : TensorEigenIdx (I := I) (M := M) g r s)
    (gf : timeL2 ℝ T) :
    ‖singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf‖ ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i σ * ‖gf‖ ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral, TimeSobolev.norm_sq_eq_integral,
    ← MeasureTheory.integral_const_mul]
  refine _root_.MeasureTheory.integral_congr_ae ?_
  filter_upwards [singleModeTimeL2_coeFn (I := I) (M := M)
    (σ := σ) i gf] with t ht
  rw [ht, norm_smul, mul_pow, norm_tensorHsBasisVec (I := I) (M := M) i,
    Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i σ),
    Real.norm_eq_abs, sq_abs, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_singleModeTimeL2_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_singleModeTimeL2_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_singleModeTimeL2_sq ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_singleModeTimeL2_sq

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_singleModeTimeL2 (i : TensorEigenIdx (I := I) (M := M) g r s)
    (gf : timeL2 ℝ T) :
    ‖singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf‖ =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * ‖gf‖ := by
  have hsq := norm_singleModeTimeL2_sq (I := I) (M := M)
    (σ := σ) i gf
  have hrhs_nonneg : 0 ≤ Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * ‖gf‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have h := Real.sqrt_le_sqrt (le_of_eq hsq)
  have h' := Real.sqrt_le_sqrt (le_of_eq hsq.symm)
  have hsqrt : ‖singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf‖ =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ * ‖gf‖ ^ 2) := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [hsqrt, Real.sqrt_mul (tensorSobolevWeight_nonneg (I := I) (M := M) i σ),
    Real.sqrt_sq (norm_nonneg _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_singleModeTimeL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_singleModeTimeL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_singleModeTimeL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.norm_singleModeTimeL2

omit [NeZero (Module.finrank ℝ E)] in
theorem inner_tensorHsBasisVec_eq_zero {i j : TensorEigenIdx (I := I) (M := M) g r s}
    (hij : i ≠ j) :
    (_root_.Inner.inner ℝ (tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i)
      (tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ j) : ℝ) = 0 := by
  classical
  rw [TensorHs.inner_def]
  have hterm : (fun k => tensorSobolevWeight (I := I) (M := M) k σ *
        ((tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i).coeff k *
          (tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ j).coeff k))
      = fun _ => (0 : ℝ) := by
    funext k
    rw [tensorHsBasisVec_coeff, tensorHsBasisVec_coeff]
    by_cases hki : k = i
    · rw [if_pos hki, if_neg (by rw [hki]; exact hij), _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero]
    · rw [if_neg hki, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.mul_zero]
  rw [hterm, tsum_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.inner_tensorHsBasisVec_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.inner_tensorHsBasisVec_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.inner_tensorHsBasisVec_eq_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.inner_tensorHsBasisVec_eq_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem inner_singleModeTimeL2_eq_zero
    {i j : TensorEigenIdx (I := I) (M := M) g r s} (hij : i ≠ j)
    (gf hf : timeL2 ℝ T) :
    (_root_.Inner.inner ℝ (singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf)
      (singleModeTimeL2 (I := I) (M := M) (σ := σ) j hf) : ℝ) = 0 := by
  rw [TimeSobolev.inner_def]
  rw [show (∫ t in Set.Icc (0 : ℝ) T,
        inner ℝ (singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf t)
          (singleModeTimeL2 (I := I) (M := M) (σ := σ) j hf t))
      = ∫ t in Set.Icc (0 : ℝ) T, (0 : ℝ) from ?_, _root_.MeasureTheory.integral_zero]
  refine _root_.MeasureTheory.integral_congr_ae ?_
  filter_upwards [singleModeTimeL2_coeFn (I := I) (M := M)
      (σ := σ) i gf,
    singleModeTimeL2_coeFn (I := I) (M := M)
      (σ := σ) j hf] with t hit hjt
  rw [hit, hjt, inner_smul_left, inner_smul_right,
    inner_tensorHsBasisVec_eq_zero (I := I) (M := M) hij, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.inner_singleModeTimeL2_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.inner_singleModeTimeL2_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.inner_singleModeTimeL2_eq_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.inner_singleModeTimeL2_eq_zero

def singleModeScaledCLM {σ : ℝ}
    {T : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeL2 ℝ T →L[ℝ]
      timeL2 (TensorHs (I := I) (M := M) g r s σ) T :=
  (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ •
    singleModeTimeL2 (I := I) (M := M) (σ := σ) (T := T) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeScaledCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeScaledCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeScaledCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeScaledCLM

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem singleModeScaledCLM_apply
    (i : TensorEigenIdx (I := I) (M := M) g r s) (gf : timeL2 ℝ T) :
    singleModeScaledCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i gf =
      (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ •
        singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf := by
  rw [singleModeScaledCLM, smul_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeScaledCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeScaledCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeScaledCLM_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeScaledCLM_apply

def singleModeIsometry {σ : ℝ}
    {T : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeL2 ℝ T →ₗᵢ[ℝ]
      timeL2 (TensorHs (I := I) (M := M) g r s σ) T :=
  { (singleModeScaledCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i).toLinearMap with
    norm_map' := fun gf => by
      have hsqrt_pos : 0 < Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) :=
        Real.sqrt_pos.mpr (tensorSobolevWeight_pos (I := I) (M := M) i σ)
      have hval : ((singleModeScaledCLM (I := I) (M := M) (g := g) (r := r) (s := s)
            (σ := σ) i).toLinearMap gf) =
            (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ •
              singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf :=
        singleModeScaledCLM_apply (I := I) (M := M) i gf
      rw [hval, norm_smul, norm_singleModeTimeL2 (I := I) (M := M) i, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hsqrt_pos), ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt hsqrt_pos), one_mul] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeIsometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeIsometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeIsometry ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeIsometry

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem singleModeIsometry_apply
    (i : TensorEigenIdx (I := I) (M := M) g r s) (gf : timeL2 ℝ T) :
    singleModeIsometry (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i gf =
      (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ •
        singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf :=
  singleModeScaledCLM_apply (I := I) (M := M) i gf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeIsometry_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeIsometry_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeIsometry_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeIsometry_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem orthogonalFamily_singleModeIsometry {σ : ℝ} {T : ℝ} :
    OrthogonalFamily ℝ (fun _ : TensorEigenIdx (I := I) (M := M) g r s => timeL2 ℝ T)
      (fun i => singleModeIsometry (I := I) (M := M) (g := g) (r := r) (s := s)
        (σ := σ) (T := T) i) := by
  intro i j hij gf hf
  rw [singleModeIsometry_apply, singleModeIsometry_apply, inner_smul_left,
    inner_smul_right, inner_singleModeTimeL2_eq_zero (I := I) (M := M) hij,
    _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.orthogonalFamily_singleModeIsometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.orthogonalFamily_singleModeIsometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.orthogonalFamily_singleModeIsometry ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.orthogonalFamily_singleModeIsometry

omit [NeZero (Module.finrank ℝ E)] in
theorem singleModeTimeL2_eq_isometry (i : TensorEigenIdx (I := I) (M := M) g r s)
    (gf : timeL2 ℝ T) :
    singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf =
      singleModeIsometry (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i
        ((Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)) • gf) := by
  have hsqrt_pos : 0 < Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) :=
    Real.sqrt_pos.mpr (tensorSobolevWeight_pos (I := I) (M := M) i σ)
  rw [singleModeIsometry_apply, map_smul, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hsqrt_pos), one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeTimeL2_eq_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeTimeL2_eq_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeTimeL2_eq_isometry ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.singleModeTimeL2_eq_isometry

omit [NeZero (Module.finrank ℝ E)] in
theorem summable_singleModeTimeL2
    (gFam : TensorEigenIdx (I := I) (M := M) g r s → timeL2 ℝ T)
    (hsum : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
      ‖gFam i‖ ^ 2)) :
    Summable (fun i => singleModeTimeL2 (I := I) (M := M) (σ := σ) i
      (gFam i)) := by
  have hrw : (fun i => singleModeTimeL2 (I := I) (M := M) (σ := σ) i
        (gFam i))
      = fun i => singleModeIsometry (I := I) (M := M) (g := g) (r := r) (s := s)
          (σ := σ) i
          ((Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)) • gFam i) := by
    funext i
    exact singleModeTimeL2_eq_isometry (I := I) (M := M) i (gFam i)
  rw [hrw]
  rw [(orthogonalFamily_singleModeIsometry (I := I) (M := M)
    (g := g) (r := r) (s := s) (σ := σ) (T := T)).summable_iff_norm_sq_summable]
  refine hsum.congr (fun i => ?_)
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_singleModeTimeL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_singleModeTimeL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_singleModeTimeL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.summable_singleModeTimeL2

def timeL2OfModes
    (gFam : TensorEigenIdx (I := I) (M := M) g r s → timeL2 ℝ T) :
    timeL2 (TensorHs (I := I) (M := M) g r s σ) T :=
  ∑' i, singleModeTimeL2 (I := I) (M := M) (σ := σ) i (gFam i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeL2OfModes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeL2OfModes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeL2OfModes ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeL2OfModes

omit [NeZero (Module.finrank ℝ E)] in
theorem timeL2OfModes_timeModeCoeff
    (gFam : TensorEigenIdx (I := I) (M := M) g r s → timeL2 ℝ T)
    (hsum : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
      ‖gFam i‖ ^ 2))
    (j : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (timeL2OfModes (I := I) (M := M) (σ := σ) gFam) j =
      gFam j := by
  classical
  have hsumm := summable_singleModeTimeL2 (I := I) (M := M) gFam hsum
  have hcomm : timeModeCoeff (I := I) (M := M)
        (timeL2OfModes (I := I) (M := M) (σ := σ) gFam) j =
      ∑' i, timeModeCoeff (I := I) (M := M)
        (singleModeTimeL2 (I := I) (M := M) (σ := σ) i (gFam i)) j := by
    rw [timeL2OfModes]
    exact ContinuousLinearMap.map_tsum
      ((tensorHsCoeffL (I := I) (M := M) j).compLpL 2 (timeMeasure T))
      hsumm
  rw [hcomm]
  have hterm : (fun i => timeModeCoeff (I := I) (M := M)
        (singleModeTimeL2 (I := I) (M := M) (σ := σ) i (gFam i)) j)
      = fun i => if i = j then gFam i else 0 := by
    funext i
    rw [timeModeCoeff_singleModeTimeL2 (I := I) (M := M) i j (gFam i)]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · rw [if_neg hij, if_neg (fun h => hij h.symm)]
  rw [hterm, tsum_ite_eq j gFam]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeL2OfModes_timeModeCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeL2OfModes_timeModeCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeL2OfModes_timeModeCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.timeL2OfModes_timeModeCoeff

end MaximalRegularity
end Parabolic
end Analysis
end DifferentialGeometry
