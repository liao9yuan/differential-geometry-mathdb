import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Covering.OneDim

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.intervalIntegral
open scoped _root_.ENNReal _root_.NNReal _root_.Topology _root_.InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

section VectorLebesgueDifferentiation

open _root_.IsUnifLocDoublingMeasure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem average_Icc_eq {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) :
    (⨍ t in _root_.Set.Icc a b, f t) = (b - a)⁻¹ • ∫ t in _root_.Set.Icc a b, f t := by
  rw [_root_.MeasureTheory.setAverage_eq, _root_.MeasureTheory.measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.average_Icc_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.average_Icc_eq target :: scope.openDecls } }

omit [CompleteSpace E] in
private theorem slope_integral_eq_average_right {f : ℝ → E}
    (hg : ∀ a b : ℝ, IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume a b) (c x y : ℝ) (hxy : x ≤ y) :
    slope (fun u => ∫ t in c..u, f t) x y = ⨍ t in _root_.Set.Icc x y, f t := by
  rw [average_Icc_eq hxy, slope_def_module, _root_.intervalIntegral.integral_interval_sub_left (hg c y) (hg c x),
    _root_.intervalIntegral.integral_of_le hxy, _root_.MeasureTheory.integral_Icc_eq_integral_Ioc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.slope_integral_eq_average_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.slope_integral_eq_average_right target :: scope.openDecls } }

omit [CompleteSpace E] in
private theorem slope_integral_eq_average_left {f : ℝ → E}
    (hg : ∀ a b : ℝ, IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume a b) (c x y : ℝ) (hyx : y ≤ x) :
    slope (fun u => ∫ t in c..u, f t) x y = ⨍ t in _root_.Set.Icc y x, f t := by
  rw [average_Icc_eq hyx, slope_def_module, _root_.MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← _root_.intervalIntegral.integral_of_le hyx, ← _root_.intervalIntegral.integral_interval_sub_left (hg c x) (hg c y),
    ← neg_sub x y, inv_neg, neg_smul, ← smul_neg, neg_sub]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.slope_integral_eq_average_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.slope_integral_eq_average_left target :: scope.openDecls } }

theorem locallyIntegrable_ae_hasDerivAt_integral
    {f : ℝ → E} (hf : _root_.MeasureTheory.LocallyIntegrable f _root_.MeasureTheory.MeasureSpace.volume) :
    ∀ᵐ x, ∀ c, HasDerivAt (fun x => ∫ t in c..x, f t) (f x) x := by
  have hg : ∀ a b : ℝ, IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume a b := fun a b =>
    intervalIntegrable_iff.mpr <|
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set _root_.Set.uIoc_subset_uIcc
  have LDT := (_root_.IsUnifLocDoublingMeasure.vitaliFamily (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ) 1).ae_tendsto_average hf
  filter_upwards [LDT] with x hx
  intro c
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  refine ⟨?_, ?_⟩
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp (Real.tendsto_Icc_vitaliFamily_left x))
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact slope_integral_eq_average_left hg c x y (le_of_lt hy)
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp (Real.tendsto_Icc_vitaliFamily_right x))
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact slope_integral_eq_average_right hg c x y (le_of_lt hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.locallyIntegrable_ae_hasDerivAt_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.locallyIntegrable_ae_hasDerivAt_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.locallyIntegrable_ae_hasDerivAt_integral ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.locallyIntegrable_ae_hasDerivAt_integral

end VectorLebesgueDifferentiation

variable {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]
variable {T : ℝ}

def timeH1 (X : Type*) [NormedAddCommGroup X] (T : ℝ) : Type _ :=
  WithLp 2 (X × timeL2 X T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1

namespace timeH1

section NormedInstances

variable [NormedSpace ℝ X]

instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instNormedAddCommGroup : NormedAddCommGroup (timeH1 X T) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (X × timeL2 X T)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instNormedAddCommGroup

instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instNormedSpaceReal : NormedSpace ℝ (timeH1 X T) :=
  inferInstanceAs (NormedSpace ℝ (WithLp 2 (X × timeL2 X T)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instNormedSpaceReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instNormedSpaceReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instNormedSpaceReal ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instNormedSpaceReal

instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instCompleteSpace : CompleteSpace (timeH1 X T) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (X × timeL2 X T)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instCompleteSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instCompleteSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instCompleteSpace ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instCompleteSpace

end NormedInstances

noncomputable instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instInnerProductSpaceReal [InnerProductSpace ℝ X] :
    InnerProductSpace ℝ (timeH1 X T) :=
  inferInstanceAs (InnerProductSpace ℝ (WithLp 2 (X × timeL2 X T)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instInnerProductSpaceReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instInnerProductSpaceReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instInnerProductSpaceReal ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.instInnerProductSpaceReal

section Normed

variable [NormedSpace ℝ X]

def mk (u₀ : X) (v : timeL2 X T) : timeH1 X T :=
  WithLp.toLp 2 (u₀, v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.mk ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.mk

def initial (u : timeH1 X T) : X :=
  (WithLp.ofLp u).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial

def deriv (u : timeH1 X T) : timeL2 X T :=
  (WithLp.ofLp u).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv

omit [CompleteSpace X] [NormedSpace ℝ X] in
@[simp]
theorem initial_mk (u₀ : X) (v : timeL2 X T) : (mk u₀ v).initial = u₀ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_mk ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_mk

omit [CompleteSpace X] [NormedSpace ℝ X] in
@[simp]
theorem deriv_mk (u₀ : X) (v : timeL2 X T) : (mk u₀ v).deriv = v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_mk ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_mk

omit [CompleteSpace X] [NormedSpace ℝ X] in
@[simp]
theorem mk_initial_deriv (u : timeH1 X T) : mk u.initial u.deriv = u := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.mk_initial_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.mk_initial_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.mk_initial_deriv ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.mk_initial_deriv

omit [CompleteSpace X] [NormedSpace ℝ X] in
@[ext]
theorem ext {u w : timeH1 X T} (hinit : u.initial = w.initial) (hderiv : u.deriv = w.deriv) :
    u = w := by
  rw [← mk_initial_deriv u, ← mk_initial_deriv w, hinit, hderiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.ext ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.ext

omit [CompleteSpace X] [NormedSpace ℝ X] in
@[simp]
theorem initial_add (u w : timeH1 X T) : (u + w).initial = u.initial + w.initial := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_add

omit [CompleteSpace X] [NormedSpace ℝ X] in
@[simp]
theorem deriv_add (u w : timeH1 X T) : (u + w).deriv = u.deriv + w.deriv := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_add

omit [CompleteSpace X] in
@[simp]
theorem initial_smul (c : ℝ) (u : timeH1 X T) : (c • u).initial = c • u.initial := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_smul

omit [CompleteSpace X] in
@[simp]
theorem deriv_smul (c : ℝ) (u : timeH1 X T) : (c • u).deriv = c • u.deriv := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_smul

omit [CompleteSpace X] [NormedSpace ℝ X] in
@[simp]
theorem initial_zero : (0 : timeH1 X T).initial = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.initial_zero

omit [CompleteSpace X] [NormedSpace ℝ X] in
@[simp]
theorem deriv_zero : (0 : timeH1 X T).deriv = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_zero

omit [CompleteSpace X] [NormedSpace ℝ X] in
theorem norm_sq_eq (u : timeH1 X T) :
    ‖u‖ ^ 2 = ‖u.initial‖ ^ 2 + ‖u.deriv‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_sq_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_sq_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_sq_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_sq_eq

omit [CompleteSpace X] [NormedSpace ℝ X] in
theorem norm_initial_le (u : timeH1 X T) : ‖u.initial‖ ≤ ‖u‖ := by
  have h := norm_sq_eq u
  nlinarith [norm_nonneg u.initial, norm_nonneg u.deriv, norm_nonneg u, sq_nonneg ‖u.deriv‖]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_initial_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_initial_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_initial_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_initial_le

omit [CompleteSpace X] [NormedSpace ℝ X] in
theorem norm_deriv_le (u : timeH1 X T) : ‖u.deriv‖ ≤ ‖u‖ := by
  have h := norm_sq_eq u
  nlinarith [norm_nonneg u.initial, norm_nonneg u.deriv, norm_nonneg u, sq_nonneg ‖u.initial‖]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_deriv_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_deriv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_deriv_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_deriv_le

def trace0 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (T : ℝ) : timeH1 X T →L[ℝ] X :=
  WithLp.fstL 2 ℝ X (timeL2 X T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0

def timeDeriv (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (T : ℝ) : timeH1 X T →L[ℝ] timeL2 X T :=
  WithLp.sndL 2 ℝ X (timeL2 X T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv

omit [CompleteSpace X] in
@[simp] theorem trace0_apply (u : timeH1 X T) : trace0 X T u = u.initial := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0_apply

omit [CompleteSpace X] in
@[simp] theorem timeDeriv_apply (u : timeH1 X T) : timeDeriv X T u = u.deriv := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv_apply

omit [CompleteSpace X] in
@[simp] theorem trace0_mk (u₀ : X) (v : timeL2 X T) : trace0 X T (mk u₀ v) = u₀ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0_mk ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0_mk

omit [CompleteSpace X] in
@[simp] theorem timeDeriv_mk (u₀ : X) (v : timeL2 X T) : timeDeriv X T (mk u₀ v) = v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv_mk ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv_mk

def toFun (u : timeH1 X T) : ℝ → X :=
  fun t => u.initial + ∫ s in (0 : ℝ)..t, u.deriv s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun

omit [CompleteSpace X] in
@[simp]
theorem toFun_apply (u : timeH1 X T) (t : ℝ) :
    u.toFun t = u.initial + ∫ s in (0 : ℝ)..t, u.deriv s :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_apply

omit [CompleteSpace X] in
theorem toFun_zero (u : timeH1 X T) : u.toFun 0 = u.initial := by
  simp [toFun]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_zero

omit [CompleteSpace X] [NormedSpace ℝ X] in
theorem intervalIntegrable_deriv {a b : ℝ} (u : timeH1 X T)
    (ha : a ∈ _root_.Set.Icc (0 : ℝ) T) (hb : b ∈ _root_.Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun s => u.deriv s) _root_.MeasureTheory.MeasureSpace.volume a b := by
  have hsub : _root_.Set.uIcc a b ⊆ _root_.Set.Icc (0 : ℝ) T :=
    _root_.Set.uIcc_subset_Icc ha hb
  refine MeasureTheory.IntegrableOn.intervalIntegrable ?_
  exact (TimeSobolev.integrableOn u.deriv).mono_set hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.intervalIntegrable_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.intervalIntegrable_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.intervalIntegrable_deriv ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.intervalIntegrable_deriv

omit [CompleteSpace X] in
theorem continuousOn_toFun (u : timeH1 X T) :
    ContinuousOn u.toFun (_root_.Set.Icc (0 : ℝ) T) := by
  rcases le_or_gt 0 T with hT | hT
  · have hcont : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, u.deriv s) (_root_.Set.Icc (0 : ℝ) T) := by
      have h := _root_.intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := T)
        (f := fun s => u.deriv s) (μ := _root_.MeasureTheory.MeasureSpace.volume)
        (by
          rw [_root_.Set.uIcc_of_le hT]
          exact TimeSobolev.integrableOn u.deriv)
      rwa [_root_.Set.uIcc_of_le hT] at h
    exact continuousOn_const.add hcont
  · rw [_root_.Set.Icc_eq_empty (by linarith)]
    exact continuousOn_empty _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.continuousOn_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.continuousOn_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.continuousOn_toFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.continuousOn_toFun

omit [CompleteSpace X] in
theorem continuousWithinAt_toFun (u : timeH1 X T) {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    ContinuousWithinAt u.toFun (_root_.Set.Icc (0 : ℝ) T) t :=
  u.continuousOn_toFun t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.continuousWithinAt_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.continuousWithinAt_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.continuousWithinAt_toFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.continuousWithinAt_toFun

omit [CompleteSpace X] in
private theorem deriv_memLp (hT : 0 ≤ T) (f : ℝ → X)
    (hf : ContDiffOn ℝ 1 f (_root_.Set.Icc (0 : ℝ) T)) :
    MemLp (_root_.deriv f) 2 (timeMeasure T) := by
  rcases hT.eq_or_lt with hT0 | hTpos
  · subst T
    rw [timeMeasure_eq_zero_of_nonpos le_rfl]
    exact _root_.MeasureTheory.memLp_measure_zero
  · let v : ℝ → X := derivWithin f (_root_.Set.Icc (0 : ℝ) T)
    have hv : ContinuousOn v (_root_.Set.Icc (0 : ℝ) T) := by
      simpa only [v] using
        hf.continuousOn_derivWithin (uniqueDiffOn_Icc hTpos) le_rfl
    have hmem : _root_.MeasureTheory.MemLp v 2 (timeMeasure T) :=
      TimeSobolev.memLp_of_continuousOn hv
    have hae : v =ᵐ[timeMeasure T] _root_.deriv f := by
      unfold timeMeasure
      rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc]
      filter_upwards [_root_.MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
      simpa only [v] using
        derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    exact MemLp.ae_eq hae hmem

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_memLp target :: scope.openDecls } }

noncomputable def ofContDiffOn (hT : 0 ≤ T) (f : ℝ → X)
    (hf : ContDiffOn ℝ 1 f (_root_.Set.Icc (0 : ℝ) T)) : timeH1 X T :=
  mk (f 0) ((deriv_memLp hT f hf).toLp (_root_.deriv f))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.ofContDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.ofContDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.ofContDiffOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.ofContDiffOn

omit [CompleteSpace X] in
theorem deriv_ofContDiffOn (hT : 0 ≤ T) (f : ℝ → X)
    (hf : ContDiffOn ℝ 1 f (_root_.Set.Icc (0 : ℝ) T)) :
    (ofContDiffOn hT f hf).deriv =ᵐ[timeMeasure T] _root_.deriv f := by
  simpa only [ofContDiffOn, deriv_mk] using
    (deriv_memLp hT f hf).coeFn_toLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_ofContDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_ofContDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_ofContDiffOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.deriv_ofContDiffOn

theorem toFun_ofContDiffOn (hT : 0 ≤ T) (f : ℝ → X)
    (hf : ContDiffOn ℝ 1 f (_root_.Set.Icc (0 : ℝ) T)) :
    EqOn (ofContDiffOn hT f hf).toFun f (_root_.Set.Icc (0 : ℝ) T) := by
  intro t ht
  rw [toFun_apply, show (ofContDiffOn hT f hf).initial = f 0 by
    simp only [ofContDiffOn, initial_mk]]
  have hae := deriv_ofContDiffOn hT f hf
  have hae' : (fun s ↦ (ofContDiffOn hT f hf).deriv s)
      =ᵐ[volume.restrict (_root_.Set.Icc (0 : ℝ) T)] _root_.deriv f := by
    simpa only [timeMeasure] using hae
  have hsub : _root_.Set.uIoc (0 : ℝ) t ⊆ _root_.Set.Icc (0 : ℝ) T := by
    intro s hs
    rw [_root_.Set.uIoc_of_le ht.1] at hs
    exact ⟨le_of_lt hs.1, le_trans hs.2 ht.2⟩
  have hrestr : (fun s ↦ (ofContDiffOn hT f hf).deriv s)
      =ᵐ[volume.restrict (_root_.Set.uIoc (0 : ℝ) t)] _root_.deriv f :=
    hae'.filter_mono (_root_.MeasureTheory.ae_mono (Measure.restrict_mono hsub le_rfl))
  have hint : (∫ s in (0 : ℝ)..t, (ofContDiffOn hT f hf).deriv s)
      = ∫ s in (0 : ℝ)..t, _root_.deriv f s :=
    intervalIntegral.integral_congr_ae (_root_.MeasureTheory.ae_imp_of_ae_restrict hrestr)
  rw [hint, intervalIntegral.integral_deriv_of_contDiffOn_Icc
    (hf.mono (_root_.Set.Icc_subset_Icc le_rfl ht.2)) ht.1]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_ofContDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_ofContDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_ofContDiffOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_ofContDiffOn

omit [CompleteSpace X] in
theorem toFun_eq_trace0_add_integral (u : timeH1 X T) (t : ℝ) :
    u.toFun t = trace0 X T u + ∫ s in (0 : ℝ)..t, (timeDeriv X T u) s :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_eq_trace0_add_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_eq_trace0_add_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_eq_trace0_add_integral ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_eq_trace0_add_integral

omit [CompleteSpace X] in
theorem toFun_sub_toFun (u : timeH1 X T) {t₀ t₁ : ℝ}
    (ht₀ : t₀ ∈ _root_.Set.Icc (0 : ℝ) T) (ht₁ : t₁ ∈ _root_.Set.Icc (0 : ℝ) T) :
    u.toFun t₁ - u.toFun t₀ = ∫ s in t₀..t₁, u.deriv s := by
  have h0 : (0 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) T := by
    refine ⟨le_rfl, ?_⟩
    rcases ht₀ with ⟨h0t₀, ht₀T⟩
    linarith
  simp only [toFun_apply]
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left
    (u.intervalIntegrable_deriv h0 ht₁) (u.intervalIntegrable_deriv h0 ht₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_sub_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_sub_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_sub_toFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_sub_toFun

theorem hasDerivWithinAt_toFun_of_continuousOn (u : timeH1 X T) {g : ℝ → X}
    (hg : ContinuousOn g (_root_.Set.Icc (0 : ℝ) T)) (hrep : u.deriv =ᵐ[timeMeasure T] g)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt u.toFun (g t) (_root_.Set.Icc (0 : ℝ) T) t := by
  rcases le_or_gt 0 T with hT | hT
  · have h0 : (0 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have hgIcc : _root_.MeasureTheory.IntegrableOn g (_root_.Set.Icc (0 : ℝ) T) volume :=
      (TimeSobolev.memLp_of_continuousOn hg).integrable (by norm_num)
    have hrepvol : (fun r => u.deriv r) =ᵐ[volume.restrict (_root_.Set.Icc (0 : ℝ) T)] g := hrep
    have hae : ∀ s ∈ _root_.Set.Icc (0 : ℝ) T, (∫ r in (0 : ℝ)..s, u.deriv r)
        = ∫ r in (0 : ℝ)..s, g r := by
      intro s hs
      refine intervalIntegral.integral_congr_ae ?_
      have hsub : Set.uIoc (0 : ℝ) s ⊆ _root_.Set.Icc (0 : ℝ) T := by
        intro r hr
        rw [Set.uIoc, min_eq_left hs.1, max_eq_right hs.1] at hr
        exact ⟨le_of_lt hr.1, le_trans hr.2 hs.2⟩
      have hrestr : (fun r => u.deriv r) =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) s)] g :=
        hrepvol.filter_mono (_root_.MeasureTheory.ae_mono (Measure.restrict_mono hsub le_rfl))
      exact _root_.MeasureTheory.ae_imp_of_ae_restrict hrestr
    have hderiv : HasDerivWithinAt (fun s => ∫ r in (0 : ℝ)..s, g r) (g t)
        (_root_.Set.Icc (0 : ℝ) T) t := by
      have hfact : Fact (t ∈ _root_.Set.Icc (0 : ℝ) T) := ⟨ht⟩
      have hint : IntervalIntegrable g _root_.MeasureTheory.MeasureSpace.volume 0 t :=
        MeasureTheory.IntegrableOn.intervalIntegrable (by
          rw [_root_.Set.uIcc_of_le ht.1]
          exact hgIcc.mono_set (_root_.Set.Icc_subset_Icc le_rfl ht.2))
      have hmeas : StronglyMeasurableAtFilter g (𝓝[_root_.Set.Icc (0 : ℝ) T] t) volume :=
        ⟨Icc (0 : ℝ) T, self_mem_nhdsWithin,
          (hg.aestronglyMeasurable measurableSet_Icc)⟩
      have hcont : ContinuousWithinAt g (_root_.Set.Icc (0 : ℝ) T) t := hg t ht
      exact intervalIntegral.integral_hasDerivWithinAt_right hint hmeas hcont
    have hderiv' : HasDerivWithinAt (fun s => ∫ r in (0 : ℝ)..s, u.deriv r) (g t)
        (_root_.Set.Icc (0 : ℝ) T) t :=
      hderiv.congr (fun s hs => hae s hs) (hae t ht)
    have := hderiv'.const_add u.initial
    simpa only [toFun] using! this
  · rw [_root_.Set.Icc_eq_empty (by linarith)] at ht
    exact absurd ht (_root_.Set.notMem_empty t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.hasDerivWithinAt_toFun_of_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.hasDerivWithinAt_toFun_of_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.hasDerivWithinAt_toFun_of_continuousOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.hasDerivWithinAt_toFun_of_continuousOn

theorem ae_hasDerivWithinAt_toFun (u : timeH1 X T) :
    ∀ᵐ t ∂(timeMeasure T), HasDerivWithinAt u.toFun (u.deriv t) (_root_.Set.Icc (0 : ℝ) T) t := by
  rcases le_or_gt 0 T with hT | hT
  · have h0 : (0 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have hac : timeMeasure T ≪ volume :=
      Measure.absolutelyContinuous_of_le (Measure.restrict_le_self)
    set v : ℝ → X := fun s => if s ∈ _root_.Set.Ioc (0 : ℝ) T then u.deriv s else 0 with hv_def
    have hvint : _root_.MeasureTheory.IntegrableOn v (_root_.Set.Ioc (0 : ℝ) T) volume := by
      have hcongr : _root_.MeasureTheory.IntegrableOn (fun s => u.deriv s) (_root_.Set.Ioc (0 : ℝ) T) volume :=
        (TimeSobolev.integrableOn u.deriv).mono_set _root_.Set.Ioc_subset_Icc_self
      refine hcongr.congr_fun ?_ measurableSet_Ioc
      intro s hs
      simp only [hv_def, if_pos hs]
    have hvloc : _root_.MeasureTheory.LocallyIntegrable v volume := by
      refine Integrable.locallyIntegrable ?_
      refine (_root_.MeasureTheory.integrableOn_iff_integrable_of_support_subset (s := _root_.Set.Ioc (0 : ℝ) T) ?_).1 hvint
      intro s hs
      by_contra hmem
      apply hs
      simp only [hv_def, if_neg hmem]
    have hLDT := locallyIntegrable_ae_hasDerivAt_integral hvloc
    have hLDT' : ∀ᵐ t ∂(timeMeasure T), ∀ c, HasDerivAt
        (fun x => ∫ r in c..x, v r) (v t) t := hac hLDT
    have hne0 : ∀ᵐ t ∂(timeMeasure T), t ≠ 0 :=
      hac (ae_iff.mpr (by simp))
    have hneT : ∀ᵐ t ∂(timeMeasure T), t ≠ T :=
      hac (ae_iff.mpr (by simp))
    have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ _root_.Set.Icc (0 : ℝ) T :=
      _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [hLDT', hne0, hneT, hmem] with t ht htne0 htneT htmem
    have htIoo : t ∈ _root_.Set.Ioo (0 : ℝ) T :=
      ⟨lt_of_le_of_ne htmem.1 (Ne.symm htne0), lt_of_le_of_ne htmem.2 htneT⟩
    have hae : ∀ s ∈ _root_.Set.Ioo (0 : ℝ) T,
        (∫ r in (0 : ℝ)..s, v r) = ∫ r in (0 : ℝ)..s, u.deriv r := by
      intro s hs
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with r hr
      rw [Set.uIoc, min_eq_left (le_of_lt hs.1), max_eq_right (le_of_lt hs.1)] at hr
      have hrIoc : r ∈ _root_.Set.Ioc (0 : ℝ) T :=
        ⟨hr.1, le_trans hr.2 (le_of_lt hs.2)⟩
      simp only [hv_def, if_pos hrIoc]
    have htIoc : t ∈ _root_.Set.Ioc (0 : ℝ) T := ⟨htIoo.1, le_of_lt htIoo.2⟩
    have hvt : v t = u.deriv t := by simp only [hv_def, if_pos htIoc]
    have hderiv_v : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, v r) (v t) t := ht 0
    have hderiv_u : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, u.deriv r)
        (u.deriv t) t := by
      have heq : (fun s => ∫ r in (0 : ℝ)..s, u.deriv r)
          =ᶠ[𝓝 t] fun s => ∫ r in (0 : ℝ)..s, v r := by
        filter_upwards [Ioo_mem_nhds htIoo.1 htIoo.2] with s hs using (hae s hs).symm
      exact hvt ▸ (hderiv_v.congr_of_eventuallyEq heq)
    exact (hderiv_u.const_add u.initial).hasDerivWithinAt
  · have hbot : _root_.MeasureTheory.ae (timeMeasure T) = ⊥ :=
      MeasureTheory.ae_eq_bot.mpr (timeMeasure_eq_zero_of_nonpos (le_of_lt hT))
    rw [Filter.eventually_iff, hbot]
    exact Filter.mem_bot

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.ae_hasDerivWithinAt_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.ae_hasDerivWithinAt_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.ae_hasDerivWithinAt_toFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.ae_hasDerivWithinAt_toFun

theorem chain_ae
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (u : timeH1 X T) (v : timeH1 Y T) {f : X → Y} {s : Set X}
    (A : ℝ → X →L[ℝ] Y)
    (hf : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      HasFDerivWithinAt f (A t) s (u.toFun t))
    (hu : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : ℝ) T) s)
    (hval : _root_.Set.EqOn v.toFun (f ∘ u.toFun) (_root_.Set.Icc (0 : ℝ) T)) :
    v.deriv =ᵐ[timeMeasure T]
      fun t ↦ A t (u.deriv t) := by
  have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ _root_.Set.Ioo (0 : ℝ) T := by
    unfold timeMeasure
    rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    exact _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo
  filter_upwards [u.ae_hasDerivWithinAt_toFun,
    v.ae_hasDerivWithinAt_toFun, hmem] with t hut hvt ht
  have htIcc : t ∈ _root_.Set.Icc (0 : ℝ) T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hIcc : _root_.Set.Icc (0 : ℝ) T ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hut' : HasDerivAt u.toFun (u.deriv t) t := hut.hasDerivAt hIcc
  have hvt' : HasDerivAt v.toFun (v.deriv t) t := hvt.hasDerivAt hIcc
  have hmaps : ∀ᶠ r in 𝓝 t, u.toFun r ∈ s := by
    filter_upwards [hIcc] with r hr
    exact hu hr
  have hcomp : HasDerivAt (f ∘ u.toFun) (A t (u.deriv t)) t :=
    (hf t htIcc).comp_hasDerivAt t hut' hmaps
  have heq : v.toFun =ᶠ[𝓝 t] f ∘ u.toFun := by
    filter_upwards [hIcc] with r hr
    exact hval hr
  exact hvt'.unique (hcomp.congr_of_eventuallyEq heq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.chain_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.chain_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.chain_ae ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.chain_ae

omit [CompleteSpace X] in
theorem norm_toFun_le (u : timeH1 X T) {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    ‖u.toFun t‖ ≤ ‖trace0 X T u‖ + Real.sqrt T * ‖timeDeriv X T u‖ := by
  rcases ht with ⟨ht0, htT⟩
  have hTnn : (0 : ℝ) ≤ T := le_trans ht0 htT
  have hint_eq : (∫ s in (0 : ℝ)..t, u.deriv s) = ∫ s in _root_.Set.Ioc (0 : ℝ) t, u.deriv s :=
    intervalIntegral.integral_of_le ht0
  have hnorm_int : ‖∫ s in (0 : ℝ)..t, u.deriv s‖ ≤ ∫ s in _root_.Set.Ioc (0 : ℝ) t, ‖u.deriv s‖ := by
    rw [hint_eq]
    exact _root_.MeasureTheory.norm_integral_le_integral_norm _
  have hmono : (∫ s in _root_.Set.Ioc (0 : ℝ) t, ‖u.deriv s‖) ≤ ∫ s in _root_.Set.Icc (0 : ℝ) T, ‖u.deriv s‖ := by
    have hintT : _root_.MeasureTheory.IntegrableOn (fun s => ‖u.deriv s‖) (_root_.Set.Icc (0 : ℝ) T) volume :=
      (TimeSobolev.integrableOn u.deriv).norm
    refine _root_.MeasureTheory.setIntegral_mono_set hintT ?_ ?_
    · filter_upwards with s using norm_nonneg _
    · refine LE.le.eventuallyLE ?_
      intro s hs
      exact ⟨le_of_lt hs.1, le_trans hs.2 htT⟩
  have hCS : (∫ s in _root_.Set.Icc (0 : ℝ) T, ‖u.deriv s‖) ≤ Real.sqrt T * ‖u.deriv‖ :=
    TimeSobolev.integral_norm_le u.deriv
  calc ‖u.toFun t‖ = ‖u.initial + ∫ s in (0 : ℝ)..t, u.deriv s‖ := rfl
    _ ≤ ‖u.initial‖ + ‖∫ s in (0 : ℝ)..t, u.deriv s‖ := norm_add_le _ _
    _ ≤ ‖u.initial‖ + ∫ s in _root_.Set.Ioc (0 : ℝ) t, ‖u.deriv s‖ := by gcongr
    _ ≤ ‖u.initial‖ + ∫ s in _root_.Set.Icc (0 : ℝ) T, ‖u.deriv s‖ := by gcongr
    _ ≤ ‖u.initial‖ + Real.sqrt T * ‖u.deriv‖ := by gcongr
    _ = ‖trace0 X T u‖ + Real.sqrt T * ‖timeDeriv X T u‖ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFun_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFun_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFun_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFun_le

omit [CompleteSpace X] in
theorem norm_toFun_le_norm (u : timeH1 X T) {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    ‖u.toFun t‖ ≤ (1 + Real.sqrt T) * ‖u‖ := by
  have hbase := u.norm_toFun_le ht
  have hinit : ‖trace0 X T u‖ ≤ ‖u‖ := by
    rw [trace0_apply]; exact u.norm_initial_le
  have hderiv : ‖timeDeriv X T u‖ ≤ ‖u‖ := by
    rw [timeDeriv_apply]; exact u.norm_deriv_le
  have hsqrt : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg T
  calc ‖u.toFun t‖ ≤ ‖trace0 X T u‖ + Real.sqrt T * ‖timeDeriv X T u‖ := hbase
    _ ≤ ‖u‖ + Real.sqrt T * ‖u‖ := by
        refine add_le_add hinit ?_
        exact mul_le_mul_of_nonneg_left hderiv hsqrt
    _ = (1 + Real.sqrt T) * ‖u‖ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFun_le_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFun_le_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFun_le_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFun_le_norm

def toFunL2 (u : timeH1 X T) : timeL2 X T :=
  TimeSobolev.ofContinuousOn u.continuousOn_toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFunL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFunL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFunL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFunL2

omit [CompleteSpace X] in
theorem norm_toFunL2_le (u : timeH1 X T) :
    ‖u.toFunL2‖ ≤ Real.sqrt T * ((1 + Real.sqrt T) * ‖u‖) := by
  rw [toFunL2]
  refine TimeSobolev.norm_ofContinuousOn_le_of_bound u.continuousOn_toFun ?_
  intro t ht
  exact u.norm_toFun_le_norm ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFunL2_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFunL2_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFunL2_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFunL2_le

omit [CompleteSpace X] in
theorem toFun_add (u w : timeH1 X T) {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    (u + w).toFun t = u.toFun t + w.toFun t := by
  have h0 : (0 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  have hsplit : ∫ s in (0 : ℝ)..t, ((u + w).deriv) s
      = (∫ s in (0 : ℝ)..t, u.deriv s) + ∫ s in (0 : ℝ)..t, w.deriv s := by
    have hcongr : ∫ s in (0 : ℝ)..t, ((u + w).deriv) s
        = ∫ s in (0 : ℝ)..t, (u.deriv s + w.deriv s) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hae : ⇑((u + w).deriv) =ᵐ[volume.restrict (_root_.Set.Icc (0 : ℝ) T)]
          (fun s => u.deriv s + w.deriv s) := by
        have hd : ((u + w).deriv : timeL2 X T) = u.deriv + w.deriv := deriv_add u w
        have := Lp.coeFn_add (u.deriv) (w.deriv)
        rw [hd]
        filter_upwards [this] with s hs using hs
      have hsub : Set.uIoc (0 : ℝ) t ⊆ _root_.Set.Icc (0 : ℝ) T := by
        intro r hr
        rw [Set.uIoc, min_eq_left ht.1, max_eq_right ht.1] at hr
        exact ⟨le_of_lt hr.1, le_trans hr.2 ht.2⟩
      exact _root_.MeasureTheory.ae_imp_of_ae_restrict
        (hae.filter_mono (_root_.MeasureTheory.ae_mono (Measure.restrict_mono hsub le_rfl)))
    rw [hcongr]
    exact intervalIntegral.integral_add
      (u.intervalIntegrable_deriv h0 ht) (w.intervalIntegrable_deriv h0 ht)
  simp only [toFun_apply, initial_add, hsplit]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_add

omit [CompleteSpace X] in
theorem toFun_smul (c : ℝ) (u : timeH1 X T) {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    (c • u).toFun t = c • u.toFun t := by
  have hsmul : ∫ s in (0 : ℝ)..t, ((c • u).deriv) s
      = c • ∫ s in (0 : ℝ)..t, u.deriv s := by
    have hcongr : ∫ s in (0 : ℝ)..t, ((c • u).deriv) s
        = ∫ s in (0 : ℝ)..t, (c • u.deriv s) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hae : ⇑((c • u).deriv) =ᵐ[volume.restrict (_root_.Set.Icc (0 : ℝ) T)]
          (fun s => c • u.deriv s) := by
        have hd : ((c • u).deriv : timeL2 X T) = c • u.deriv := deriv_smul c u
        have := Lp.coeFn_smul c (u.deriv)
        rw [hd]
        filter_upwards [this] with s hs using hs
      have hsub : Set.uIoc (0 : ℝ) t ⊆ _root_.Set.Icc (0 : ℝ) T := by
        intro r hr
        rw [Set.uIoc, min_eq_left ht.1, max_eq_right ht.1] at hr
        exact ⟨le_of_lt hr.1, le_trans hr.2 ht.2⟩
      exact _root_.MeasureTheory.ae_imp_of_ae_restrict
        (hae.filter_mono (_root_.MeasureTheory.ae_mono (Measure.restrict_mono hsub le_rfl)))
    rw [hcongr, intervalIntegral.integral_smul]
  simp only [toFun_apply, initial_smul, hsmul, smul_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toFun_smul

def toTimeL2ₗ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (T : ℝ) : timeH1 X T →ₗ[ℝ] timeL2 X T where
  toFun u := u.toFunL2
  map_add' u w := by
    refine Lp.ext ?_
    have huw : ⇑((u + w).toFunL2) =ᵐ[timeMeasure T] (u + w).toFun :=
      TimeSobolev.coeFn_ofContinuousOn (u + w).continuousOn_toFun
    have hu : ⇑(u.toFunL2) =ᵐ[timeMeasure T] u.toFun :=
      TimeSobolev.coeFn_ofContinuousOn u.continuousOn_toFun
    have hw : ⇑(w.toFunL2) =ᵐ[timeMeasure T] w.toFun :=
      TimeSobolev.coeFn_ofContinuousOn w.continuousOn_toFun
    have hadd := Lp.coeFn_add (u.toFunL2) (w.toFunL2)
    have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ _root_.Set.Icc (0 : ℝ) T :=
      _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [huw, hu, hw, hadd, hmem] with t htuw htu htw htadd htmem
    rw [htuw, htadd, Pi.add_apply, htu, htw, toFun_add u w htmem]
  map_smul' c u := by
    refine Lp.ext ?_
    have hcu : ⇑((c • u).toFunL2) =ᵐ[timeMeasure T] (c • u).toFun :=
      TimeSobolev.coeFn_ofContinuousOn (c • u).continuousOn_toFun
    have hu : ⇑(u.toFunL2) =ᵐ[timeMeasure T] u.toFun :=
      TimeSobolev.coeFn_ofContinuousOn u.continuousOn_toFun
    have hsmul := Lp.coeFn_smul c (u.toFunL2)
    have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ _root_.Set.Icc (0 : ℝ) T :=
      _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [hcu, hu, hsmul, hmem] with t htcu htu htsmul htmem
    rw [htcu, RingHom.id_apply, htsmul, Pi.smul_apply, htu, toFun_smul c u htmem]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toTimeL2ₗ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toTimeL2ₗ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toTimeL2ₗ ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toTimeL2ₗ

def toTimeL2 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [hComplete : CompleteSpace X] (T : ℝ) : timeH1 X T →L[ℝ] timeL2 X T :=
  LinearMap.mkContinuous (toTimeL2ₗ X T) (Real.sqrt T * (1 + Real.sqrt T)) (fun u => by
    let _ := hComplete
    have h := u.norm_toFunL2_le
    rwa [← mul_assoc] at h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toTimeL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toTimeL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toTimeL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toTimeL2

@[simp]
theorem toTimeL2_apply (u : timeH1 X T) : toTimeL2 X T u = u.toFunL2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toTimeL2_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toTimeL2_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toTimeL2_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.toTimeL2_apply

theorem norm_toTimeL2_le (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (T : ℝ) :
    ‖toTimeL2 X T‖ ≤ Real.sqrt T * (1 + Real.sqrt T) :=
  LinearMap.mkContinuous_norm_le _
    (mul_nonneg (Real.sqrt_nonneg T) (by positivity)) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toTimeL2_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toTimeL2_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toTimeL2_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toTimeL2_le

end Normed

omit [CompleteSpace X] in
theorem inner_def [InnerProductSpace ℝ X] (u w : timeH1 X T) :
    (_root_.Inner.inner ℝ u w : ℝ) = _root_.Inner.inner ℝ u.initial w.initial + _root_.Inner.inner ℝ u.deriv w.deriv :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.inner_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.inner_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.inner_def ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.inner_def

end timeH1

theorem exists_timeH1_of_scalar_representatives
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    {T : ℝ} {p q : ℝ → X} (hq : _root_.MeasureTheory.MemLp q 2 (timeMeasure T)) (p₀ : X)
    (hscalar : ∀ x : X, ∃ v : timeH1 ℝ T,
      v.initial = _root_.Inner.inner ℝ x p₀ ∧
      (fun t => _root_.Inner.inner ℝ x (p t)) =ᵐ[timeMeasure T] v.toFun ∧
      v.deriv =ᵐ[timeMeasure T] fun t => _root_.Inner.inner ℝ x (q t)) :
    ∃ w : timeH1 X T,
      w.initial = p₀ ∧ p =ᵐ[timeMeasure T] w.toFun ∧
        w.deriv =ᵐ[timeMeasure T] q := by
  let qL2 : timeL2 X T := hq.toLp q
  let w : timeH1 X T := timeH1.mk p₀ qL2
  have hqrep : qL2 =ᵐ[timeMeasure T] q := hq.coeFn_toLp
  let e : ℕ → X := TopologicalSpace.denseSeq X
  have he : DenseRange e := TopologicalSpace.denseRange_denseSeq X
  choose v hvinit hvrep hvderiv using fun i => hscalar (e i)
  have hvw (i : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
      (v i).toFun t = _root_.Inner.inner ℝ (e i) (w.toFun t) := by
    have hsub : _root_.Set.uIoc (0 : ℝ) t ⊆ _root_.Set.Icc (0 : ℝ) T := by
      intro r hr
      rw [_root_.Set.uIoc_of_le ht.1] at hr
      exact ⟨le_of_lt hr.1, hr.2.trans ht.2⟩
    have hvderiv' : (v i).deriv =ᵐ[volume.restrict (_root_.Set.uIoc (0 : ℝ) t)]
        fun r => _root_.Inner.inner ℝ (e i) (q r) := by
      have htime : (v i).deriv =ᵐ[volume.restrict (_root_.Set.Icc (0 : ℝ) T)]
          fun r => _root_.Inner.inner ℝ (e i) (q r) := by
        simpa only [timeMeasure] using hvderiv i
      exact htime.filter_mono (_root_.MeasureTheory.ae_mono (Measure.restrict_mono hsub le_rfl))
    have hqrep' : qL2 =ᵐ[volume.restrict (_root_.Set.uIoc (0 : ℝ) t)] q := by
      have htime : qL2 =ᵐ[volume.restrict (_root_.Set.Icc (0 : ℝ) T)] q := by
        simpa only [timeMeasure] using hqrep
      exact htime.filter_mono (_root_.MeasureTheory.ae_mono (Measure.restrict_mono hsub le_rfl))
    have hvint : (∫ r in (0 : ℝ)..t, (v i).deriv r) =
        ∫ r in (0 : ℝ)..t, _root_.Inner.inner ℝ (e i) (q r) :=
      intervalIntegral.integral_congr_ae (_root_.MeasureTheory.ae_imp_of_ae_restrict hvderiv')
    have hqint :
        (∫ r in (0 : ℝ)..t, _root_.Inner.inner ℝ (e i) (qL2 r)) =
          ∫ r in (0 : ℝ)..t, _root_.Inner.inner ℝ (e i) (q r) :=
      intervalIntegral.integral_congr_ae <|
        (_root_.MeasureTheory.ae_imp_of_ae_restrict hqrep').mono fun r hr hrmem => by rw [hr hrmem]
    have hqii : IntervalIntegrable (fun r => qL2 r) _root_.MeasureTheory.MeasureSpace.volume 0 t := by
      apply MeasureTheory.IntegrableOn.intervalIntegrable
      exact (TimeSobolev.integrableOn qL2).mono_set
        (_root_.Set.uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht)
    have hmap := (innerSL ℝ (e i)).intervalIntegral_comp_comm hqii
    change (∫ r in (0 : ℝ)..t, _root_.Inner.inner ℝ (e i) (qL2 r)) =
      _root_.Inner.inner ℝ (e i) (∫ r in (0 : ℝ)..t, qL2 r) at hmap
    rw [timeH1.toFun_apply, timeH1.toFun_apply, hvinit i, hvint]
    change _root_.Inner.inner ℝ (e i) p₀ + _ =
      _root_.Inner.inner ℝ (e i) (p₀ + ∫ r in (0 : ℝ)..t, qL2 r)
    rw [inner_add_right, ← hmap, hqint]
  have hpair : ∀ᵐ t ∂(timeMeasure T), ∀ i,
      inner ℝ (e i) (p t) = _root_.Inner.inner ℝ (e i) (w.toFun t) := by
    rw [_root_.MeasureTheory.ae_all_iff]
    intro i
    filter_upwards [hvrep i, _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht htIcc
    exact ht.trans (hvw i t htIcc)
  refine ⟨w, rfl, ?_, ?_⟩
  · filter_upwards [hpair] with t ht
    exact he.eq_of_inner_right ℝ ht
  · simpa only [w, timeH1.deriv_mk] using hqrep

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_timeH1_of_scalar_representatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_timeH1_of_scalar_representatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_timeH1_of_scalar_representatives ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_timeH1_of_scalar_representatives

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
