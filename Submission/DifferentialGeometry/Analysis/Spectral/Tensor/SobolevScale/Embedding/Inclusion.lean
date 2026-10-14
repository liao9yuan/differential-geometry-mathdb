import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSobolevWeight_mono {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) {τ σ : ℝ} (hτσ : τ ≤ σ) :
    tensorSobolevWeight (I := I) (M := M) i τ ≤
      tensorSobolevWeight (I := I) (M := M) i σ := by
  unfold tensorSobolevWeight
  exact Real.rpow_le_rpow_of_exponent_le
    (one_le_one_add_lambda (I := I) (M := M) i) hτσ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_mono ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_mono

namespace TensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [NeZero (Module.finrank ℝ E)] in
lemma weighted_summable_of_le {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le ?_ ?_ T.weighted_summable
  · intro i
    have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i τ :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i τ
    positivity
  · intro i
    have hmono : tensorSobolevWeight (I := I) (M := M) i τ ≤
        tensorSobolevWeight (I := I) (M := M) i σ :=
      tensorSobolevWeight_mono (I := I) (M := M) i hτσ
    exact mul_le_mul_of_nonneg_right hmono (sq_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.weighted_summable_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.weighted_summable_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.weighted_summable_of_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.weighted_summable_of_le

def inclusionFun {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    TensorHs (I := I) (M := M) g r s τ where
  coeff := T.coeff
  weighted_summable := weighted_summable_of_le (I := I) (M := M) hτσ T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma inclusionFun_coeff {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    (inclusionFun (I := I) (M := M) hτσ T).coeff = T.coeff := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun_coeff

omit [NeZero (Module.finrank ℝ E)] in
lemma inclusionFun_add {τ σ : ℝ} (hτσ : τ ≤ σ)
    (S T : TensorHs (I := I) (M := M) g r s σ) :
    inclusionFun (I := I) (M := M) hτσ (S + T) =
      inclusionFun (I := I) (M := M) hτσ S +
        inclusionFun (I := I) (M := M) hτσ T := by
  ext i
  simp only [inclusionFun_coeff, add_coeff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun_add

omit [NeZero (Module.finrank ℝ E)] in
lemma inclusionFun_smul {τ σ : ℝ} (hτσ : τ ≤ σ) (c : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    inclusionFun (I := I) (M := M) hτσ (c • T) =
      c • inclusionFun (I := I) (M := M) hτσ T := by
  ext i
  simp only [inclusionFun_coeff, smul_coeff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.inclusionFun_smul

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_inclusionFun_le {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    ‖inclusionFun (I := I) (M := M) hτσ T‖ ≤ ‖T‖ := by
  have h_t_sq : ‖inclusionFun (I := I) (M := M) hτσ T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (inclusionFun (I := I) (M := M) hτσ T)
    rwa [inclusionFun_coeff] at h
  have h_s_sq : ‖T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_le_terms : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
    intro i
    exact mul_le_mul_of_nonneg_right
      (tensorSobolevWeight_mono (I := I) (M := M) i hτσ) (sq_nonneg _)
  have h_tsum_le :
      ∑' i, tensorSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2 ≤
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2 :=
    Summable.tsum_le_tsum h_le_terms
      (weighted_summable_of_le (I := I) (M := M) hτσ T) T.weighted_summable
  have h_sq_le : ‖inclusionFun (I := I) (M := M) hτσ T‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [h_t_sq, h_s_sq]; exact h_tsum_le
  have h1 : 0 ≤ ‖inclusionFun (I := I) (M := M) hτσ T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  nlinarith [h_sq_le, h1, h2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_inclusionFun_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_inclusionFun_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_inclusionFun_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_inclusionFun_le

end TensorHs

def tensorHsInclusion {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {τ σ : ℝ} (hτσ : τ ≤ σ) :
    TensorHs (I := I) (M := M) g r s σ →L[ℝ]
      TensorHs (I := I) (M := M) g r s τ :=
  LinearMap.mkContinuous
    { toFun := TensorHs.inclusionFun (I := I) (M := M) hτσ
      map_add' := TensorHs.inclusionFun_add (I := I) (M := M) hτσ
      map_smul' := fun c T =>
        TensorHs.inclusionFun_smul (I := I) (M := M) hτσ c T }
    1
    (fun T => by
      change ‖TensorHs.inclusionFun (I := I) (M := M) hτσ T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact TensorHs.norm_inclusionFun_le (I := I) (M := M) hτσ T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorHsInclusion_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ T =
      TensorHs.inclusionFun (I := I) (M := M) hτσ T := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_apply

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsInclusion_coeff {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ T).coeff =
      T.coeff := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_coeff

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsInclusion_coeff_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {τ σ : ℝ}
    (hτσ : τ ≤ σ) (T : TensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ T).coeff i =
      T.coeff i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_coeff_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_coeff_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_coeff_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_coeff_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {τ σ : ℝ} (hτσ : τ ≤ σ) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_opNorm_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_opNorm_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_opNorm_le_one ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_opNorm_le_one

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_norm_le {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ T‖ ≤ ‖T‖ :=
  TensorHs.norm_inclusionFun_le (I := I) (M := M) hτσ T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_norm_le

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_injective {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {τ σ : ℝ} (hτσ : τ ≤ σ) :
    Function.Injective
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ) := by
  intro S T hST
  ext i
  have h := congrArg (fun U => TensorHs.coeff U i) hST
  simpa only [tensorHsInclusion_coeff] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_injective ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_injective

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsInclusion_refl {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ} :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) (le_refl σ) =
      ContinuousLinearMap.id ℝ
        (TensorHs (I := I) (M := M) g r s σ) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  refine TensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, ContinuousLinearMap.id_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_refl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_refl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_refl_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ}
    (T : TensorHs (I := I) (M := M) g r s σ) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) (le_refl σ) T = T := by
  ext i
  simp only [tensorHsInclusion_coeff_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_refl_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_refl_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_refl_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_refl_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_trans {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {ρ τ σ : ℝ} (hρτ : ρ ≤ τ) (hτσ : τ ≤ σ) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) (hρτ.trans hτσ) =
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hρτ).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ) := by
  ext T i
  simp only [tensorHsInclusion_coeff_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_trans ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_trans

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_trans_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {ρ τ σ : ℝ} (hρτ : ρ ≤ τ) (hτσ : τ ≤ σ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) (hρτ.trans hτσ) T =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hρτ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ T) := by
  ext i
  simp only [tensorHsInclusion_coeff_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_trans_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_trans_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_trans_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_trans_apply

namespace TensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ}

def finiteSupportSubmodule (σ : ℝ) :
    Submodule ℝ (TensorHs (I := I) (M := M) g r s σ) where
  carrier := {T | (Function.support T.coeff).Finite}
  add_mem' := by
    intro S T hS hT
    refine Set.Finite.subset (hS.union hT) ?_
    intro i hi
    simp only [Function.mem_support, add_coeff, ne_eq] at hi
    by_contra hcon
    simp only [Set.mem_union, Function.mem_support, ne_eq, not_or,
      _root_.Classical.not_not] at hcon
    exact hi (by rw [hcon.1, hcon.2, add_zero])
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, zero_coeff]
    refine Set.finite_empty.subset ?_
    intro i hi
    simp only [Function.mem_support, ne_eq, not_true_eq_false] at hi
  smul_mem' := by
    intro c T hT
    refine Set.Finite.subset hT ?_
    intro i hi
    simp only [Function.mem_support, smul_coeff, ne_eq] at hi
    simp only [Function.mem_support, ne_eq]
    intro hcon
    exact hi (by rw [hcon, _root_.MulZeroClass.mul_zero])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.finiteSupportSubmodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.finiteSupportSubmodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.finiteSupportSubmodule ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.finiteSupportSubmodule

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma mem_finiteSupportSubmodule {σ : ℝ}
    (T : TensorHs (I := I) (M := M) g r s σ) :
    T ∈ finiteSupportSubmodule (I := I) (M := M) (g := g) (r := r) (s := s) σ ↔
      (Function.support T.coeff).Finite := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.mem_finiteSupportSubmodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.mem_finiteSupportSubmodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.mem_finiteSupportSubmodule ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.mem_finiteSupportSubmodule

end TensorHs

namespace TensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ}

open scoped _root_.Classical in
omit [NeZero (Module.finrank ℝ E)] in
lemma rescaleEquivL2_smul_basisVec
    (T : TensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    rescaleEquivL2 (I := I) (M := M) (σ := σ)
        (T.coeff i • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i) =
      lp.single 2 i
        (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
          T.coeff i) := by
  classical
  apply lp.ext
  funext j
  rw [rescaleEquivL2_apply, lp.single_apply]
  simp only [smul_coeff, tensorHsBasisVec_coeff]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.rescaleEquivL2_smul_basisVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.rescaleEquivL2_smul_basisVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.rescaleEquivL2_smul_basisVec ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.rescaleEquivL2_smul_basisVec

omit [NeZero (Module.finrank ℝ E)] in
theorem hasSum_smul_basisVec
    (T : TensorHs (I := I) (M := M) g r s σ) :
    HasSum (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      T.coeff i • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i) T := by
  classical
  rw [← ContinuousLinearEquiv.hasSum'
    (e := (rescaleEquivL2 (I := I) (M := M)
      (σ := σ)).toContinuousLinearEquiv)]
  have h_l2 : HasSum
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        lp.single 2 i
          (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
            T.coeff i))
      (rescaleEquivL2 (I := I) (M := M)
        (σ := σ) T) := by
    have h := lp.hasSum_single (α := TensorEigenIdx (I := I) (M := M) g r s)
      (E := fun _ => ℝ) (p := 2) (by norm_num)
      (rescaleEquivL2 (I := I) (M := M)
        (σ := σ) T)
    refine h.congr_fun (fun i => ?_)
    rw [rescaleEquivL2_apply]
  refine h_l2.congr_fun (fun i => ?_)
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    rescaleEquivL2_smul_basisVec]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.hasSum_smul_basisVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.hasSum_smul_basisVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.hasSum_smul_basisVec ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.hasSum_smul_basisVec

omit [NeZero (Module.finrank ℝ E)] in
theorem mem_closure_finiteSupportSubmodule
    (T : TensorHs (I := I) (M := M) g r s σ) :
    T ∈ closure
      (finiteSupportSubmodule (I := I) (M := M) (g := g) (r := r) (s := s) σ :
        Set (TensorHs (I := I) (M := M) g r s σ)) := by
  classical
  refine mem_closure_of_tendsto
    (hasSum_smul_basisVec (I := I) (M := M) T) ?_
  refine Filter.Eventually.of_forall (fun u => ?_)
  refine Submodule.sum_mem _ (fun i _ => ?_)
  refine Submodule.smul_mem _ _ ?_
  rw [mem_finiteSupportSubmodule]
  refine Set.Finite.subset (Set.finite_singleton i) ?_
  intro j hj
  simp only [Function.mem_support, tensorHsBasisVec_coeff, ne_eq,
    ite_eq_right_iff, one_ne_zero, imp_false, _root_.Classical.not_not] at hj
  simpa using hj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.mem_closure_finiteSupportSubmodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.mem_closure_finiteSupportSubmodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.mem_closure_finiteSupportSubmodule ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.mem_closure_finiteSupportSubmodule

end TensorHs

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsFiniteSupportSubmodule_topologicalClosure
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ} :
    (TensorHs.finiteSupportSubmodule (I := I) (M := M) (g := g) (r := r) (s := s)
        σ).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro T _
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact TensorHs.mem_closure_finiteSupportSubmodule (I := I) (M := M) T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsFiniteSupportSubmodule_topologicalClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsFiniteSupportSubmodule_topologicalClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsFiniteSupportSubmodule_topologicalClosure ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsFiniteSupportSubmodule_topologicalClosure

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsFiniteSupportSubmodule_dense
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ} :
    Dense (TensorHs.finiteSupportSubmodule (I := I) (M := M) (g := g) (r := r) (s := s)
      σ :
      Set (TensorHs (I := I) (M := M) g r s σ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact tensorHsFiniteSupportSubmodule_topologicalClosure
    (I := I) (M := M) (g := g) (r := r) (s := s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsFiniteSupportSubmodule_dense then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsFiniteSupportSubmodule_dense"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsFiniteSupportSubmodule_dense ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsFiniteSupportSubmodule_dense

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHs_dense_finiteSupport {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ} :
    Dense {T : TensorHs (I := I) (M := M) g r s σ |
      (Function.support T.coeff).Finite} :=
  tensorHsFiniteSupportSubmodule_dense (I := I) (M := M) (g := g) (r := r) (s := s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs_dense_finiteSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs_dense_finiteSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs_dense_finiteSupport ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs_dense_finiteSupport

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsBasisVec_span_dense {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ} :
    Dense (Submodule.span ℝ
      (Set.range (tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ)) :
      Set (TensorHs (I := I) (M := M) g r s σ)) := by
  classical
  refine tensorHsFiniteSupportSubmodule_dense (I := I) (M := M) (g := g) (r := r) (s := s)
    |>.mono ?_
  intro T hT
  rw [SetLike.mem_coe, TensorHs.mem_finiteSupportSubmodule] at hT
  classical
  have h_eq : T = ∑ i ∈ hT.toFinset,
      T.coeff i • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i := by
    refine TensorHs.ext ?_
    funext j
    have h_sum : (∑ i ∈ hT.toFinset,
          T.coeff i • tensorHsBasisVec (I := I) (M := M) σ i).coeff j =
        ∑ i ∈ hT.toFinset,
          (if j = i then T.coeff i else 0) := by
      induction hT.toFinset using Finset.induction with
      | empty => simp
      | insert a t ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih,
            TensorHs.add_coeff]
          simp only [TensorHs.smul_coeff, tensorHsBasisVec_coeff,
            mul_ite, mul_one, _root_.MulZeroClass.mul_zero]
    rw [h_sum]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Ne.symm hij]
    · intro hj
      have hzero : T.coeff j = 0 := by
        by_contra hne
        exact hj (hT.mem_toFinset.mpr (Function.mem_support.mpr hne))
      simp [hzero]
  rw [h_eq]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsBasisVec_span_dense then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsBasisVec_span_dense"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsBasisVec_span_dense ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsBasisVec_span_dense

def tensorHsHilbertBasis {g : SmoothRiemannianMetric I M} {r s : ℕ} (σ : ℝ) :
    HilbertBasis (TensorEigenIdx (I := I) (M := M) g r s) ℝ
      (TensorHs (I := I) (M := M) g r s σ) :=
  HilbertBasis.ofRepr
    (TensorHs.rescaleEquivL2 (I := I) (M := M)
      (g := g) (r := r) (s := s) (σ := σ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsHilbertBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsHilbertBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsHilbertBasis ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsHilbertBasis

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsHilbertBasis_repr_apply_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (σ : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ((tensorHsHilbertBasis (I := I) (M := M)
        (g := g) (r := r) (s := s) σ).repr T : _ → ℝ) i =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * T.coeff i :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsHilbertBasis_repr_apply_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsHilbertBasis_repr_apply_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsHilbertBasis_repr_apply_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsHilbertBasis_repr_apply_apply

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
