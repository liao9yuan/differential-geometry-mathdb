import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Inclusion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

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

namespace TensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

def cast {σ τ : ℝ} (h : σ = τ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    TensorHs (I := I) (M := M) g r s τ where
  coeff := T.coeff
  weighted_summable := by
    subst h; exact T.weighted_summable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma cast_coeff {σ τ : ℝ} (h : σ = τ)
    (T : TensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (cast (I := I) (M := M) h T).coeff i = T.coeff i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_coeff

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma cast_coeff_fun {σ τ : ℝ} (h : σ = τ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    (cast (I := I) (M := M) h T).coeff = T.coeff := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_coeff_fun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_coeff_fun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_coeff_fun ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_coeff_fun

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma cast_rfl {σ : ℝ}
    (T : TensorHs (I := I) (M := M) g r s σ) :
    cast (I := I) (M := M) (rfl : σ = σ) T = T := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_rfl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_rfl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_rfl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma cast_add {σ τ : ℝ} (h : σ = τ)
    (S T : TensorHs (I := I) (M := M) g r s σ) :
    cast (I := I) (M := M) h (S + T) =
      cast (I := I) (M := M) h S + cast (I := I) (M := M) h T := by
  ext i
  simp only [cast_coeff, add_coeff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_add

omit [NeZero (Module.finrank ℝ E)] in
lemma cast_smul {σ τ : ℝ} (h : σ = τ) (c : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    cast (I := I) (M := M) h (c • T) =
      c • cast (I := I) (M := M) h T := by
  ext i
  simp only [cast_coeff, smul_coeff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.cast_smul

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_cast {σ τ : ℝ} (h : σ = τ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    ‖cast (I := I) (M := M) h T‖ = ‖T‖ := by
  subst h; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_cast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_cast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_cast ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_cast

def castEquiv {σ τ : ℝ} (h : σ = τ) :
    TensorHs (I := I) (M := M) g r s σ ≃ₗᵢ[ℝ]
      TensorHs (I := I) (M := M) g r s τ where
  toFun := cast (I := I) (M := M) h
  invFun := cast (I := I) (M := M) h.symm
  map_add' := cast_add (I := I) (M := M) h
  map_smul' := cast_smul (I := I) (M := M) h
  left_inv T := by ext i; simp only [cast_coeff]
  right_inv T := by ext i; simp only [cast_coeff]
  norm_map' := norm_cast (I := I) (M := M) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.castEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.castEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.castEquiv ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.castEquiv

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma castEquiv_coeff {σ τ : ℝ} (h : σ = τ)
    (T : TensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (castEquiv (I := I) (M := M) h T).coeff i = T.coeff i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.castEquiv_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.castEquiv_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.castEquiv_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.castEquiv_coeff

end TensorHs

namespace TensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSobolevWeight_add (i : TensorEigenIdx (I := I) (M := M) g r s)
    (σ τ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (σ + τ) =
      tensorSobolevWeight (I := I) (M := M) i σ *
        tensorSobolevWeight (I := I) (M := M) i τ := by
  unfold tensorSobolevWeight
  exact Real.rpow_add
    (lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)) σ τ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tensorSobolevWeight_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tensorSobolevWeight_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tensorSobolevWeight_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tensorSobolevWeight_add

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSobolevWeight_neg (i : TensorEigenIdx (I := I) (M := M) g r s)
    (σ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (-σ) =
      (tensorSobolevWeight (I := I) (M := M) i σ)⁻¹ := by
  unfold tensorSobolevWeight
  exact Real.rpow_neg
    (le_trans zero_le_one (one_le_one_add_lambda (I := I) (M := M) i)) σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tensorSobolevWeight_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tensorSobolevWeight_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tensorSobolevWeight_neg ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tensorSobolevWeight_neg

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSobolevWeight_sub (i : TensorEigenIdx (I := I) (M := M) g r s)
    (σ τ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (σ - τ) =
      tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorSobolevWeight (I := I) (M := M) i τ)⁻¹ := by
  rw [sub_eq_add_neg, tensorSobolevWeight_add (I := I) (M := M),
    tensorSobolevWeight_neg (I := I) (M := M)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tensorSobolevWeight_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tensorSobolevWeight_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tensorSobolevWeight_sub ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.tensorSobolevWeight_sub

end TensorHs

namespace TensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [NeZero (Module.finrank ℝ E)] in
lemma fractionalPower_weight_term (i : TensorEigenIdx (I := I) (M := M) g r s)
    (θ σ : ℝ) (c : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
        (tensorSobolevWeight (I := I) (M := M) i θ * c) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i σ * c ^ 2 := by
  have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i θ :=
    tensorSobolevWeight_pos (I := I) (M := M) i θ
  have hsum : (σ - 2 * θ) + (θ + θ) = σ := by ring
  calc
    tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
          (tensorSobolevWeight (I := I) (M := M) i θ * c) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
            (tensorSobolevWeight (I := I) (M := M) i θ *
              tensorSobolevWeight (I := I) (M := M) i θ) * c ^ 2 := by
          ring
    _ = tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
            tensorSobolevWeight (I := I) (M := M) i (θ + θ) * c ^ 2 := by
          rw [tensorSobolevWeight_add (I := I) (M := M) i θ θ]
    _ = tensorSobolevWeight (I := I) (M := M) i
            ((σ - 2 * θ) + (θ + θ)) * c ^ 2 := by
          rw [tensorSobolevWeight_add (I := I) (M := M) i (σ - 2 * θ)
            (θ + θ)]
    _ = tensorSobolevWeight (I := I) (M := M) i σ * c ^ 2 := by
          rw [hsum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPower_weight_term then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPower_weight_term"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPower_weight_term ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPower_weight_term

omit [NeZero (Module.finrank ℝ E)] in
lemma fractionalPower_weighted_summable {σ : ℝ} (θ : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
        (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i) ^ 2) := by
  have h_eq :
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
          (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i) ^ 2) =
      (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2) := by
    funext i
    exact fractionalPower_weight_term (I := I) (M := M) i θ σ (T.coeff i)
  rw [h_eq]
  exact T.weighted_summable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPower_weighted_summable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPower_weighted_summable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPower_weighted_summable ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPower_weighted_summable

def fractionalPowerFun {σ : ℝ} (θ : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    TensorHs (I := I) (M := M) g r s (σ - 2 * θ) where
  coeff i := tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i
  weighted_summable := fractionalPower_weighted_summable (I := I) (M := M) θ T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma fractionalPowerFun_coeff {σ : ℝ} (θ : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (fractionalPowerFun (I := I) (M := M) θ T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun_coeff

omit [NeZero (Module.finrank ℝ E)] in
lemma fractionalPowerFun_add {σ : ℝ} (θ : ℝ)
    (S T : TensorHs (I := I) (M := M) g r s σ) :
    fractionalPowerFun (I := I) (M := M) θ (S + T) =
      fractionalPowerFun (I := I) (M := M) θ S +
        fractionalPowerFun (I := I) (M := M) θ T := by
  ext i
  simp only [fractionalPowerFun_coeff, add_coeff]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun_add

omit [NeZero (Module.finrank ℝ E)] in
lemma fractionalPowerFun_smul {σ : ℝ} (θ : ℝ) (c : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    fractionalPowerFun (I := I) (M := M) θ (c • T) =
      c • fractionalPowerFun (I := I) (M := M) θ T := by
  ext i
  simp only [fractionalPowerFun_coeff, smul_coeff]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.fractionalPowerFun_smul

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_fractionalPowerFun {σ : ℝ} (θ : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    ‖fractionalPowerFun (I := I) (M := M) θ T‖ = ‖T‖ := by
  have h_target_sq : ‖fractionalPowerFun (I := I) (M := M) θ T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
        (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (fractionalPowerFun (I := I) (M := M) θ T)
    simpa only [fractionalPowerFun_coeff] using h
  have h_source_sq : ‖T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_terms : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
          (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 :=
    fun i => fractionalPower_weight_term (I := I) (M := M) i θ σ (T.coeff i)
  have h_sq_eq : ‖fractionalPowerFun (I := I) (M := M) θ T‖ ^ 2 =
      ‖T‖ ^ 2 := by
    rw [h_target_sq, h_source_sq]
    exact tsum_congr h_terms
  have h1 : 0 ≤ ‖fractionalPowerFun (I := I) (M := M) θ T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  have := congrArg Real.sqrt h_sq_eq
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_fractionalPowerFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_fractionalPowerFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_fractionalPowerFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_fractionalPowerFun

end TensorHs

def tensorFractionalPower {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (θ : ℝ) {σ : ℝ} :
    TensorHs (I := I) (M := M) g r s σ →L[ℝ]
      TensorHs (I := I) (M := M) g r s (σ - 2 * θ) :=
  LinearMap.mkContinuous
    { toFun := TensorHs.fractionalPowerFun (I := I) (M := M) θ
      map_add' := TensorHs.fractionalPowerFun_add (I := I) (M := M) θ
      map_smul' := fun c T =>
        TensorHs.fractionalPowerFun_smul (I := I) (M := M) θ c T }
    1
    (fun T => by
      change ‖TensorHs.fractionalPowerFun (I := I) (M := M) θ T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact le_of_eq (TensorHs.norm_fractionalPowerFun (I := I) (M := M) θ T))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorFractionalPower_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (θ : ℝ) (T : TensorHs (I := I) (M := M) g r s σ) :
    tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ T =
      TensorHs.fractionalPowerFun (I := I) (M := M) θ T := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_apply

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorFractionalPower_coeff {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (θ : ℝ) (T : TensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_coeff

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (θ : ℝ) :
    ‖tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) θ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_opNorm_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_opNorm_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_opNorm_le_one ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_opNorm_le_one

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_norm {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (θ : ℝ) (T : TensorHs (I := I) (M := M) g r s σ) :
    ‖tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ T‖ = ‖T‖ :=
  TensorHs.norm_fractionalPowerFun (I := I) (M := M) θ T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_norm

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_inner {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (θ : ℝ) (S T : TensorHs (I := I) (M := M) g r s σ) :
    (_root_.Inner.inner ℝ (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ S)
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ T) : ℝ) =
      inner ℝ S T := by
  rw [TensorHs.inner_def, TensorHs.inner_def]
  refine tsum_congr (fun i => ?_)
  simp only [tensorFractionalPower_coeff]
  have hsum : (σ - 2 * θ) + (θ + θ) = σ := by ring
  calc
    tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
          (tensorSobolevWeight (I := I) (M := M) i θ * S.coeff i *
            (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i))
        = tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
            (tensorSobolevWeight (I := I) (M := M) i θ *
              tensorSobolevWeight (I := I) (M := M) i θ) *
            (S.coeff i * T.coeff i) := by ring
    _ = tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
            tensorSobolevWeight (I := I) (M := M) i (θ + θ) *
            (S.coeff i * T.coeff i) := by
          rw [← TensorHs.tensorSobolevWeight_add (I := I) (M := M) i θ θ]
    _ = tensorSobolevWeight (I := I) (M := M) i
            ((σ - 2 * θ) + (θ + θ)) * (S.coeff i * T.coeff i) := by
          rw [← TensorHs.tensorSobolevWeight_add (I := I) (M := M)
            i (σ - 2 * θ) (θ + θ)]
    _ = tensorSobolevWeight (I := I) (M := M) i σ *
          (S.coeff i * T.coeff i) := by rw [hsum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_inner ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_inner

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_zero_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ}
    (T : TensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (0 : ℝ) T).coeff i =
      T.coeff i := by
  rw [tensorFractionalPower_coeff, tensorSobolevWeight_zero, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_zero_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_zero_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_zero_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_zero_coeff

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_zero
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ}
    (T : TensorHs (I := I) (M := M) g r s σ) :
    tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (0 : ℝ) T =
      TensorHs.cast (I := I) (M := M)
        (by ring : σ = σ - 2 * 0) T := by
  refine TensorHs.ext ?_
  funext i
  rw [tensorFractionalPower_zero_coeff, TensorHs.cast_coeff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_add_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (θ φ : ℝ) (T : TensorHs (I := I) (M := M) g r s σ) :
    tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) φ T) =
      (TensorHs.cast (I := I) (M := M)
        (by ring :
          σ - 2 * (θ + φ) = (σ - 2 * φ) - 2 * θ))
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (θ + φ) T) := by
  refine TensorHs.ext ?_
  funext i
  rw [tensorFractionalPower_coeff, tensorFractionalPower_coeff,
    TensorHs.cast_coeff, tensorFractionalPower_coeff,
    TensorHs.tensorSobolevWeight_add (I := I) (M := M) i θ φ]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_add_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_add_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_add_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_add_apply

def tensorFractionalPowerEquiv {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (θ σ : ℝ) :
    TensorHs (I := I) (M := M) g r s σ ≃ₗᵢ[ℝ]
      TensorHs (I := I) (M := M) g r s (σ - 2 * θ) where
  toFun := TensorHs.fractionalPowerFun (I := I) (M := M) θ
  invFun T :=
    TensorHs.cast (I := I) (M := M)
      (by ring : σ - 2 * θ - 2 * (-θ) = σ)
      (TensorHs.fractionalPowerFun (I := I) (M := M) (-θ) T)
  map_add' := TensorHs.fractionalPowerFun_add (I := I) (M := M) θ
  map_smul' := fun c T =>
    TensorHs.fractionalPowerFun_smul (I := I) (M := M) θ c T
  left_inv T := by
    refine TensorHs.ext ?_
    funext i
    simp only [TensorHs.cast_coeff, TensorHs.fractionalPowerFun_coeff,
      TensorHs.tensorSobolevWeight_neg (I := I) (M := M) i θ]
    have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i θ :=
      tensorSobolevWeight_pos (I := I) (M := M) i θ
    rw [← mul_assoc, inv_mul_cancel₀ hw_pos.ne', one_mul]
  right_inv T := by
    refine TensorHs.ext ?_
    funext i
    simp only [TensorHs.fractionalPowerFun_coeff, TensorHs.cast_coeff,
      TensorHs.tensorSobolevWeight_neg (I := I) (M := M) i θ]
    have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i θ :=
      tensorSobolevWeight_pos (I := I) (M := M) i θ
    rw [← mul_assoc, mul_inv_cancel₀ hw_pos.ne', one_mul]
  norm_map' T := TensorHs.norm_fractionalPowerFun (I := I) (M := M) θ T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorFractionalPowerEquiv_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (θ σ : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s) θ σ T =
      tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ T := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_apply

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorFractionalPowerEquiv_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (θ σ : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s) θ σ T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_coeff

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPowerEquiv_toContinuousLinearMap
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (θ σ : ℝ) :
    (tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s)
        θ σ).toContinuousLinearEquiv.toContinuousLinearMap =
      tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) θ := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_toContinuousLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_toContinuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_toContinuousLinearMap ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_toContinuousLinearMap

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPowerEquiv_symm {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    (θ σ : ℝ) (T : TensorHs (I := I) (M := M) g r s (σ - 2 * θ)) :
    (tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s) θ σ).symm T =
      TensorHs.cast (I := I) (M := M)
        (by ring : σ - 2 * θ - 2 * (-θ) = σ)
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (-θ) T) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_symm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_symm

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPowerEquiv_norm {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    (θ σ : ℝ) (T : TensorHs (I := I) (M := M) g r s σ) :
    ‖tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s) θ σ T‖ = ‖T‖ :=
  TensorHs.norm_fractionalPowerFun (I := I) (M := M) θ T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPowerEquiv_norm

namespace TensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [NeZero (Module.finrank ℝ E)] in
lemma lambdaPower_weighted_summable {σ : ℝ} (sh : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (σ - sh) *
        (tensorSobolevWeight (I := I) (M := M) i (sh / 2) *
          T.coeff i) ^ 2) := by
  have h := fractionalPower_weighted_summable (I := I) (M := M)
    (σ := σ) (sh / 2) T
  have heq : σ - 2 * (sh / 2) = σ - sh := by ring
  rwa [heq] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPower_weighted_summable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPower_weighted_summable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPower_weighted_summable ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPower_weighted_summable

def lambdaPowerFun {σ : ℝ} (sh : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    TensorHs (I := I) (M := M) g r s (σ - sh) where
  coeff i := tensorSobolevWeight (I := I) (M := M) i (sh / 2) * T.coeff i
  weighted_summable := lambdaPower_weighted_summable (I := I) (M := M) sh T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma lambdaPowerFun_coeff {σ : ℝ} (sh : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (lambdaPowerFun (I := I) (M := M) sh T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i (sh / 2) * T.coeff i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun_coeff

omit [NeZero (Module.finrank ℝ E)] in
lemma lambdaPowerFun_add {σ : ℝ} (sh : ℝ)
    (S T : TensorHs (I := I) (M := M) g r s σ) :
    lambdaPowerFun (I := I) (M := M) sh (S + T) =
      lambdaPowerFun (I := I) (M := M) sh S +
        lambdaPowerFun (I := I) (M := M) sh T := by
  ext i
  simp only [lambdaPowerFun_coeff, add_coeff]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun_add

omit [NeZero (Module.finrank ℝ E)] in
lemma lambdaPowerFun_smul {σ : ℝ} (sh : ℝ) (c : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    lambdaPowerFun (I := I) (M := M) sh (c • T) =
      c • lambdaPowerFun (I := I) (M := M) sh T := by
  ext i
  simp only [lambdaPowerFun_coeff, smul_coeff]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.lambdaPowerFun_smul

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_lambdaPowerFun {σ : ℝ} (sh : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    ‖lambdaPowerFun (I := I) (M := M) sh T‖ = ‖T‖ := by
  have h_target_sq : ‖lambdaPowerFun (I := I) (M := M) sh T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i (σ - sh) *
        (tensorSobolevWeight (I := I) (M := M) i (sh / 2) *
          T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (lambdaPowerFun (I := I) (M := M) sh T)
    simpa only [lambdaPowerFun_coeff] using h
  have h_source_sq : ‖T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_terms : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i (σ - sh) *
          (tensorSobolevWeight (I := I) (M := M) i (sh / 2) *
            T.coeff i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
    intro i
    have h := fractionalPower_weight_term (I := I) (M := M)
      i (sh / 2) σ (T.coeff i)
    have heq : σ - 2 * (sh / 2) = σ - sh := by ring
    rwa [heq] at h
  have h_sq_eq : ‖lambdaPowerFun (I := I) (M := M) sh T‖ ^ 2 = ‖T‖ ^ 2 := by
    rw [h_target_sq, h_source_sq]
    exact tsum_congr h_terms
  have h1 : 0 ≤ ‖lambdaPowerFun (I := I) (M := M) sh T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  have := congrArg Real.sqrt h_sq_eq
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_lambdaPowerFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_lambdaPowerFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_lambdaPowerFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.norm_lambdaPowerFun

end TensorHs

def tensorLambdaPower {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (sh : ℝ) {σ : ℝ} :
    TensorHs (I := I) (M := M) g r s σ →L[ℝ]
      TensorHs (I := I) (M := M) g r s (σ - sh) :=
  LinearMap.mkContinuous
    { toFun := TensorHs.lambdaPowerFun (I := I) (M := M) sh
      map_add' := TensorHs.lambdaPowerFun_add (I := I) (M := M) sh
      map_smul' := fun c T =>
        TensorHs.lambdaPowerFun_smul (I := I) (M := M) sh c T }
    1
    (fun T => by
      change ‖TensorHs.lambdaPowerFun (I := I) (M := M) sh T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact le_of_eq (TensorHs.norm_lambdaPowerFun (I := I) (M := M) sh T))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorLambdaPower_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (sh : ℝ) (T : TensorHs (I := I) (M := M) g r s σ) :
    tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) sh T =
      TensorHs.lambdaPowerFun (I := I) (M := M) sh T := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_apply

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorLambdaPower_coeff {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (sh : ℝ) (T : TensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) sh T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i (sh / 2) * T.coeff i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_coeff

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorLambdaPower_norm {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (sh : ℝ) (T : TensorHs (I := I) (M := M) g r s σ) :
    ‖tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) sh T‖ = ‖T‖ :=
  TensorHs.norm_lambdaPowerFun (I := I) (M := M) sh T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_norm

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorLambdaPower_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (sh : ℝ) :
    ‖tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) sh‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_opNorm_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_opNorm_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_opNorm_le_one ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_opNorm_le_one

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorLambdaPower_eq_fractionalPower
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ}
    (sh : ℝ) (T : TensorHs (I := I) (M := M) g r s σ) :
    tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) sh T =
      TensorHs.cast (I := I) (M := M)
        (by ring : σ - 2 * (sh / 2) = σ - sh)
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (sh / 2) T) := by
  refine TensorHs.ext ?_
  funext i
  rw [tensorLambdaPower_coeff, TensorHs.cast_coeff,
    tensorFractionalPower_coeff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_eq_fractionalPower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_eq_fractionalPower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_eq_fractionalPower ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_eq_fractionalPower

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorLambdaPower_zero_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ}
    (T : TensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) (0 : ℝ) T).coeff i =
      T.coeff i := by
  rw [tensorLambdaPower_coeff, zero_div, tensorSobolevWeight_zero, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_zero_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_zero_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_zero_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorLambdaPower_zero_coeff

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_tensorHsInclusion
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {τ σ : ℝ}
    (θ : ℝ) (hτσ : τ ≤ σ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ T) =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (sub_le_sub_right hτσ (2 * θ))
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ T) := by
  refine TensorHs.ext ?_
  funext i
  rw [tensorFractionalPower_coeff, tensorHsInclusion_coeff_apply,
    tensorHsInclusion_coeff_apply, tensorFractionalPower_coeff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_tensorHsInclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_tensorHsInclusion

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_comp_tensorHsInclusion
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {τ σ : ℝ}
    (θ : ℝ) (hτσ : τ ≤ σ) :
    (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ) =
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (sub_le_sub_right hτσ (2 * θ))).comp
        (tensorFractionalPower (I := I) (M := M) (σ := σ)
          θ) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact tensorFractionalPower_tensorHsInclusion (I := I) (M := M) θ hτσ T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_comp_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_comp_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_comp_tensorHsInclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorFractionalPower_comp_tensorHsInclusion

def tensorHsEquivOfFractionalPower {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    (σ τ : ℝ) :
    TensorHs (I := I) (M := M) g r s σ ≃ₗᵢ[ℝ]
      TensorHs (I := I) (M := M) g r s τ :=
  (tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s)
    ((σ - τ) / 2) σ).trans
    (TensorHs.castEquiv (I := I) (M := M)
      (by ring : σ - 2 * ((σ - τ) / 2) = τ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsEquivOfFractionalPower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsEquivOfFractionalPower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsEquivOfFractionalPower ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsEquivOfFractionalPower

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsEquivOfFractionalPower_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (σ τ : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHsEquivOfFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) σ τ T).coeff
        i =
      tensorSobolevWeight (I := I) (M := M) i ((σ - τ) / 2) * T.coeff i := by
  unfold tensorHsEquivOfFractionalPower
  rw [LinearIsometryEquiv.trans_apply]
  change (TensorHs.castEquiv (I := I) (M := M) _
    (tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s)
      ((σ - τ) / 2) σ T)).coeff i = _
  rw [TensorHs.castEquiv_coeff, tensorFractionalPowerEquiv_coeff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsEquivOfFractionalPower_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsEquivOfFractionalPower_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsEquivOfFractionalPower_coeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsEquivOfFractionalPower_coeff

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsEquivOfFractionalPower_norm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (σ τ : ℝ)
    (T : TensorHs (I := I) (M := M) g r s σ) :
    ‖tensorHsEquivOfFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) σ τ T‖ =
      ‖T‖ :=
  (tensorHsEquivOfFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s)
    σ τ).norm_map T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsEquivOfFractionalPower_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsEquivOfFractionalPower_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsEquivOfFractionalPower_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsEquivOfFractionalPower_norm

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
