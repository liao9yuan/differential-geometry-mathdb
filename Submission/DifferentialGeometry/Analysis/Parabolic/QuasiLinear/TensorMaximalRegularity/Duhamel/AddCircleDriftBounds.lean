import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedOperators
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.AffineMajorant

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

variable {ι : Type*} [Fintype ι]

open _root_.AddCircle in
theorem norm_parameterDriftOperatorHsPi_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
    let D : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := parameterDerivativeHs g 1
    let m : TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := scalarHsMul g 1 (by norm_num)
    let d : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
    ‖parameterDriftOperatorHsPi (ι := ι) g a‖ ≤
      (‖m‖ * ‖D‖ ^ 2) * ‖a‖ + ‖m‖ * ‖d‖ * ‖D‖ := by
  intro D m d
  have hbase : ‖parameterDriftOperatorHsPi (ι := ι) g a‖ ≤
      ‖m‖ * ‖D a - d‖ * ‖D‖ := by
    apply ContinuousLinearMap.norm_piLpMap_le _ (by positivity)
    intro i
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (m.le_opNorm _) (norm_nonneg _))
  calc
    _ ≤ ‖m‖ * ‖D a - d‖ * ‖D‖ := hbase
    _ ≤ ‖m‖ * (‖D‖ * ‖a‖ + ‖d‖) * ‖D‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_sub_le (D a) d).trans (add_le_add (D.le_opNorm a) le_rfl)
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.norm_parameterDriftOperatorHsPi_le then
    throwError "Refusing to shadow existing declaration AddCircle.norm_parameterDriftOperatorHsPi_le"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.norm_parameterDriftOperatorHsPi_le ``Submission.AddCircle.norm_parameterDriftOperatorHsPi_le

open _root_.AddCircle in
theorem norm_parameterDriftOperatorH0Pi_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let D : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := parameterDerivativeHs g 1
    let D₀ := Z.comp (parameterDerivativeHs g 0)
    let m := scalarH0ContinuousMul g
    let d : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
    ‖parameterDriftOperatorH0Pi (ι := ι) g a‖ ≤
      (‖m‖ * ‖C‖ * ‖D‖ * ‖D₀‖) * ‖a‖ + ‖m‖ * ‖C‖ * ‖d‖ * ‖D₀‖ := by
  intro C Z D D₀ m d
  have hbase : ‖parameterDriftOperatorH0Pi (ι := ι) g a‖ ≤
      ‖m‖ * (‖C‖ * ‖D a - d‖) * ‖D₀‖ := by
    apply ContinuousLinearMap.norm_piLpMap_le _ (by positivity)
    intro i
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (m.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (C.le_opNorm _) (norm_nonneg _))
  calc
    _ ≤ ‖m‖ * (‖C‖ * ‖D a - d‖) * ‖D₀‖ := hbase
    _ ≤ ‖m‖ * (‖C‖ * (‖D‖ * ‖a‖ + ‖d‖)) * ‖D₀‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_sub_le (D a) d).trans (add_le_add (D.le_opNorm a) le_rfl)
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.norm_parameterDriftOperatorH0Pi_le then
    throwError "Refusing to shadow existing declaration AddCircle.norm_parameterDriftOperatorH0Pi_le"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.norm_parameterDriftOperatorH0Pi_le ``Submission.AddCircle.norm_parameterDriftOperatorH0Pi_le

open _root_.AddCircle in
theorem norm_toLp_parameterDriftOperatorHsPi_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    let D : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := parameterDerivativeHs g 1
    let m : TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := scalarHsMul g 1 (by norm_num)
    let d : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
    let h := memLp_parameterDriftOperatorHsPi (ι := ι) g (Lp.memLp a)
    ‖h.toLp (fun t => parameterDriftOperatorHsPi (ι := ι) g (a t))‖ ≤
      (‖m‖ * ‖D‖ ^ 2) * ‖a‖ + Real.sqrt T * (‖m‖ * ‖d‖ * ‖D‖) := by
  intro D m d h
  apply timeL2_norm_le_of_ae_affine_bound _ a (by positivity) (by positivity)
  filter_upwards [h.coeFn_toLp] with t ht
  rw [ht]
  exact norm_parameterDriftOperatorHsPi_le g (a t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.norm_toLp_parameterDriftOperatorHsPi_le then
    throwError "Refusing to shadow existing declaration AddCircle.norm_toLp_parameterDriftOperatorHsPi_le"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.norm_toLp_parameterDriftOperatorHsPi_le ``Submission.AddCircle.norm_toLp_parameterDriftOperatorHsPi_le

open _root_.AddCircle in
theorem norm_toLp_parameterDriftOperatorH0Pi_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let D : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := parameterDerivativeHs g 1
    let D₀ := Z.comp (parameterDerivativeHs g 0)
    let m := scalarH0ContinuousMul g
    let d : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
    let h := memLp_parameterDriftOperatorH0Pi (ι := ι) g (Lp.memLp a)
    ‖h.toLp (fun t => parameterDriftOperatorH0Pi (ι := ι) g (a t))‖ ≤
      (‖m‖ * ‖C‖ * ‖D‖ * ‖D₀‖) * ‖a‖ +
        Real.sqrt T * (‖m‖ * ‖C‖ * ‖d‖ * ‖D₀‖) := by
  intro C Z D D₀ m d h
  apply timeL2_norm_le_of_ae_affine_bound _ a (by positivity) (by positivity)
  filter_upwards [h.coeFn_toLp] with t ht
  rw [ht]
  exact norm_parameterDriftOperatorH0Pi_le g (a t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.norm_toLp_parameterDriftOperatorH0Pi_le then
    throwError "Refusing to shadow existing declaration AddCircle.norm_toLp_parameterDriftOperatorH0Pi_le"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.norm_toLp_parameterDriftOperatorH0Pi_le ``Submission.AddCircle.norm_toLp_parameterDriftOperatorH0Pi_le

end AddCircle
