import Submission.DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpOperators
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleMultiplicationInclusion
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedForcing

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

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

variable {ι : Type*} [Fintype ι]

open _root_.AddCircle in
def parameterPrincipalOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
    ((ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi fun _ : ι =>
        ((parameterSecondDerivativeHs g 1).precomp _).comp
          (scalarHsMul g 1 (by norm_num))))
      (a - ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterPrincipalOperatorHsPi then
    throwError "Refusing to shadow existing declaration AddCircle.parameterPrincipalOperatorHsPi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterPrincipalOperatorHsPi ``Submission.AddCircle.parameterPrincipalOperatorHsPi

open _root_.AddCircle in
def parameterDriftOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
    ((ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi fun _ : ι =>
        ((parameterDerivativeHs g 1).precomp _).comp
          (scalarHsMul g 1 (by norm_num))))
      (parameterDerivativeHs g 1 a -
        ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDriftOperatorHsPi then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDriftOperatorHsPi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDriftOperatorHsPi ``Submission.AddCircle.parameterDriftOperatorHsPi

open _root_.AddCircle in
def parameterPrincipalOperatorH0Pi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ)) :=
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    ((ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi fun _ : ι =>
        (((Z.comp (parameterSecondDerivativeHs g 0)).precomp _).comp
          (scalarH0ContinuousMul g)).comp C))
      (a - ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterPrincipalOperatorH0Pi then
    throwError "Refusing to shadow existing declaration AddCircle.parameterPrincipalOperatorH0Pi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterPrincipalOperatorH0Pi ``Submission.AddCircle.parameterPrincipalOperatorH0Pi

open _root_.AddCircle in
def parameterDriftOperatorH0Pi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ)) :=
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    ((ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi fun _ : ι =>
        (((Z.comp (parameterDerivativeHs g 0)).precomp _).comp
          (scalarH0ContinuousMul g)).comp C))
      (parameterDerivativeHs g 1 a -
        ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDriftOperatorH0Pi then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDriftOperatorH0Pi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDriftOperatorH0Pi ``Submission.AddCircle.parameterDriftOperatorH0Pi

open _root_.AddCircle in
theorem tensorHsInclusion_parameterPrincipalOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) :
    (ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ)))
      (parameterPrincipalOperatorHsPi g a v) =
    parameterPrincipalOperatorH0Pi g a
      ((ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2)) v) := by
  apply PiLp.ext
  intro i
  exact tensorHsInclusion_scalarHsMul_parameterSecondDerivativeHs g _ (v i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.tensorHsInclusion_parameterPrincipalOperatorHsPi then
    throwError "Refusing to shadow existing declaration AddCircle.tensorHsInclusion_parameterPrincipalOperatorHsPi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.tensorHsInclusion_parameterPrincipalOperatorHsPi ``Submission.AddCircle.tensorHsInclusion_parameterPrincipalOperatorHsPi

open _root_.AddCircle in
theorem tensorHsInclusion_parameterDriftOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) :
    (ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ)))
      (parameterDriftOperatorHsPi g a v) =
    parameterDriftOperatorH0Pi g a
      ((ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 1)) v) := by
  apply PiLp.ext
  intro i
  exact tensorHsInclusion_scalarHsMul_parameterDerivativeHs g _ (v i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.tensorHsInclusion_parameterDriftOperatorHsPi then
    throwError "Refusing to shadow existing declaration AddCircle.tensorHsInclusion_parameterDriftOperatorHsPi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.tensorHsInclusion_parameterDriftOperatorHsPi ``Submission.AddCircle.tensorHsInclusion_parameterDriftOperatorHsPi

open _root_.AddCircle in
theorem memLp_parameterPrincipalOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] {μ : _root_.MeasureTheory.Measure Ω} [_root_.MeasureTheory.IsFiniteMeasure μ]
    {p : ℝ≥0∞} {a : Ω → TensorHs g 0 0 ((1 : ℕ) : ℝ)}
    (ha : _root_.MeasureTheory.MemLp a p μ) :
    MemLp (fun t => parameterPrincipalOperatorHsPi (ι := ι) g (a t)) p μ := by
  exact (ha.sub (_root_.MeasureTheory.memLp_const _)).continuousLinearMap_comp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.memLp_parameterPrincipalOperatorHsPi then
    throwError "Refusing to shadow existing declaration AddCircle.memLp_parameterPrincipalOperatorHsPi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.memLp_parameterPrincipalOperatorHsPi ``Submission.AddCircle.memLp_parameterPrincipalOperatorHsPi

open _root_.AddCircle in
theorem memLp_parameterDriftOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] {μ : _root_.MeasureTheory.Measure Ω} [_root_.MeasureTheory.IsFiniteMeasure μ]
    {p : ℝ≥0∞} {a : Ω → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)}
    (ha : _root_.MeasureTheory.MemLp a p μ) :
    MemLp (fun t => parameterDriftOperatorHsPi (ι := ι) g (a t)) p μ := by
  exact ((ha.continuousLinearMap_comp (parameterDerivativeHs g 1)).sub
    (_root_.MeasureTheory.memLp_const _)).continuousLinearMap_comp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.memLp_parameterDriftOperatorHsPi then
    throwError "Refusing to shadow existing declaration AddCircle.memLp_parameterDriftOperatorHsPi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.memLp_parameterDriftOperatorHsPi ``Submission.AddCircle.memLp_parameterDriftOperatorHsPi

open _root_.AddCircle in
theorem memLp_parameterPrincipalOperatorH0Pi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] {μ : _root_.MeasureTheory.Measure Ω} [_root_.MeasureTheory.IsFiniteMeasure μ]
    {p : ℝ≥0∞} {a : Ω → TensorHs g 0 0 ((1 : ℕ) : ℝ)}
    (ha : _root_.MeasureTheory.MemLp a p μ) :
    MemLp (fun t => parameterPrincipalOperatorH0Pi (ι := ι) g (a t)) p μ := by
  exact (ha.sub (_root_.MeasureTheory.memLp_const _)).continuousLinearMap_comp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.memLp_parameterPrincipalOperatorH0Pi then
    throwError "Refusing to shadow existing declaration AddCircle.memLp_parameterPrincipalOperatorH0Pi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.memLp_parameterPrincipalOperatorH0Pi ``Submission.AddCircle.memLp_parameterPrincipalOperatorH0Pi

open _root_.AddCircle in
theorem memLp_parameterDriftOperatorH0Pi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] {μ : _root_.MeasureTheory.Measure Ω} [_root_.MeasureTheory.IsFiniteMeasure μ]
    {p : ℝ≥0∞} {a : Ω → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)}
    (ha : _root_.MeasureTheory.MemLp a p μ) :
    MemLp (fun t => parameterDriftOperatorH0Pi (ι := ι) g (a t)) p μ := by
  exact ((ha.continuousLinearMap_comp (parameterDerivativeHs g 1)).sub
    (_root_.MeasureTheory.memLp_const _)).continuousLinearMap_comp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.memLp_parameterDriftOperatorH0Pi then
    throwError "Refusing to shadow existing declaration AddCircle.memLp_parameterDriftOperatorH0Pi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.memLp_parameterDriftOperatorH0Pi ``Submission.AddCircle.memLp_parameterDriftOperatorH0Pi

open _root_.AddCircle in
theorem norm_parameterPrincipalOperatorHsPi_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    ‖parameterPrincipalOperatorHsPi (ι := ι) g a‖ ≤
      ‖scalarHsMul g 1 (by norm_num)‖ *
        ‖a - ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g))‖ *
          ‖parameterSecondDerivativeHs g 1‖ := by
  apply ContinuousLinearMap.norm_piLpMap_le _ (by positivity)
  intro i
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right ((scalarHsMul g 1 (by norm_num)).le_opNorm _)
      (norm_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.norm_parameterPrincipalOperatorHsPi_le then
    throwError "Refusing to shadow existing declaration AddCircle.norm_parameterPrincipalOperatorHsPi_le"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.norm_parameterPrincipalOperatorHsPi_le ``Submission.AddCircle.norm_parameterPrincipalOperatorHsPi_le

open _root_.AddCircle in
theorem norm_parameterPrincipalOperatorH0Pi_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    ‖parameterPrincipalOperatorH0Pi (ι := ι) g a‖ ≤
      ‖scalarH0ContinuousMul g‖ * (‖C‖ *
        ‖a - ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g))‖) *
          ‖Z.comp (parameterSecondDerivativeHs g 0)‖ := by
  intro C Z
  apply ContinuousLinearMap.norm_piLpMap_le _ (by positivity)
  intro i
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact ((scalarH0ContinuousMul g).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (C.le_opNorm _) (norm_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.norm_parameterPrincipalOperatorH0Pi_le then
    throwError "Refusing to shadow existing declaration AddCircle.norm_parameterPrincipalOperatorH0Pi_le"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.norm_parameterPrincipalOperatorH0Pi_le ``Submission.AddCircle.norm_parameterPrincipalOperatorH0Pi_le

open _root_.AddCircle in
theorem parameterDerivativeParabolicForcing_eq_operators
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a₂ : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (b : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2))) :
    let a := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) a₂
    WithLp.toLp 2 (fun i => parameterDerivativeParabolicForcing g a (b i) (f₀ i) (v i)) =
      parameterPrincipalOperatorH0Pi g a v +
        parameterDriftOperatorH0Pi g a₂
          ((ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
            (g := g) (r := 0) (s := 0)
              (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)) v) +
        WithLp.toLp 2 (fun i => parameterDerivativeParabolicForcing g a (b i) (f₀ i) 0) := by
  intro a
  let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  have hc (c : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯) :
      C (ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g c)) = ⟨c, c.2.continuous⟩ := by
    ext z
    simp only [C, ContinuousLinearMap.comp_apply, tensorHsInclusion_ccTensorToHs,
      scalarH1ToContinuous_apply_ccTensorToHs,
      DifferentialGeometry.Analysis.Sobolev.scalar0_scalarCc]
    rfl
  apply PiLp.ext
  intro i
  change parameterDerivativeParabolicForcing g a (b i) (f₀ i) (v i) =
    scalarH0ContinuousMul g (C (a - ccTensorToHs g 0 ((1 : ℕ) : ℝ)
      (scalarCc g (laplacianPrincipalCoefficient g)))) _ +
    scalarH0ContinuousMul g (C (parameterDerivativeHs g 1 a₂ -
      ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g)))) _ +
    parameterDerivativeParabolicForcing g a (b i) (f₀ i) 0
  rw [C.map_sub, C.map_sub, hc, hc]
  exact parameterDerivativeParabolicForcing_eq_principal_add_drift g a₂ (b i) (f₀ i) (v i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeParabolicForcing_eq_operators then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeParabolicForcing_eq_operators"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeParabolicForcing_eq_operators ``Submission.AddCircle.parameterDerivativeParabolicForcing_eq_operators

open _root_.AddCircle in
theorem parameterDriftOperatorH0Pi_smul_apply
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (c : ℝ)
    (a : TensorHs g 0 0 ((2 : ℕ) : ℝ))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((2 : ℕ) : ℝ))) :
    let N := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let D := (parameterDerivativeHs g 1).comp N
    let d : C(AddCircle (1 : ℝ), ℝ) :=
      ⟨laplacianDriftCoefficient g, (laplacianDriftCoefficient g).2.continuous⟩
    parameterDriftOperatorH0Pi g (c • N a)
      ((ContinuousLinearMap.piLpMap 2 fun _ : ι => K) v) =
        WithLp.toLp 2 (fun i =>
          scalarH0ContinuousMul g (c • C (D a) - d) (Z (D (v i)))) := by
  intro N K Z C D d
  let Z₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let d₁ := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
  have hd : C d₁ = d := by
    ext x
    simp only [C, d₁, ContinuousLinearMap.comp_apply, tensorHsInclusion_ccTensorToHs,
      scalarH1ToContinuous_apply_ccTensorToHs,
      DifferentialGeometry.Analysis.Sobolev.scalar0_scalarCc]
    rfl
  have hder (w : TensorHs g 0 0 ((2 : ℕ) : ℝ)) :
      Z₀ (parameterDerivativeHs g 0 (K w)) = Z (D w) := by
    have h := congrArg Z₀
      (parameterDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1) (N w))
    simpa only [Z₀, Z, D, K, N, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply] using h
  apply PiLp.ext
  intro i
  change scalarH0ContinuousMul g
    (C (parameterDerivativeHs g 1 (c • N a) - d₁))
      (Z₀ (parameterDerivativeHs g 0 (K (v i)))) = _
  rw [map_smul, C.map_sub, C.map_smul, hd, hder]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDriftOperatorH0Pi_smul_apply then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDriftOperatorH0Pi_smul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDriftOperatorH0Pi_smul_apply ``Submission.AddCircle.parameterDriftOperatorH0Pi_smul_apply

open _root_.AddCircle in
theorem lipschitzWith_parameterPrincipalOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    LipschitzWith (‖scalarHsMul g 1 (by norm_num)‖₊ * ‖parameterSecondDerivativeHs g 1‖₊)
      (parameterPrincipalOperatorHsPi (ι := ι) g) := by
  let m := scalarHsMul g 1 (by norm_num)
  let Q := parameterSecondDerivativeHs g 1
  let L := (ContinuousLinearMap.piLpMapL 2).comp
    (ContinuousLinearMap.pi fun _ : ι => (Q.precomp _).comp m)
  let c := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g))
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have heq : parameterPrincipalOperatorHsPi (ι := ι) g a -
      parameterPrincipalOperatorHsPi (ι := ι) g b = L (a - b) := by
    change L (a - c) - L (b - c) = L (a - b)
    rw [← map_sub]
    congr 1
    abel
  have hnorm : ‖L (a - b)‖ ≤ ‖m‖ * ‖a - b‖ * ‖Q‖ := by
    apply ContinuousLinearMap.norm_piLpMap_le _ (by positivity)
    intro i
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (m.le_opNorm _) (norm_nonneg _))
  rw [dist_eq_norm, heq, dist_eq_norm, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
  exact hnorm.trans_eq (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.lipschitzWith_parameterPrincipalOperatorHsPi then
    throwError "Refusing to shadow existing declaration AddCircle.lipschitzWith_parameterPrincipalOperatorHsPi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.lipschitzWith_parameterPrincipalOperatorHsPi ``Submission.AddCircle.lipschitzWith_parameterPrincipalOperatorHsPi

open _root_.AddCircle in
theorem lipschitzWith_parameterDriftOperatorHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    LipschitzWith (‖scalarHsMul g 1 (by norm_num)‖₊ * ‖parameterDerivativeHs g 1‖₊ ^ 2)
      (parameterDriftOperatorHsPi (ι := ι) g) := by
  let m := scalarHsMul g 1 (by norm_num)
  let D := parameterDerivativeHs g 1
  let L := (ContinuousLinearMap.piLpMapL 2).comp
    (ContinuousLinearMap.pi fun _ : ι => (D.precomp _).comp m)
  let c := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have heq : parameterDriftOperatorHsPi (ι := ι) g a -
      parameterDriftOperatorHsPi (ι := ι) g b = L (D (a - b)) := by
    change L (D a - c) - L (D b - c) = L (D (a - b))
    calc
      _ = L ((D a - c) - (D b - c)) := (map_sub L _ _).symm
      _ = L (D a - D b) := congrArg L (by abel)
      _ = L (D (a - b)) := congrArg L (map_sub D a b).symm
  have hnorm' : ‖L (D (a - b))‖ ≤ ‖m‖ * ‖D (a - b)‖ * ‖D‖ := by
    apply ContinuousLinearMap.norm_piLpMap_le _ (by positivity)
    intro i
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (m.le_opNorm _) (norm_nonneg _))
  have hnorm : ‖L (D (a - b))‖ ≤ ‖m‖ * (‖D‖ * ‖a - b‖) * ‖D‖ :=
    hnorm'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (D.le_opNorm _) (norm_nonneg m)) (norm_nonneg D))
  rw [dist_eq_norm, heq, dist_eq_norm, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm, coe_nnnorm]
  exact hnorm.trans_eq (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.lipschitzWith_parameterDriftOperatorHsPi then
    throwError "Refusing to shadow existing declaration AddCircle.lipschitzWith_parameterDriftOperatorHsPi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.lipschitzWith_parameterDriftOperatorHsPi ``Submission.AddCircle.lipschitzWith_parameterDriftOperatorHsPi

end AddCircle
