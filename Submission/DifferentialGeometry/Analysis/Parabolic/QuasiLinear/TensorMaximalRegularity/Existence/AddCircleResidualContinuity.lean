import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.LinearTimeDependentStability
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedOperators

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

open private vectorTensorHsNormedSpace from
  Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.LinearTimeDependentStability

attribute [local instance] vectorTensorHsNormedSpace

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

private theorem principal_memLp
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a : _root_.MeasureTheory.Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T)) :
    MemLp (fun t => AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a t))
      ∞ (timeMeasure T) :=
  AddCircle.memLp_parameterPrincipalOperatorHsPi g (Lp.memLp a)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.principal_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.principal_memLp target :: scope.openDecls } }

private theorem drift_memLp
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (b : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    MemLp (fun t => AddCircle.parameterDriftOperatorHsPi (ι := ι) g (b t))
      2 (timeMeasure T) :=
  AddCircle.memLp_parameterDriftOperatorHsPi g (Lp.memLp b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.drift_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.drift_memLp target :: scope.openDecls } }

private abbrev circleHeatVectorForcingResidualCore
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} :=
  @heatVectorForcingResidualL ι (by infer_instance)
      ℝ Real.normedAddCommGroup (@InnerProductSpace.toNormedSpace ℝ ℝ Real.instRCLike
        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup ℝ
          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing ℝ
            (@SeminormedCommRing.toNonUnitalSeminormedCommRing ℝ
              (@NormedCommRing.toSeminormedCommRing ℝ Real.normedCommRing))))
        (@RCLike.toInnerProductSpaceReal ℝ Real.instRCLike))
      (@FiniteDimensional.rclike_to_real ℝ Real.instRCLike) (by infer_instance)
      ℝ (@UniformSpace.toTopologicalSpace ℝ
        (@PseudoMetricSpace.toUniformSpace ℝ Real.pseudoMetricSpace))
      (𝓘(ℝ, ℝ)) (AddCircle (1 : ℝ))
      (@QuotientAddGroup.instTopologicalSpace ℝ
        (@UniformSpace.toTopologicalSpace ℝ
          (@PseudoMetricSpace.toUniformSpace ℝ Real.pseudoMetricSpace))
        Real.instAddGroup
        (@AddSubgroup.zmultiples ℝ
          Real.instAddGroup (1 : ℝ)))
      (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)
      (by infer_instance) (by infer_instance) g 0 0 ((1 : ℕ) : ℝ) T

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleHeatVectorForcingResidualCore
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleHeatVectorForcingResidualCore target :: scope.openDecls } }

section CircleResidualOperator

variable {ι : Type*} [Fintype ι]

variable (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)

variable (A2 : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))

variable (hA2 : AEStronglyMeasurable A2 (timeMeasure T))

variable (C2 : ℝ≥0) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ C2)

variable (A1 : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) →L[ℝ]
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))

variable (hA1 : MemLp A1 2 (timeMeasure T))

private abbrev circleHeatVectorForcingResidualL :=
  circleHeatVectorForcingResidualCore (ι := ι) g hT A2 hA2 C2 hC2 A1 hA1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleHeatVectorForcingResidualL
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleHeatVectorForcingResidualL target :: scope.openDecls } }

end CircleResidualOperator

private def parameterResidualL
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (a : _root_.MeasureTheory.Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))
    (b : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (C : ℝ≥0)
    (hC : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a t)‖ ≤ C) :=
  circleHeatVectorForcingResidualL (ι := ι) g hT
    (fun t => AddCircle.parameterPrincipalOperatorHsPi g (a t))
    (principal_memLp (ι := ι) g a).aestronglyMeasurable C hC
    (fun t => AddCircle.parameterDriftOperatorHsPi g (b t))
    (drift_memLp (ι := ι) g b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterResidualL
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterResidualL target :: scope.openDecls } }

private abbrev circleResidualNormBound
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T) :=
  @heatVectorForcingResidualL_sub_norm_le ι (by infer_instance)
      ℝ Real.normedAddCommGroup (@InnerProductSpace.toNormedSpace ℝ ℝ Real.instRCLike
        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup ℝ
          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing ℝ
            (@SeminormedCommRing.toNonUnitalSeminormedCommRing ℝ
              (@NormedCommRing.toSeminormedCommRing ℝ Real.normedCommRing))))
        (@RCLike.toInnerProductSpaceReal ℝ Real.instRCLike))
      (@FiniteDimensional.rclike_to_real ℝ Real.instRCLike) (by infer_instance)
      ℝ (@UniformSpace.toTopologicalSpace ℝ
        (@PseudoMetricSpace.toUniformSpace ℝ Real.pseudoMetricSpace))
      (𝓘(ℝ, ℝ)) (AddCircle (1 : ℝ))
      (@QuotientAddGroup.instTopologicalSpace ℝ
        (@UniformSpace.toTopologicalSpace ℝ
          (@PseudoMetricSpace.toUniformSpace ℝ Real.pseudoMetricSpace))
        Real.instAddGroup
        (@AddSubgroup.zmultiples ℝ
          Real.instAddGroup (1 : ℝ)))
      (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)
      (by infer_instance) (by infer_instance) g 0 0 ((1 : ℕ) : ℝ) T hT

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleResidualNormBound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleResidualNormBound target :: scope.openDecls } }

private abbrev principalCoefficientConstant
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :=
  ‖scalarHsMul g 1 (by norm_num)‖₊ * ‖AddCircle.parameterSecondDerivativeHs g 1‖₊

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.principalCoefficientConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.principalCoefficientConstant target :: scope.openDecls } }

private abbrev driftCoefficientConstant
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :=
  ‖scalarHsMul g 1 (by norm_num)‖₊ * ‖AddCircle.parameterDerivativeHs g 1‖₊ ^ 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.driftCoefficientConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.driftCoefficientConstant target :: scope.openDecls } }

private theorem principal_ae_sub_norm_le
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a a0 : _root_.MeasureTheory.Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T)) :
    ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a t) -
        AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a0 t)‖ ≤
          (principalCoefficientConstant g : ℝ) * ‖a - a0‖ := by
  have hnorm : ∀ᵐ t ∂timeMeasure T, ‖(a - a0) t‖ ≤ ‖a - a0‖ := by
    simpa only [← _root_.MeasureTheory.toReal_eLpNorm (Lp.memLp (a - a0)).aestronglyMeasurable, Lp.norm_def] using
      _root_.MeasureTheory.ae_le_lpNorm_exponent_top (Lp.memLp (a - a0))
  filter_upwards [hnorm, Lp.coeFn_sub a a0] with t ht hsub
  have hsmall : ‖a t - a0 t‖ ≤ ‖a - a0‖ := by
    simpa only [hsub, Pi.sub_apply] using ht
  exact ((AddCircle.lipschitzWith_parameterPrincipalOperatorHsPi (ι := ι) g).norm_sub_le
    (a t) (a0 t)).trans (mul_le_mul_of_nonneg_left hsmall
      (principalCoefficientConstant g).coe_nonneg)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.principal_ae_sub_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.principal_ae_sub_norm_le target :: scope.openDecls } }

private theorem lp_norm_sub_le_of_lipschitzWith
    {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : _root_.MeasureTheory.Measure Ω} {p : ℝ≥0∞}
    {c : ℝ≥0} {f : E → F} (hf : LipschitzWith c f)
    (u u0 : _root_.MeasureTheory.Lp E p μ) (v v0 : _root_.MeasureTheory.Lp F p μ)
    (hv : v =ᵐ[μ] fun t => f (u t)) (hv0 : v0 =ᵐ[μ] fun t => f (u0 t)) :
    ‖v - v0‖ ≤ (c : ℝ) * ‖u - u0‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hv, hv0, Lp.coeFn_sub v v0, Lp.coeFn_sub u u0]
    with t hvt hv0t hvsub husub
  rw [hvsub, husub, Pi.sub_apply, Pi.sub_apply, hvt, hv0t]
  exact hf.norm_sub_le _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.lp_norm_sub_le_of_lipschitzWith
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.lp_norm_sub_le_of_lipschitzWith target :: scope.openDecls } }

private theorem drift_lp_sub_norm_le
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (b b0 : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    ‖(drift_memLp (ι := ι) g b).toLp
        (fun t => AddCircle.parameterDriftOperatorHsPi (ι := ι) g (b t)) -
      (drift_memLp (ι := ι) g b0).toLp
        (fun t => AddCircle.parameterDriftOperatorHsPi (ι := ι) g (b0 t))‖ ≤
          (driftCoefficientConstant g : ℝ) * ‖b - b0‖ := by
  exact lp_norm_sub_le_of_lipschitzWith
    (AddCircle.lipschitzWith_parameterDriftOperatorHsPi (ι := ι) g) b b0 _ _
    (drift_memLp (ι := ι) g b).coeFn_toLp (drift_memLp (ι := ι) g b0).coeFn_toLp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.drift_lp_sub_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.drift_lp_sub_norm_le target :: scope.openDecls } }

section ParameterBound

variable {ι : Type*} [Fintype ι]

variable (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)

variable (a a0 : Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))

variable (b b0 : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)

variable (C C0 : ℝ≥0)

variable (hC : ∀ᵐ t ∂timeMeasure T,
    ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a t)‖ ≤ C)

variable (hC0 : ∀ᵐ t ∂timeMeasure T,
    ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a0 t)‖ ≤ C0)

private abbrev parameterResidualDifferenceNorm :=
  ‖parameterResidualL g hT a b C hC - parameterResidualL g hT a0 b0 C0 hC0‖

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterResidualDifferenceNorm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterResidualDifferenceNorm target :: scope.openDecls } }

private theorem principal_ae_sub_nnnorm_le :
    ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a t) -
        AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a0 t)‖ ≤
          ((principalCoefficientConstant g * ‖a - a0‖₊ : ℝ≥0) : ℝ) := by
  simpa only [NNReal.coe_mul, coe_nnnorm] using principal_ae_sub_norm_le (ι := ι) g a a0

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.principal_ae_sub_nnnorm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.principal_ae_sub_nnnorm_le target :: scope.openDecls } }

private abbrev parameterPrincipalResidualNormBound :=
  circleResidualNormBound (ι := ι) g hT
    (fun t => AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a t))
    (fun t => AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a0 t))
    (principal_memLp (ι := ι) g a).aestronglyMeasurable
    (principal_memLp (ι := ι) g a0).aestronglyMeasurable
    C C0 (principalCoefficientConstant g * ‖a - a0‖₊) hC hC0
    (principal_ae_sub_nnnorm_le (ι := ι) g a a0)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterPrincipalResidualNormBound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterPrincipalResidualNormBound target :: scope.openDecls } }

private abbrev parameterResidualNormBound :
    parameterResidualDifferenceNorm g hT a a0 b b0 C C0 hC hC0 ≤
      ((principalCoefficientConstant g * ‖a - a0‖₊ : ℝ≥0) : ℝ) * (1 + T) +
        Real.sqrt (1 + T) *
          ‖(drift_memLp (ι := ι) g b).toLp
              (fun t => AddCircle.parameterDriftOperatorHsPi (ι := ι) g (b t)) -
            (drift_memLp (ι := ι) g b0).toLp
              (fun t => AddCircle.parameterDriftOperatorHsPi (ι := ι) g (b0 t))‖ := by
  dsimp only [parameterResidualDifferenceNorm, parameterResidualL,
    circleHeatVectorForcingResidualL, circleHeatVectorForcingResidualCore]
  with_reducible_and_instances
    exact parameterPrincipalResidualNormBound g hT a a0 C C0 hC hC0
      (fun t => AddCircle.parameterDriftOperatorHsPi (ι := ι) g (b t))
      (fun t => AddCircle.parameterDriftOperatorHsPi (ι := ι) g (b0 t))
      (drift_memLp (ι := ι) g b) (drift_memLp (ι := ι) g b0)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterResidualNormBound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterResidualNormBound target :: scope.openDecls } }

private abbrev parameterResidualCoefficientNormBound :=
  (parameterResidualNormBound g hT a a0 b b0 C C0 hC hC0).trans
    (add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left (drift_lp_sub_norm_le (ι := ι) g b b0)
        (Real.sqrt_nonneg (1 + T))))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterResidualCoefficientNormBound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterResidualCoefficientNormBound target :: scope.openDecls } }

private theorem parameter_residual_sub_norm_le :
    parameterResidualDifferenceNorm g hT a a0 b b0 C C0 hC hC0 ≤
      (principalCoefficientConstant g : ℝ) * ‖a - a0‖ * (1 + T) +
        Real.sqrt (1 + T) * ((driftCoefficientConstant g : ℝ) * ‖b - b0‖) := by
  simpa only [parameterResidualDifferenceNorm, parameterResidualL,
    circleHeatVectorForcingResidualL, circleHeatVectorForcingResidualCore,
    NNReal.coe_mul, coe_nnnorm] using
    parameterResidualCoefficientNormBound g hT a a0 b b0 C C0 hC hC0

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameter_residual_sub_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameter_residual_sub_norm_le target :: scope.openDecls } }

end ParameterBound

section ParameterOperators

variable
    {X ι : Type*} [Fintype ι] {l : Filter X}

variable
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)

variable
    (a : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))

variable
    (a0 : Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T))

variable
    (b : X → timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)

variable
    (b0 : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)

variable
    (ha : Tendsto a l (𝓝 a0)) (hb : Tendsto b l (𝓝 b0))

variable
    (C : X → ℝ≥0) (C0 : ℝ≥0)

variable
    (hC : ∀ x, ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a x t)‖ ≤ C x)

variable
    (hC0 : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (a0 t)‖ ≤ C0)

include ha hb in
private theorem parameter_coefficient_norm_bound_tendsto :
    _root_.Filter.Tendsto (fun x =>
      (principalCoefficientConstant g : ℝ) * ‖a x - a0‖ * (1 + T) +
        Real.sqrt (1 + T) * ((driftCoefficientConstant g : ℝ) * ‖b x - b0‖)) l (𝓝 0) := by
  have ha0 := tendsto_iff_norm_sub_tendsto_zero.mp ha
  have hb0 := tendsto_iff_norm_sub_tendsto_zero.mp hb
  simpa only [_root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul, add_zero] using
    ((ha0.const_mul (principalCoefficientConstant g : ℝ)).mul_const (1 + T)).add
      ((hb0.const_mul (driftCoefficientConstant g : ℝ)).const_mul (Real.sqrt (1 + T)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameter_coefficient_norm_bound_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameter_coefficient_norm_bound_tendsto target :: scope.openDecls } }

include ha hb in
private theorem parameter_residual_norm_tendsto :
    _root_.Filter.Tendsto (fun x => parameterResidualDifferenceNorm g hT
      (a x) a0 (b x) b0 (C x) C0 (hC x) hC0) l (𝓝 0) := by
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun x =>
      parameter_residual_sub_norm_le g hT (a x) a0 (b x) b0 (C x) C0 (hC x) hC0)
    (parameter_coefficient_norm_bound_tendsto g a a0 b b0 ha hb)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameter_residual_norm_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameter_residual_norm_tendsto target :: scope.openDecls } }

include ha hb in
private theorem parameter_residual_tendsto :
    _root_.Filter.Tendsto (fun x => parameterResidualL g hT (a x) (b x) (C x) (hC x)) l
      (𝓝 (parameterResidualL g hT a0 b0 C0 hC0)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact parameter_residual_norm_tendsto g hT a a0 b b0 ha hb C C0 hC hC0

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameter_residual_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameter_residual_tendsto target :: scope.openDecls } }

include ha hb in
theorem tendsto_heatVectorForcingResidualL_parameterOperators :
    Tendsto (fun x => circleHeatVectorForcingResidualL (ι := ι) g hT
      (fun t => AddCircle.parameterPrincipalOperatorHsPi g (a x t))
      (principal_memLp (ι := ι) g (a x)).aestronglyMeasurable (C x) (hC x)
      (fun t => AddCircle.parameterDriftOperatorHsPi g (b x t))
      (drift_memLp (ι := ι) g (b x))) l
      (𝓝 (circleHeatVectorForcingResidualL (ι := ι) g hT
        (fun t => AddCircle.parameterPrincipalOperatorHsPi g (a0 t))
        (principal_memLp (ι := ι) g a0).aestronglyMeasurable C0 hC0
        (fun t => AddCircle.parameterDriftOperatorHsPi g (b0 t))
        (drift_memLp (ι := ι) g b0))) := by
  exact parameter_residual_tendsto g hT a a0 b b0 ha hb C C0 hC hC0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tendsto_heatVectorForcingResidualL_parameterOperators then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tendsto_heatVectorForcingResidualL_parameterOperators"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tendsto_heatVectorForcingResidualL_parameterOperators ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tendsto_heatVectorForcingResidualL_parameterOperators

end ParameterOperators


end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
