import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcing
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.H0MultiplicationInclusion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

variable {ι : Type*}

open _root_.AddCircle in
def parameterDerivativeBaselineForcingHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2))) :
    (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) ×
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
    let D := parameterDerivativeHs g 1
    let Q := K.comp (parameterSecondDerivativeHs g 2)
    let m := scalarHsMul g 1 (by norm_num)
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i : ι =>
        (((m.flip (D (Q (f₀ i)))).comp J +
          (m.flip (J (Q (f₀ i)))).comp D).comp (ContinuousLinearMap.fst ℝ _ _)) +
          (D.comp (PiLp.proj 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) i)).comp
            (ContinuousLinearMap.snd ℝ _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeBaselineForcingHsPi then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeBaselineForcingHsPi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeBaselineForcingHsPi ``Submission.AddCircle.parameterDerivativeBaselineForcingHsPi

open _root_.AddCircle in
private theorem parameterDerivativeHs_project_one
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let D := (parameterDerivativeHs g 0).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    Z (D (J u)) = P (parameterDerivativeHs g 1 u) := by
  intro J D Z P
  simp only [D, J, ContinuousLinearMap.comp_apply]
  rw [← tensorHsInclusion_trans_apply,
    parameterDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1)]
  exact (tensorHsInclusion_trans_apply _ _ _).symm

run_cmd do
  let target := ``Submission.AddCircle.parameterDerivativeHs_project_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.parameterDerivativeHs_project_one target :: scope.openDecls } }

open _root_.AddCircle in
private theorem parameterSecondDerivativeHs_project_two
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    parameterSecondDerivativeHs g 1 (P u) = J (K (parameterSecondDerivativeHs g 2 u)) := by
  intro J K P
  rw [parameterSecondDerivativeHs_tensorHsInclusion g (by omega : 1 ≤ 2)]
  exact tensorHsInclusion_trans_apply _ _ _

run_cmd do
  let target := ``Submission.AddCircle.parameterSecondDerivativeHs_project_two
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.parameterSecondDerivativeHs_project_two target :: scope.openDecls } }

open _root_.AddCircle in
theorem tensorHsInclusion_parameterDerivativeBaselineForcingHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (a₂ : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (b₂ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    (ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ)))
      (parameterDerivativeBaselineForcingHsPi g f₀ (a₂, b₂)) =
    WithLp.toLp 2 (fun i => parameterDerivativeParabolicForcing g (J a₂) (J (b₂ i)) (P (f₀ i)) 0) := by
  intro J P
  let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
  let Q := K.comp (parameterSecondDerivativeHs g 2)
  let D := (parameterDerivativeHs g 0).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ)))
  let Dh := (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))).comp
      ((parameterDerivativeHs g 2).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)))
  let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let J₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
  have hD (u : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
      Z (D (J u)) = J₀ (parameterDerivativeHs g 1 u) :=
    parameterDerivativeHs_project_one g u
  have hQ (i : ι) : parameterSecondDerivativeHs g 1 (P (f₀ i)) = J (Q (f₀ i)) :=
    parameterSecondDerivativeHs_project_two g (f₀ i)
  have hthird (i : ι) :
      J₀ (parameterDerivativeHs g 1 (Q (f₀ i))) =
        Z (parameterSecondDerivativeHs g 0 (Dh (P (f₀ i)))) := by
    rw [← hD, ← hQ]
    exact congrArg Z (parameterDerivativeHs_parameterSecondDerivativeHs g 0 (P (f₀ i)))
  apply PiLp.ext
  intro i
  change J₀ (scalarHsMul g 1 (by norm_num) (J a₂)
      (parameterDerivativeHs g 1 (Q (f₀ i))) +
    scalarHsMul g 1 (by norm_num) (parameterDerivativeHs g 1 a₂) (J (Q (f₀ i))) +
      parameterDerivativeHs g 1 (b₂ i)) = _
  rw [J₀.map_add, J₀.map_add, tensorHsInclusion_scalarHsMul_zero,
    tensorHsInclusion_scalarHsMul_zero, hthird]
  change scalarH0ContinuousMul g (C (J a₂))
      (Z (parameterSecondDerivativeHs g 0 (Dh (P (f₀ i))))) +
    scalarH0ContinuousMul g (C (parameterDerivativeHs g 1 a₂)) (J₀ (J (Q (f₀ i)))) +
      J₀ (parameterDerivativeHs g 1 (b₂ i)) = _
  rw [scalarH0ContinuousMul_scalarH1ToContinuous_comm]
  simp only [parameterDerivativeParabolicForcing, map_zero, zero_apply,
    zero_add, add_zero, sub_zero]
  change _ = scalarH0ContinuousMul g (C (J a₂))
      (Z (parameterSecondDerivativeHs g 0 (Dh (P (f₀ i))))) +
    scalarH0ContinuousMul g (C (parameterSecondDerivativeHs g 1 (P (f₀ i))))
      (Z (D (J a₂))) + Z (D (J (b₂ i)))
  rw [hQ, hD, hD]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.tensorHsInclusion_parameterDerivativeBaselineForcingHsPi then
    throwError "Refusing to shadow existing declaration AddCircle.tensorHsInclusion_parameterDerivativeBaselineForcingHsPi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.tensorHsInclusion_parameterDerivativeBaselineForcingHsPi ``Submission.AddCircle.tensorHsInclusion_parameterDerivativeBaselineForcingHsPi

section

open _root_.MeasureTheory _root_.Submission.MeasureTheory

variable [Fintype ι]

open _root_.AddCircle in
def parameterDerivativeBaselineForcingLp
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    {Ω : Type*} [MeasurableSpace Ω] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : _root_.MeasureTheory.Measure Ω}
    (a₂ : _root_.MeasureTheory.Lp (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) p μ)
    (b₂ : _root_.MeasureTheory.Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) p μ) :
    Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) p μ :=
    let L := parameterDerivativeBaselineForcingHsPi g f₀
    (L.comp (ContinuousLinearMap.inl ℝ _ _)).compLpL p μ a₂ +
      (L.comp (ContinuousLinearMap.inr ℝ _ _)).compLpL p μ b₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeBaselineForcingLp then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeBaselineForcingLp"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeBaselineForcingLp ``Submission.AddCircle.parameterDerivativeBaselineForcingLp

open _root_.AddCircle in
theorem parameterDerivativeBaselineForcingLp_ae
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    {Ω : Type*} [MeasurableSpace Ω] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : _root_.MeasureTheory.Measure Ω}
    (a₂ : _root_.MeasureTheory.Lp (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) p μ)
    (b₂ : _root_.MeasureTheory.Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) p μ) :
    ∀ᵐ t ∂μ, parameterDerivativeBaselineForcingLp g f₀ a₂ b₂ t =
      parameterDerivativeBaselineForcingHsPi g f₀ (a₂ t, b₂ t) := by
  let L := parameterDerivativeBaselineForcingHsPi g f₀
  let A := L.comp (ContinuousLinearMap.inl ℝ _ _)
  let B := L.comp (ContinuousLinearMap.inr ℝ _ _)
  filter_upwards [Lp.coeFn_add (A.compLpL p μ a₂) (B.compLpL p μ b₂),
    A.coeFn_compLpL a₂, B.coeFn_compLpL b₂] with t hsum hA hB
  change (A.compLpL p μ a₂ + B.compLpL p μ b₂) t = _
  rw [hsum, Pi.add_apply, hA, hB]
  change L (a₂ t, 0) + L (0, b₂ t) = L (a₂ t, b₂ t)
  rw [← L.map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeBaselineForcingLp_ae then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeBaselineForcingLp_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeBaselineForcingLp_ae ``Submission.AddCircle.parameterDerivativeBaselineForcingLp_ae

end

end AddCircle

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
namespace AddCircle
open _root_.AddCircle
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open _root_.AddCircle in
private theorem norm_compLpL_inl_add_compLpL_inr_le
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {Ω : Type*} [MeasurableSpace Ω] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : _root_.MeasureTheory.Measure Ω}
    (L : (X × Y) →L[ℝ] Z) (a : _root_.MeasureTheory.Lp X p μ) (b : _root_.MeasureTheory.Lp Y p μ) :
    ‖(L.comp (ContinuousLinearMap.inl ℝ X Y)).compLpL p μ a +
      (L.comp (ContinuousLinearMap.inr ℝ X Y)).compLpL p μ b‖ ≤
        ‖L‖ * (‖a‖ + ‖b‖) := by
  have hA : ‖L.comp (ContinuousLinearMap.inl ℝ X Y)‖ ≤ ‖L‖ :=
    (ContinuousLinearMap.opNorm_comp_le L (ContinuousLinearMap.inl ℝ X Y)).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_inl_le_one ℝ X Y) (norm_nonneg L))
  have hB : ‖L.comp (ContinuousLinearMap.inr ℝ X Y)‖ ≤ ‖L‖ :=
    (ContinuousLinearMap.opNorm_comp_le L (ContinuousLinearMap.inr ℝ X Y)).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_inr_le_one ℝ X Y) (norm_nonneg L))
  calc
    _ ≤ ‖(L.comp (ContinuousLinearMap.inl ℝ X Y)).compLpL p μ a‖ +
        ‖(L.comp (ContinuousLinearMap.inr ℝ X Y)).compLpL p μ b‖ := norm_add_le _ _
    _ ≤ ‖L.comp (ContinuousLinearMap.inl ℝ X Y)‖ * ‖a‖ +
        ‖L.comp (ContinuousLinearMap.inr ℝ X Y)‖ * ‖b‖ :=
      add_le_add ((L.comp (ContinuousLinearMap.inl ℝ X Y)).norm_compLp_le a)
        ((L.comp (ContinuousLinearMap.inr ℝ X Y)).norm_compLp_le b)
    _ ≤ ‖L‖ * ‖a‖ + ‖L‖ * ‖b‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hA (norm_nonneg a))
        (mul_le_mul_of_nonneg_right hB (norm_nonneg b))
    _ = _ := (mul_add _ _ _).symm

run_cmd do
  let target := ``Submission.AddCircle.norm_compLpL_inl_add_compLpL_inr_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.norm_compLpL_inl_add_compLpL_inr_le target :: scope.openDecls } }

open _root_.AddCircle in
theorem parameterDerivativeBaselineForcingLp_norm_le
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    {Ω : Type*} [MeasurableSpace Ω] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : _root_.MeasureTheory.Measure Ω}
    (a₂ : _root_.MeasureTheory.Lp (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) p μ)
    (b₂ : _root_.MeasureTheory.Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) p μ) :
    ‖parameterDerivativeBaselineForcingLp g f₀ a₂ b₂‖ ≤
      ‖parameterDerivativeBaselineForcingHsPi g f₀‖ * (‖a₂‖ + ‖b₂‖) := by
  dsimp only [parameterDerivativeBaselineForcingLp]
  apply norm_compLpL_inl_add_compLpL_inr_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeBaselineForcingLp_norm_le then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeBaselineForcingLp_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeBaselineForcingLp_norm_le ``Submission.AddCircle.parameterDerivativeBaselineForcingLp_norm_le

end AddCircle
end
