import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedBaseline
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedOperators
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.LinearTimeDependentInclusion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

variable {ι : Type*} [Fintype ι]

private theorem memLp_parameterDrift_high
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    MemLp (fun t => AddCircle.parameterDriftOperatorHsPi (ι := ι) g (a₂ t))
      2 (timeMeasure T) :=
  AddCircle.memLp_parameterDriftOperatorHsPi (ι := ι) g (Lp.memLp a₂)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_parameterDrift_high
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_parameterDrift_high target :: scope.openDecls } }

private theorem memLp_parameterDrift_low
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (Z : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) :
    MemLp (fun t => Z.comp (AddCircle.parameterDriftOperatorH0Pi (ι := ι) g (a₂ t)))
      2 (timeMeasure T) :=
  (AddCircle.memLp_parameterDriftOperatorH0Pi (ι := ι) g (Lp.memLp a₂)).continuousLinearMap_comp
    (ContinuousLinearMap.compL ℝ
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1)))
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ)))
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) Z)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_parameterDrift_low
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_parameterDrift_low target :: scope.openDecls } }

private def affineHeatEquation
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (a : ℝ)
    {T : ℝ} (hT : 0 < T)
    (A2 : ℝ → (PiLp 2 (fun _ : ι => TensorHs g 0 0 (a + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 a))
    (A1 : ℝ → (PiLp 2 (fun _ : ι => TensorHs g 0 0 (a + 1))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 a))
    (f₀ F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 a)) T) : Prop :=
  let V : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (a + 2))) T :=
    heatDuhamelVectorField (g := g) (r := 0) (s := 0) (a := a) hT 0 F
  let K : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (a + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (a + 1)) :=
    ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by linarith : a + 1 ≤ a + 2)
  ∀ᵐ t ∂timeMeasure T, F t = A2 t (V t) + A1 t (K (V t)) + f₀ t

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.affineHeatEquation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.affineHeatEquation target :: scope.openDecls } }

private def timeH1ToH0
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T : ℝ) :
    timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T →L[ℝ]
      timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) T :=
  let J : (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
    ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
  J.compLpL 2 (timeMeasure T)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeH1ToH0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeH1ToH0 target :: scope.openDecls } }

private theorem parameterDerivativeBaselineForcingLp_low_ae
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T) :
    let J : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ]
        TensorHs g 0 0 ((1 : ℕ) : ℝ) := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P : TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2) →L[ℝ]
        TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2) := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let Z : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) := ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))
    let fhigh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T :=
      AddCircle.parameterDerivativeBaselineForcingLp g f₀ a₂ b₂
    let fLow : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) T :=
      timeH1ToH0 g T fhigh
    ∀ᵐ t ∂timeMeasure T, fLow t =
      Z (WithLp.toLp 2 (fun i => AddCircle.parameterDerivativeParabolicForcing g
        (J (a₂ t)) (J (b₂ t i)) (P (f₀ i)) 0)) := by
  intro J P Z fhigh fLow
  let J₀ : (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
    ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
  filter_upwards [J₀.coeFn_compLpL fhigh,
    AddCircle.parameterDerivativeBaselineForcingLp_ae g f₀ a₂ b₂] with t hj hf
  change fLow t = J₀ (fhigh t) at hj
  rw [hj, hf]
  have hp := congrArg Z (AddCircle.tensorHsInclusion_parameterDerivativeBaselineForcingHsPi
    g f₀ (a₂ t) (b₂ t))
  refine Eq.trans ?_ hp
  apply PiLp.ext
  intro i
  apply TensorHs.ext
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeBaselineForcingLp_low_ae
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeBaselineForcingLp_low_ae target :: scope.openDecls } }

private theorem parameterDerivativeParabolicForcing_eq_low_operators
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a₂ : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (b : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)))
    (w : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) :
    let J : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ]
        TensorHs g 0 0 ((1 : ℕ) : ℝ) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let Z₀ : TensorHs g 0 0 ((0 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 (0 : ℝ) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let Z : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ))) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
      ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))
    let K : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2))) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1)) :=
      ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((0 : ℕ) : ℝ) + 2)
    (∀ i, Z₀ (w i) = AddCircle.parameterDerivativeParabolicForcing g
      (J a₂) (b i) (f₀ i) (v i)) →
    w = (Z.comp (AddCircle.parameterPrincipalOperatorH0Pi g (J a₂))) v +
      (Z.comp (AddCircle.parameterDriftOperatorH0Pi g a₂)) (K v) +
      Z (WithLp.toLp 2 (fun i => AddCircle.parameterDerivativeParabolicForcing g
        (J a₂) (b i) (f₀ i) 0)) := by
  intro J Z₀ Z K hw
  have he : w = Z (WithLp.toLp 2 (fun i =>
      AddCircle.parameterDerivativeParabolicForcing g (J a₂) (b i) (f₀ i) (v i))) := by
    apply PiLp.ext
    intro i
    change w i = tensorHsInclusion
      (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ)) (AddCircle.parameterDerivativeParabolicForcing g
      (J a₂) (b i) (f₀ i) (v i))
    rw [← hw i]
    apply TensorHs.ext
    rfl
  refine he.trans ?_
  have hp := congrArg Z (AddCircle.parameterDerivativeParabolicForcing_eq_operators
    g a₂ b f₀ v)
  simpa only [J, K, ContinuousLinearMap.comp_apply, map_add] using hp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeParabolicForcing_eq_low_operators
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeParabolicForcing_eq_low_operators target :: scope.openDecls } }

private theorem parameterDerivativeDuhamelForcing_affineHeatEquation
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T) :
    let J : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ]
        TensorHs g 0 0 ((1 : ℕ) : ℝ) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P : TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2) →L[ℝ]
        TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2) :=
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let Z : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ))) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
      ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))
    let A2l : ℝ → (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2))) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
      fun t => Z.comp (AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g (J (a₂ t)))
    let A1l : ℝ → (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1))) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
      fun t => Z.comp (AddCircle.parameterDriftOperatorH0Pi (ι := ι) g (a₂ t))
    let fhigh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T :=
      AddCircle.parameterDerivativeBaselineForcingLp g f₀ a₂ b₂
    let U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T :=
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 F
    let G : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) T :=
      parameterDerivativeDuhamelForcing g 0 hT F
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (U t i) + F t i =
        scalarHsMul g 1 (by norm_num) (J (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g 1 (P (f₀ i) + U t i)) + J (b₂ t i)) →
    affineHeatEquation g ((0 : ℕ) : ℝ) hT A2l A1l (timeH1ToH0 g T fhigh) G := by
  intro J P Z A2l A1l fhigh U G heq
  let V : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2))) T :=
    maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((0 : ℕ) : ℝ)) hT 0 G
  have hweak := parameterDerivativeDuhamelForcing_ae_eq g hT F
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => P) f₀)
    (fun t => J (a₂ t))
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : ι => J) (b₂ t)) heq
  have hbase := parameterDerivativeBaselineForcingLp_low_ae g f₀ a₂ b₂
  have hheat : heatDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((0 : ℕ) : ℝ)) hT 0 G = V := by
    simpa only [map_zero] using heatDuhamelVectorField_inclusion (g := g) (r := 0) (s := 0)
      (a := ((0 : ℕ) : ℝ)) hT (tensorResolventL2_isCompactOperator g 0 0) 0 G
  unfold affineHeatEquation
  rw [hheat]
  filter_upwards [hweak, hbase] with t hw hb
  rw [hb]
  exact parameterDerivativeParabolicForcing_eq_low_operators g (a₂ t)
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => J) (b₂ t))
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => P) f₀) (V t) (G t) hw

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeDuhamelForcing_affineHeatEquation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeDuhamelForcing_affineHeatEquation target :: scope.openDecls } }

private def affineHeatLift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (A2 : ℝ → (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (A1 : ℝ → (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (fhigh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (G : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) T)
    (FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T) : Prop :=
  affineHeatEquation g ((1 : ℕ) : ℝ) hT A2 A1 fhigh FH ∧ G = timeH1ToH0 g T FH

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.affineHeatLift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.affineHeatLift target :: scope.openDecls } }

private def coefficientContractionBound
    {E : Type*} [NormedAddCommGroup E] {T : ℝ}
    (A : ℝ → E) (hA : _root_.MeasureTheory.MemLp A 2 (timeMeasure T)) (C : ℝ≥0) : Prop :=
  (C : ℝ) * (1 + T) + Real.sqrt (1 + T) * ‖hA.toLp A‖ < 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.coefficientContractionBound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.coefficientContractionBound target :: scope.openDecls } }

private theorem memLp_parameterPrincipal_high
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (J : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    MemLp (fun t => AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (J (a₂ t)))
      2 (timeMeasure T) :=
  AddCircle.memLp_parameterPrincipalOperatorHsPi (ι := ι) g
    ((Lp.memLp a₂).continuousLinearMap_comp J)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_parameterPrincipal_high
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_parameterPrincipal_high target :: scope.openDecls } }

private theorem memLp_parameterPrincipal_low
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (J : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (Z : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) :
    MemLp (fun t => Z.comp (AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g (J (a₂ t))))
      2 (timeMeasure T) :=
  ((AddCircle.memLp_parameterPrincipalOperatorH0Pi (ι := ι) g
    ((Lp.memLp a₂).continuousLinearMap_comp J))).continuousLinearMap_comp
      (ContinuousLinearMap.compL ℝ
        (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2)))
        (PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ)))
        (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) Z)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_parameterPrincipal_low
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.memLp_parameterPrincipal_low target :: scope.openDecls } }

private theorem parameterPrincipalOperator_normalized_compatibility
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) :
    let Z : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ))) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
      ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))
    (ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))
        (AddCircle.parameterPrincipalOperatorHsPi g a v) =
      (Z.comp (AddCircle.parameterPrincipalOperatorH0Pi g a))
        ((ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2)) v) := by
  intro Z
  have hp := congrArg Z (AddCircle.tensorHsInclusion_parameterPrincipalOperatorHsPi g a v)
  refine Eq.trans ?_ hp
  apply PiLp.ext
  intro i
  apply TensorHs.ext
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterPrincipalOperator_normalized_compatibility
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterPrincipalOperator_normalized_compatibility target :: scope.openDecls } }

private theorem parameterDriftOperator_normalized_compatibility
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a₂ : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) :
    let Z : (PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ))) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
      ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))
    (ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))
        (AddCircle.parameterDriftOperatorHsPi g a₂ v) =
      (Z.comp (AddCircle.parameterDriftOperatorH0Pi g a₂))
        ((ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 1)) v) := by
  intro Z
  have hp := congrArg Z (AddCircle.tensorHsInclusion_parameterDriftOperatorHsPi g a₂ v)
  refine Eq.trans ?_ hp
  apply PiLp.ext
  intro i
  apply TensorHs.ext
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDriftOperator_normalized_compatibility
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDriftOperator_normalized_compatibility target :: scope.openDecls } }

private def lowerCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) :=
  tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.lowerCoefficient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.lowerCoefficient target :: scope.openDecls } }

private def normalizeZeroPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    (PiLp 2 (fun _ : ι => TensorHs g 0 0 (0 : ℝ))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
  ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0) (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.normalizeZeroPi
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.normalizeZeroPi target :: scope.openDecls } }

private def principalOperatorHigh
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    ℝ → (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
  fun t => AddCircle.parameterPrincipalOperatorHsPi g (lowerCoefficient g (a₂ t))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.principalOperatorHigh
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.principalOperatorHigh target :: scope.openDecls } }

private def principalOperatorLow
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    ℝ → (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
  fun t => (normalizeZeroPi g).comp
    (AddCircle.parameterPrincipalOperatorH0Pi g (lowerCoefficient g (a₂ t)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.principalOperatorLow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.principalOperatorLow target :: scope.openDecls } }

private def driftOperatorHigh
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    ℝ → (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
  fun t => AddCircle.parameterDriftOperatorHsPi g (a₂ t)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.driftOperatorHigh
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.driftOperatorHigh target :: scope.openDecls } }

private def driftOperatorLow
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    ℝ → (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ)) :=
  fun t => (normalizeZeroPi g).comp (AddCircle.parameterDriftOperatorH0Pi g (a₂ t))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.driftOperatorLow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.driftOperatorLow target :: scope.openDecls } }

private def weakParameterEquation
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T) : Prop :=
  let J := lowerCoefficient g
  let P : TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2) →L[ℝ]
      TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2) :=
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
  let U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T :=
    maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((1 : ℕ) : ℝ)) hT 0 F
  ∀ᵐ t ∂timeMeasure T, ∀ i,
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (U t i) + F t i =
      scalarHsMul g 1 (by norm_num) (J (a₂ t))
        (AddCircle.parameterSecondDerivativeHs g 1 (P (f₀ i) + U t i)) + J (b₂ t i)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.weakParameterEquation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.weakParameterEquation target :: scope.openDecls } }

private abbrev affineHeatLiftOfHighCoefficients
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (C2h : ℝ≥0)
    (hC2h : ∀ᵐ t ∂timeMeasure T, ‖principalOperatorHigh (ι := ι) g a₂ t‖ ≤ C2h)
    (fhigh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (hsmallh : coefficientContractionBound (driftOperatorHigh (ι := ι) g a₂)
      (memLp_parameterDrift_high (ι := ι) g a₂) C2h) :=
  exists_unique_heat_vector_forcing_lift_of_l2_coefficients
    (ι := ι) (E := ℝ) (H := ℝ) (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
    (g := g) (r := 0) (s := 0) (a := ((0 : ℕ) : ℝ)) (b := ((1 : ℕ) : ℝ))
    (by norm_num) hT 0 0 (map_zero _).symm
    (principalOperatorHigh g a₂)
    (memLp_parameterPrincipal_high (ι := ι) g a₂ (lowerCoefficient g)).aestronglyMeasurable
    C2h hC2h (driftOperatorHigh g a₂) (memLp_parameterDrift_high (ι := ι) g a₂) fhigh hsmallh

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.affineHeatLiftOfHighCoefficients
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.affineHeatLiftOfHighCoefficients target :: scope.openDecls } }

private abbrev affineHeatLiftOfCoefficients
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (C2h C2l : ℝ≥0)
    (hC2h : ∀ᵐ t ∂timeMeasure T, ‖principalOperatorHigh (ι := ι) g a₂ t‖ ≤ C2h)
    (hC2l : ∀ᵐ t ∂timeMeasure T, ‖principalOperatorLow (ι := ι) g a₂ t‖ ≤ C2l)
    (fhigh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (hsmallh : coefficientContractionBound (driftOperatorHigh (ι := ι) g a₂)
      (memLp_parameterDrift_high (ι := ι) g a₂) C2h)
    (hsmalll : coefficientContractionBound (driftOperatorLow (ι := ι) g a₂)
      (memLp_parameterDrift_low (ι := ι) g a₂ (normalizeZeroPi g)) C2l) :=
  affineHeatLiftOfHighCoefficients (ι := ι) g hT a₂ C2h hC2h fhigh hsmallh
    (principalOperatorLow g a₂)
    (memLp_parameterPrincipal_low (ι := ι) g a₂ (lowerCoefficient g)
      (normalizeZeroPi g)).aestronglyMeasurable C2l hC2l
    (driftOperatorLow g a₂) (memLp_parameterDrift_low (ι := ι) g a₂ (normalizeZeroPi g))
    (timeH1ToH0 (ι := ι) g T fhigh) hsmalll
    (Filter.Eventually.of_forall fun t v =>
      parameterPrincipalOperator_normalized_compatibility g (lowerCoefficient g (a₂ t)) v)
    (Filter.Eventually.of_forall fun t v =>
      parameterDriftOperator_normalized_compatibility g (a₂ t) v)
    (by unfold timeH1ToH0; rfl)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.affineHeatLiftOfCoefficients
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.affineHeatLiftOfCoefficients target :: scope.openDecls } }

private theorem exists_unique_affineHeatLift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (C2h C2l : ℝ≥0)
    (hC2h : ∀ᵐ t ∂timeMeasure T, ‖principalOperatorHigh (ι := ι) g a₂ t‖ ≤ C2h)
    (hC2l : ∀ᵐ t ∂timeMeasure T, ‖principalOperatorLow (ι := ι) g a₂ t‖ ≤ C2l)
    (fhigh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (hsmallh : coefficientContractionBound (driftOperatorHigh (ι := ι) g a₂)
      (memLp_parameterDrift_high (ι := ι) g a₂) C2h)
    (hsmalll : coefficientContractionBound (driftOperatorLow (ι := ι) g a₂)
      (memLp_parameterDrift_low (ι := ι) g a₂ (normalizeZeroPi g)) C2l)
    (G : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((0 : ℕ) : ℝ))) T)
    (hG : affineHeatEquation (ι := ι) g ((0 : ℕ) : ℝ) hT
      (principalOperatorLow g a₂) (driftOperatorLow g a₂) (timeH1ToH0 g T fhigh) G) :
    ExistsUnique (affineHeatLift (ι := ι) g hT
      (principalOperatorHigh g a₂) (driftOperatorHigh g a₂) fhigh G) := by
  unfold affineHeatLift affineHeatEquation timeH1ToH0
  unfold affineHeatEquation at hG
  exact affineHeatLiftOfCoefficients (ι := ι) g hT a₂ C2h C2l hC2h hC2l
    fhigh hsmallh hsmalll G hG

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.exists_unique_affineHeatLift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.exists_unique_affineHeatLift target :: scope.openDecls } }

theorem exists_unique_parameterDerivativeDuhamelForcing_lift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T)
    (C2h C2l : ℝ≥0) :
    let A2h := principalOperatorHigh (ι := ι) g a₂
    let A2l := principalOperatorLow (ι := ι) g a₂
    let A1h := driftOperatorHigh (ι := ι) g a₂
    let A1l := driftOperatorLow (ι := ι) g a₂
    let hA1h : _root_.MeasureTheory.MemLp A1h 2 (timeMeasure T) := memLp_parameterDrift_high (ι := ι) g a₂
    let hA1l : _root_.MeasureTheory.MemLp A1l 2 (timeMeasure T) :=
      memLp_parameterDrift_low (ι := ι) g a₂ (normalizeZeroPi g)
    let fhigh := AddCircle.parameterDerivativeBaselineForcingLp (ι := ι) g f₀ a₂ b₂
    let G := parameterDerivativeDuhamelForcing (ι := ι) g 0 hT F
    (∀ᵐ t ∂timeMeasure T, ‖A2h t‖ ≤ C2h) →
    (∀ᵐ t ∂timeMeasure T, ‖A2l t‖ ≤ C2l) →
    coefficientContractionBound A1h hA1h C2h →
    coefficientContractionBound A1l hA1l C2l →
    weakParameterEquation g hT F f₀ a₂ b₂ →
    ExistsUnique (affineHeatLift (ι := ι) g hT A2h A1h fhigh G) := by
  intro A2h A2l A1h A1l hA1h hA1l fhigh G hC2h hC2l hsmallh hsmalll heq
  unfold coefficientContractionBound at hsmallh hsmalll
  unfold weakParameterEquation at heq
  have hlow := parameterDerivativeDuhamelForcing_affineHeatEquation g hT F f₀ a₂ b₂ heq
  have h := exists_unique_affineHeatLift (ι := ι) g hT a₂ C2h C2l hC2h hC2l
    fhigh hsmallh hsmalll G hlow
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.exists_unique_parameterDerivativeDuhamelForcing_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.exists_unique_parameterDerivativeDuhamelForcing_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.exists_unique_parameterDerivativeDuhamelForcing_lift ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.exists_unique_parameterDerivativeDuhamelForcing_lift

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry_1 : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry_1 target :: scope.openDecls } }
variable {ι : Type*} [Fintype ι]

private theorem affineHeatEquation_norm_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (a : ℝ)
    {T : ℝ} (hT : 0 < T)
    (A2 : ℝ → (PiLp 2 (fun _ : ι => TensorHs g 0 0 (a + 2))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 a))
    (hA2 : _root_.MeasureTheory.AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : ℝ≥0) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ C2)
    (A1 : ℝ → (PiLp 2 (fun _ : ι => TensorHs g 0 0 (a + 1))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 a))
    (hA1 : _root_.MeasureTheory.MemLp A1 2 (timeMeasure T))
    (fhigh FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 a)) T)
    (q : ℝ) (hq : q < 1)
    (hmargin : (C2 : ℝ) * (1 + T) + Real.sqrt (1 + T) * ‖hA1.toLp A1‖ ≤ q)
    (hf : affineHeatEquation g a hT A2 A1 fhigh FH) :
    ‖FH‖ ≤ ‖fhigh‖ / (1 - q) := by
  have hsmall := lt_of_le_of_lt hmargin hq
  have hheat : heatDuhamelVectorField (g := g) (r := 0) (s := 0) (a := a) hT 0 FH =
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0) (a := a) hT 0 FH := by
    simpa only [map_zero] using heatDuhamelVectorField_inclusion (g := g) (r := 0) (s := 0)
      (a := a) hT (tensorResolventL2_isCompactOperator g 0 0) 0 FH
  unfold affineHeatEquation at hf
  rw [hheat] at hf
  have hnorm := vector_forcing_norm_le_of_l2_coefficients (g := g) (r := 0) (s := 0)
    (a := a) hT A2 hA2 C2 hC2 A1 hA1 fhigh hsmall FH hf
  apply hnorm.trans
  apply (div_le_div_iff₀ (sub_pos.mpr hsmall) (sub_pos.mpr hq)).mpr
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hmargin 1) (norm_nonneg fhigh)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.affineHeatEquation_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.affineHeatEquation_norm_le target :: scope.openDecls } }

private theorem parameterDerivativeBaseline_affineHeatEquation_norm_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T)
    (C2h : ℝ≥0) (q : ℝ) (hq : q < 1)
    (hC2h : ∀ᵐ t ∂timeMeasure T, ‖principalOperatorHigh (ι := ι) g a₂ t‖ ≤ C2h)
    (hmargin : (C2h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      ‖(memLp_parameterDrift_high (ι := ι) g a₂).toLp (driftOperatorHigh g a₂)‖ ≤ q)
    (FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (hf : affineHeatEquation g ((1 : ℕ) : ℝ) hT
      (principalOperatorHigh g a₂) (driftOperatorHigh g a₂)
      (AddCircle.parameterDerivativeBaselineForcingLp g f₀ a₂ b₂) FH) :
    ‖FH‖ ≤ ‖AddCircle.parameterDerivativeBaselineForcingHsPi g f₀‖ *
      (‖a₂‖ + ‖b₂‖) / (1 - q) := by
  have hnorm : ‖FH‖ ≤ ‖AddCircle.parameterDerivativeBaselineForcingLp g f₀ a₂ b₂‖ / (1 - q) := by
    apply affineHeatEquation_norm_le g ((1 : ℕ) : ℝ) hT (principalOperatorHigh g a₂)
      (memLp_parameterPrincipal_high (ι := ι) g a₂ (lowerCoefficient g)).aestronglyMeasurable
      C2h hC2h (driftOperatorHigh g a₂) (memLp_parameterDrift_high g a₂)
      (AddCircle.parameterDerivativeBaselineForcingLp g f₀ a₂ b₂) FH q hq hmargin
    exact hf
  apply hnorm.trans
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hq).le
  apply AddCircle.parameterDerivativeBaselineForcingLp_norm_le

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeBaseline_affineHeatEquation_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeBaseline_affineHeatEquation_norm_le target :: scope.openDecls } }

section

variable (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
variable {T : ℝ} (hT : 0 < T)
variable (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
variable (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
variable (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
variable (b₂ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T)
variable (C2h C2l : ℝ≥0) (q : ℝ) (hq : q < 1)
variable (hC2h : ∀ᵐ t ∂timeMeasure T, ‖principalOperatorHigh (ι := ι) g a₂ t‖ ≤ C2h)
variable (hC2l : ∀ᵐ t ∂timeMeasure T, ‖principalOperatorLow (ι := ι) g a₂ t‖ ≤ C2l)
variable (hmargin : (C2h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
  ‖(memLp_parameterDrift_high (ι := ι) g a₂).toLp (driftOperatorHigh g a₂)‖ ≤ q)
variable (hsmalll : coefficientContractionBound (driftOperatorLow (ι := ι) g a₂)
  (memLp_parameterDrift_low (ι := ι) g a₂ (normalizeZeroPi g)) C2l)

private abbrev parameterDerivativeLiftWithPrincipalBounds :=
  exists_unique_parameterDerivativeDuhamelForcing_lift (ι := ι)
    g hT F f₀ a₂ b₂ C2h C2l hC2h hC2l

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeLiftWithPrincipalBounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeLiftWithPrincipalBounds target :: scope.openDecls } }

private abbrev parameterDerivativeLiftWithContractionBounds :=
  parameterDerivativeLiftWithPrincipalBounds (ι := ι) g hT F f₀ a₂ b₂ C2h C2l hC2h hC2l
    (lt_of_le_of_lt hmargin hq) hsmalll

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeLiftWithContractionBounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeLiftWithContractionBounds target :: scope.openDecls } }

include hC2h hC2l hmargin hq hsmalll in
 theorem exists_parameterDerivativeDuhamelForcing_lift_norm_le
    (heq : weakParameterEquation g hT F f₀ a₂ b₂) :
    ∃ FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T,
      affineHeatLift (ι := ι) g hT (principalOperatorHigh g a₂) (driftOperatorHigh g a₂)
        (AddCircle.parameterDerivativeBaselineForcingLp g f₀ a₂ b₂)
        (parameterDerivativeDuhamelForcing (ι := ι) g 0 hT F) FH ∧
      ‖FH‖ ≤ ‖AddCircle.parameterDerivativeBaselineForcingHsPi g f₀‖ *
        (‖a₂‖ + ‖b₂‖) / (1 - q) := by
  obtain ⟨FH, hFH, _⟩ := parameterDerivativeLiftWithContractionBounds (ι := ι)
    g hT F f₀ a₂ b₂ C2h C2l q hq hC2h hC2l hmargin hsmalll heq
  exact ⟨FH, hFH, parameterDerivativeBaseline_affineHeatEquation_norm_le
    g hT f₀ a₂ b₂ C2h q hq hC2h hmargin FH hFH.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.exists_parameterDerivativeDuhamelForcing_lift_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.exists_parameterDerivativeDuhamelForcing_lift_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.exists_parameterDerivativeDuhamelForcing_lift_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.exists_parameterDerivativeDuhamelForcing_lift_norm_le

end
end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end
