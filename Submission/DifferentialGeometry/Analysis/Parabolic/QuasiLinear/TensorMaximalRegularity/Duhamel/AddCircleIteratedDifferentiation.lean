import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleDifferentiation
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.LinearTransport
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleIteratedDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

variable {ι : Type*} [Fintype ι]

def iteratedParameterDerivativeDuhamelForcing
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m + n : ℕ) : ℝ))) T) :
    timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T :=
  let D := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    (AddCircle.iteratedParameterDerivativeHs g n m).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((n + m : ℕ) : ℝ) ≤ ((m + n : ℕ) : ℝ))))
  let Dh := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ))).comp
        ((AddCircle.iteratedParameterDerivativeHs g (n + 2) m).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith :
              ((n + 2 + m : ℕ) : ℝ) ≤ ((m + n : ℕ) : ℝ) + 2))))
  let U := maximalRegularityDuhamelVectorField
    (g := g) (r := 0) (s := 0) (a := ((m + n : ℕ) : ℝ)) hT 0 F
  let Lh := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((m + n : ℕ) : ℝ))
  let Ll := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ))
  D.compLpL 2 (timeMeasure T) F +
    (D.comp Lh - Ll.comp Dh).compLpL 2 (timeMeasure T) U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.iteratedParameterDerivativeDuhamelForcing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.iteratedParameterDerivativeDuhamelForcing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.iteratedParameterDerivativeDuhamelForcing ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.iteratedParameterDerivativeDuhamelForcing

theorem iteratedParameterDerivative_duhamel_vector_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m + n : ℕ) : ℝ))) T) :
    let D := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      (AddCircle.iteratedParameterDerivativeHs g n m).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith :
            ((n + m : ℕ) : ℝ) ≤ ((m + n : ℕ) : ℝ))))
    let Dh := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ))).comp
          ((AddCircle.iteratedParameterDerivativeHs g (n + 2) m).comp
            (tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by push_cast; linarith :
                ((n + 2 + m : ℕ) : ℝ) ≤ ((m + n : ℕ) : ℝ) + 2))))
    let U := maximalRegularityDuhamelVectorField
      (g := g) (r := 0) (s := 0) (a := ((m + n : ℕ) : ℝ)) hT 0 F
    let G := iteratedParameterDerivativeDuhamelForcing g n m hT F
    Dh.compLpL 2 (timeMeasure T) U =
        maximalRegularityDuhamelVectorField
          (g := g) (r := 0) (s := 0) (a := n) hT 0 G ∧
      (maximalRegularityDuhamelVectorMap
        (g := g) (r := 0) (s := 0) (a := n) hT 0 G).initial = 0 ∧
      ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
        (maximalRegularityDuhamelVectorMap
          (g := g) (r := 0) (s := 0) (a := n) hT 0 G).toFun t =
          D ((maximalRegularityDuhamelVectorMap
            (g := g) (r := 0) (s := 0)
            (a := ((m + n : ℕ) : ℝ)) hT 0 F).toFun t) := by
  intro D Dh U G
  have hc := tensorResolventL2_isCompactOperator
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0
  exact duhamel_vector_comp_zero_eq (ι := ι) (E := ℝ) (H := ℝ)
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0)
    (a := n) (b := ((m + n : ℕ) : ℝ)) hT hc D Dh (by
      apply ContinuousLinearMap.ext
      intro f
      apply PiLp.ext
      intro i
      simp only [D, Dh, ContinuousLinearMap.comp_apply, ContinuousLinearMap.piLpMap_apply]
      have hi := AddCircle.iteratedParameterDerivativeHs_tensorHsInclusion g
        (show n ≤ n + 2 by omega) m
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith :
            ((n + 2 + m : ℕ) : ℝ) ≤ ((m + n : ℕ) : ℝ) + 2) (f i))
      simpa only [← tensorHsInclusion_trans_apply] using hi.symm) F

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.iteratedParameterDerivative_duhamel_vector_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.iteratedParameterDerivative_duhamel_vector_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.iteratedParameterDerivative_duhamel_vector_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.iteratedParameterDerivative_duhamel_vector_eq

theorem iteratedParameterDerivativeDuhamelForcing_one
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T) :
    iteratedParameterDerivativeDuhamelForcing g 0 1 hT F =
      parameterDerivativeDuhamelForcing g 0 hT F := by
  simp only [iteratedParameterDerivativeDuhamelForcing, parameterDerivativeDuhamelForcing,
    AddCircle.iteratedParameterDerivativeHs, AddCircle.parameterDerivativeHsPi,
    ContinuousLinearMap.piLpMap_comp, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_assoc, ← tensorHsInclusion_trans,
    tensorHsInclusion_refl, ContinuousLinearMap.comp_id, Nat.add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.iteratedParameterDerivativeDuhamelForcing_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.iteratedParameterDerivativeDuhamelForcing_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.iteratedParameterDerivativeDuhamelForcing_one ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.iteratedParameterDerivativeDuhamelForcing_one

open scoped _root_.Topology in
private theorem tendsto_iteratedParameterDerivativeDuhamelForcing
    {ι P : Type*} [Fintype ι] {l : Filter P}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m + n : ℕ) : ℝ))) T)
    (F : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m + n : ℕ) : ℝ))) T)
    (hF : _root_.Filter.Tendsto F l (𝓝 F₀)) :
    _root_.Filter.Tendsto (fun p => iteratedParameterDerivativeDuhamelForcing g n m hT (F p)) l
      (𝓝 (iteratedParameterDerivativeDuhamelForcing g n m hT F₀)) := by
  let S := maximalRegularityVectorFieldL
    (ι := ι) (g := g) (r := 0) (s := 0) ((m + n : ℕ) : ℝ) hT.le
  have hS : _root_.Filter.Tendsto (fun p => S (F p)) l (𝓝 (S F₀)) :=
    (S.continuous.tendsto F₀).comp hF
  have heq (f : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0
      ((m + n : ℕ) : ℝ))) T) :
      S f = maximalRegularityDuhamelVectorField hT 0 f :=
    maximalRegularityVectorFieldL_eq_duhamel hT f
  have hU : _root_.Filter.Tendsto (fun p => maximalRegularityDuhamelVectorField hT 0 (F p)) l
      (𝓝 (maximalRegularityDuhamelVectorField hT 0 F₀)) := by
    simpa only [heq] using hS
  unfold iteratedParameterDerivativeDuhamelForcing
  dsimp only
  apply Filter.Tendsto.add
  · exact ((ContinuousLinearMap.continuous _).tendsto F₀).comp hF
  · exact ((ContinuousLinearMap.continuous _).tendsto
      (maximalRegularityDuhamelVectorField hT 0 F₀)).comp hU

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tendsto_iteratedParameterDerivativeDuhamelForcing
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tendsto_iteratedParameterDerivativeDuhamelForcing target :: scope.openDecls } }

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
