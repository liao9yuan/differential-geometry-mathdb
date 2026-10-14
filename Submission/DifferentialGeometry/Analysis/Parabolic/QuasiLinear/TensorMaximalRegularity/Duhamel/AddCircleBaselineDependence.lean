import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleLinearizedBaseline
import Submission.DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpOperators

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

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

open _root_.AddCircle in
private def parameterDerivativeBaselineCoefficientL
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)) →L[ℝ]
      TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
  let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
  let D := parameterDerivativeHs g 1
  let Q := K.comp (parameterSecondDerivativeHs g 2)
  let m := scalarHsMul g 1 (by norm_num)
  ContinuousLinearMap.flip
    ((ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi fun _ : ι =>
        ((D.comp Q).precomp _).comp (m.comp J) +
          ((J.comp Q).precomp _).comp (m.comp D)))

run_cmd do
  let target := ``Submission.AddCircle.parameterDerivativeBaselineCoefficientL
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.parameterDerivativeBaselineCoefficientL target :: scope.openDecls } }

open _root_.AddCircle in
theorem tendsto_parameterDerivativeBaselineForcingLp
    {Ω X ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : _root_.MeasureTheory.Measure Ω} {p : ℝ≥0∞} [Fact (1 ≤ p)] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (f0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (a : X → _root_.MeasureTheory.Lp (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) p μ)
    (a0 : _root_.MeasureTheory.Lp (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) p μ)
    (b : X → _root_.MeasureTheory.Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) p μ)
    (b0 : _root_.MeasureTheory.Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) p μ)
    (hf : _root_.Filter.Tendsto f l (𝓝 f0)) (ha : _root_.Filter.Tendsto a l (𝓝 a0)) (hb : _root_.Filter.Tendsto b l (𝓝 b0)) :
    _root_.Filter.Tendsto (fun x => parameterDerivativeBaselineForcingLp g (f x) (a x) (b x)) l
      (𝓝 (parameterDerivativeBaselineForcingLp g f0 a0 b0)) := by
  let A := parameterDerivativeBaselineCoefficientL (ι := ι) g
  let D := ContinuousLinearMap.piLpMap 2 (fun _ : ι => parameterDerivativeHs g 1)
  have heq (f' : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
      (a' : _root_.MeasureTheory.Lp (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) p μ)
      (b' : _root_.MeasureTheory.Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) p μ) :
      parameterDerivativeBaselineForcingLp g f' a' b' =
        A.compLpL₂ p μ f' a' + D.compLpL p μ b' := by
    apply Lp.ext
    filter_upwards [parameterDerivativeBaselineForcingLp_ae g f' a' b',
      Lp.coeFn_add (A.compLpL₂ p μ f' a') (D.compLpL p μ b'),
      (A f').coeFn_compLp a', D.coeFn_compLpL b'] with t ht hadd hA hD
    change A.compLpL₂ p μ f' a' t = A f' (a' t) at hA
    rw [ht, hadd, Pi.add_apply, hA, hD]
    apply PiLp.ext
    intro i
    rfl
  have hA := ((A.compLpL₂ p μ).continuous₂.tendsto _).comp (hf.prodMk_nhds ha)
  have hD := (D.compLpL p μ).continuous.tendsto b0 |>.comp hb
  have h := hA.add hD
  change _root_.Filter.Tendsto (fun x => A.compLpL₂ p μ (f x) (a x) + D.compLpL p μ (b x)) l
    (𝓝 (A.compLpL₂ p μ f0 a0 + D.compLpL p μ b0)) at h
  simpa only [heq] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.tendsto_parameterDerivativeBaselineForcingLp then
    throwError "Refusing to shadow existing declaration AddCircle.tendsto_parameterDerivativeBaselineForcingLp"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.tendsto_parameterDerivativeBaselineForcingLp ``Submission.AddCircle.tendsto_parameterDerivativeBaselineForcingLp

end AddCircle

end
