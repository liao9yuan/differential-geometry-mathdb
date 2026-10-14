import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleIteratedMultiplication
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.H0MultiplicationInclusion
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
namespace AddCircle
open _root_.AddCircle
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

open _root_.AddCircle in
def iteratedParameterDerivativeSourceHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (f₀ : TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))
    (a b : TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))
    (v : TensorHs g 0 0 ((1 + k : ℕ) : ℝ)) : TensorHs g 0 0 ((1 : ℕ) : ℝ) :=
  let Ra := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by push_cast; linarith : ((1 + k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by exact_mod_cast (show 1 ≤ k + 3 by omega) : ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let A₁ := (iteratedParameterDerivativeHs g 1 1).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + 1 ≤ k + 3 by omega) :
        ((1 + 1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
  let D := (iteratedParameterDerivativeHs g 1 (k + 2)).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + (k + 2) : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
  let P := (iteratedParameterDerivativeHs g 1 (k + 1)).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + (k + 1) ≤ k + 3 by omega) :
        ((1 + (k + 1) : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
  let q₀ := parameterSecondDerivativeHs g (k + 3) f₀
  let M := scalarHsMul g 1 (by norm_num)
  iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k (Ra a) v +
    M (A a) (D q₀) + ((k + 2 : ℕ) : ℝ) • M (A₁ a) (P q₀) + D b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.iteratedParameterDerivativeSourceHs then
    throwError "Refusing to shadow existing declaration AddCircle.iteratedParameterDerivativeSourceHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.iteratedParameterDerivativeSourceHs ``Submission.AddCircle.iteratedParameterDerivativeSourceHs

open _root_.AddCircle in
theorem memLp_iteratedParameterDerivativeSourceHs_of_continuousOn
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (f₀ : TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)) {T : ℝ}
    (a b : timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    {v : ℝ → TensorHs g 0 0 ((1 + k : ℕ) : ℝ)} (hv : ContinuousOn v (_root_.Set.Icc 0 T)) :
    _root_.MeasureTheory.MemLp (fun t => iteratedParameterDerivativeSourceHs g k f₀ (a t) (b t) (v t))
      2 (timeMeasure T) := by
  let Ra := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by push_cast; linarith : ((1 + k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by exact_mod_cast (show 1 ≤ k + 3 by omega) : ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let A₁ := (iteratedParameterDerivativeHs g 1 1).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + 1 ≤ k + 3 by omega) :
        ((1 + 1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
  let D := (iteratedParameterDerivativeHs g 1 (k + 2)).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + (k + 2) : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
  let P := (iteratedParameterDerivativeHs g 1 (k + 1)).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + (k + 1) ≤ k + 3 by omega) :
        ((1 + (k + 1) : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
  let q₀ := parameterSecondDerivativeHs g (k + 3) f₀
  let M := scalarHsMul g 1 (by norm_num)
  let R := iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  have hvm : _root_.MeasureTheory.AEStronglyMeasurable v (timeMeasure T) :=
    hv.aestronglyMeasurable measurableSet_Icc
  have hvb : ∀ᵐ t ∂timeMeasure T, ‖v t‖ ≤ C := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem (μ := _root_.MeasureTheory.MeasureSpace.volume) measurableSet_Icc] with t ht
    exact hC t ht
  have hR := R.memLp_of_bilin 2 ((Lp.memLp a).continuousLinearMap_comp Ra)
    (_root_.MeasureTheory.memLp_top_of_bound hvm C hvb)
  have hA := (Lp.memLp a).continuousLinearMap_comp ((M.flip (D q₀)).comp A)
  have hD := ((Lp.memLp a).continuousLinearMap_comp
    ((M.flip (P q₀)).comp A₁)).const_smul ((k + 2 : ℕ) : ℝ)
  have hb := (Lp.memLp b).continuousLinearMap_comp D
  exact ((hR.add hA).add hD).add hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.memLp_iteratedParameterDerivativeSourceHs_of_continuousOn then
    throwError "Refusing to shadow existing declaration AddCircle.memLp_iteratedParameterDerivativeSourceHs_of_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.memLp_iteratedParameterDerivativeSourceHs_of_continuousOn ``Submission.AddCircle.memLp_iteratedParameterDerivativeSourceHs_of_continuousOn

end AddCircle

end

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_1 : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry_1 target :: scope.openDecls } }

open _root_.AddCircle in
theorem tensorHsInclusion_iteratedParameterDerivativeSourceHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (f₀ : TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))
    (a b : TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))
    (v : TensorHs g 0 0 ((1 + k : ℕ) : ℝ)) :
    let f := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2) f₀
    let B := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let E₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let D := E₀.comp ((iteratedParameterDerivativeHs g 0 (k + 2)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((0 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))))
    let W₁ := (iteratedParameterDerivativeHs g 1 (k + 1)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((1 + (k + 1) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let Q := parameterSecondDerivativeHs g (k + 2)
    let Ra := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((1 + k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
        ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A₁ := (iteratedParameterDerivativeHs g 1 1).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show 1 + 1 ≤ k + 3 by omega) :
          ((1 + 1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let m₀ := scalarH0ContinuousMul g
    Z (iteratedParameterDerivativeSourceHs g k f₀ a b v) =
      Z (iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k (Ra a) v) +
        m₀ (C (A a)) (D (Q f)) +
        ((k + 2 : ℕ) : ℝ) • m₀ (C (A₁ a)) (Z (W₁ (Q f))) + D (B b) := by
  intro f B E₀ D W₁ Q Ra A A₁ Z C m₀
  let D₁ := (iteratedParameterDerivativeHs g 1 (k + 2)).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((1 + (k + 2) : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
  let P₁ := (iteratedParameterDerivativeHs g 1 (k + 1)).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + (k + 1) ≤ k + 3 by omega) :
        ((1 + (k + 1) : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
  let q₀ := parameterSecondDerivativeHs g (k + 3) f₀
  let M := scalarHsMul g 1 (by norm_num)
  have hQ : Q f = B q₀ := by
    exact parameterSecondDerivativeHs_tensorHsInclusion g
      (show k + 2 ≤ k + 3 by omega) f₀
  have hD (w : TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) : Z (D₁ w) = D (B w) := by
    have h := iteratedParameterDerivativeHs_tensorHsInclusion g
      (show 0 ≤ 1 by omega) (k + 2)
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((1 + (k + 2) : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)) w)
    have hh := congrArg E₀ h
    simpa only [E₀, Z, D₁, D, B, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply] using hh.symm
  have hP (w : TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) : P₁ w = W₁ (B w) := by
    simp only [P₁, W₁, B, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply]
  have hM (x y : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
      Z (M x y) = m₀ (C x) (Z y) := by
    exact tensorHsInclusion_scalarHsMul_zero g x y
  have hDq : Z (D₁ q₀) = D (Q f) := by
    rw [hD, hQ]
  have hPq : P₁ q₀ = W₁ (Q f) := by
    rw [hQ, hP]
  change Z (iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k (Ra a) v +
      M (A a) (D₁ q₀) + ((k + 2 : ℕ) : ℝ) • M (A₁ a) (P₁ q₀) + D₁ b) = _
  simp only [map_add, map_smul, hM]
  rw [hDq, hPq, hD]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.tensorHsInclusion_iteratedParameterDerivativeSourceHs then
    throwError "Refusing to shadow existing declaration AddCircle.tensorHsInclusion_iteratedParameterDerivativeSourceHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.tensorHsInclusion_iteratedParameterDerivativeSourceHs ``Submission.AddCircle.tensorHsInclusion_iteratedParameterDerivativeSourceHs

end AddCircle

end

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
namespace AddCircle
open _root_.AddCircle
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_2 : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry_2 target :: scope.openDecls } }

open _root_.AddCircle in
theorem exists_timeL2_iteratedParameterDerivativeSourceHs_of_continuousOn
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))) {T : ℝ}
    (a : timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (b : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) T)
    (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)))
    (hW : ContinuousOn W (_root_.Set.Icc 0 T)) :
    let B := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let Q := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + k : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ))).comp
        ((parameterSecondDerivativeHs g (k + 1)).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ))))
    ∃ S : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T,
      ∀ᵐ t ∂timeMeasure T, ∀ i,
        S t i = iteratedParameterDerivativeSourceHs g k (f₀ i) (a t) (b t i)
          (Q (B (f₀ i) + W t i)) := by
  intro B Q
  let R := fun t => WithLp.toLp 2 (fun i =>
    iteratedParameterDerivativeSourceHs g k (f₀ i) (a t) (b t i)
      (Q (B (f₀ i) + W t i)))
  have hR : _root_.MeasureTheory.MemLp R 2 (timeMeasure T) := by
    apply MemLp.of_eval_piLp
    intro i
    have hbi : _root_.MeasureTheory.MemLp (fun t => b t i) 2 (timeMeasure T) := (Lp.memLp b).eval_piLp i
    have hvi : ContinuousOn (fun t => Q (B (f₀ i) + W t i)) (_root_.Set.Icc 0 T) :=
      Q.continuous.comp_continuousOn
        (continuousOn_const.add ((PiLp.continuous_apply 2 _ i).comp_continuousOn hW))
    have hs := memLp_iteratedParameterDerivativeSourceHs_of_continuousOn
      g k (f₀ i) a (hbi.toLp (fun t => b t i)) hvi
    apply hs.ae_eq
    filter_upwards [hbi.coeFn_toLp] with t ht
    change iteratedParameterDerivativeSourceHs g k (f₀ i) (a t)
        ((hbi.toLp (fun t => b t i)) t) (Q (B (f₀ i) + W t i)) = _
    rw [ht]
  refine ⟨hR.toLp R, ?_⟩
  filter_upwards [hR.coeFn_toLp] with t ht
  intro i
  exact congrArg (fun z => z i) ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_timeL2_iteratedParameterDerivativeSourceHs_of_continuousOn then
    throwError "Refusing to shadow existing declaration AddCircle.exists_timeL2_iteratedParameterDerivativeSourceHs_of_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_timeL2_iteratedParameterDerivativeSourceHs_of_continuousOn ``Submission.AddCircle.exists_timeL2_iteratedParameterDerivativeSourceHs_of_continuousOn

end AddCircle

end

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
namespace AddCircle
open _root_.AddCircle
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_3 : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry_3 target :: scope.openDecls } }

open _root_.AddCircle in
theorem tensorHsInclusion_iteratedParameterDerivativeSourceHs_ae_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (f₀ : TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)) {T : ℝ}
    (a bHigh : ℝ → TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))
    (b : ℝ → TensorHs g 0 0 ((k + 2 : ℕ) : ℝ))
    (W : ℝ → TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))
    (U : ℝ → TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2)) :
    let B := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let Qlow := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + k : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ))).comp
        ((parameterSecondDerivativeHs g (k + 1)).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ))))
    let Qh := parameterSecondDerivativeHs g (k + 2)
    let Rw := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + k ≤ k + 2 by omega) :
        ((1 + k : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))
    let Ra := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
        ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A₁ := (iteratedParameterDerivativeHs g 1 1).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show 1 + 1 ≤ k + 3 by omega) :
          ((1 + 1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
    let E₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let D := E₀.comp ((iteratedParameterDerivativeHs g 0 (k + 2)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((0 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))))
    let W₁ := (iteratedParameterDerivativeHs g 1 (k + 1)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((1 + (k + 1) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let m := scalarH0ContinuousMul g
    (fun t => J (bHigh t)) =ᵐ[timeMeasure T] b →
    W =ᵐ[timeMeasure T] (fun t => K (U t)) →
    ∀ᵐ t ∂timeMeasure T,
      Z (iteratedParameterDerivativeSourceHs g k f₀ (a t) (bHigh t)
        (Qlow (B f₀ + W t))) =
      Z (iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k
        (Ra (a t)) (Rw (Qh (P f₀ + U t)))) +
        m (C (A (a t))) (D (Qh (P f₀))) +
          ((k + 2 : ℕ) : ℝ) • m (C (A₁ (a t))) (Z (W₁ (Qh (P f₀)))) + D (b t) := by
  intro B P K J Qlow Qh Rw Ra A A₁ E₀ D W₁ Z C m hb hW
  filter_upwards [hb, hW] with t hbt hWt
  have hbase : B f₀ = K (P f₀) := tensorHsInclusion_trans_apply _ _ f₀
  have hv : Qlow (B f₀ + W t) = Rw (Qh (P f₀ + U t)) := by
    rw [hbase, hWt, ← K.map_add]
    have hh := parameterSecondDerivativeHs_tensorHsInclusion g
      (show k + 1 ≤ k + 2 by omega) (P f₀ + U t)
    change Qlow (K (P f₀ + U t)) = _
    simp only [Qlow, K, Qh, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply]
    rw [hh]
    exact (tensorHsInclusion_trans_apply _ _ _).symm
  have h := tensorHsInclusion_iteratedParameterDerivativeSourceHs
    g k f₀ (a t) (bHigh t) (Qlow (B f₀ + W t))
  change Z (iteratedParameterDerivativeSourceHs g k f₀ (a t) (bHigh t)
      (Qlow (B f₀ + W t))) =
    Z (iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k
      (Ra (a t)) (Qlow (B f₀ + W t))) +
      m (C (A (a t))) (D (Qh (P f₀))) +
        ((k + 2 : ℕ) : ℝ) • m (C (A₁ (a t))) (Z (W₁ (Qh (P f₀)))) +
          D (J (bHigh t)) at h
  simpa only [hbt, hv] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.tensorHsInclusion_iteratedParameterDerivativeSourceHs_ae_eq then
    throwError "Refusing to shadow existing declaration AddCircle.tensorHsInclusion_iteratedParameterDerivativeSourceHs_ae_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.tensorHsInclusion_iteratedParameterDerivativeSourceHs_ae_eq ``Submission.AddCircle.tensorHsInclusion_iteratedParameterDerivativeSourceHs_ae_eq

end AddCircle

end

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
namespace AddCircle
open _root_.AddCircle
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_4 : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry_4 target :: scope.openDecls } }

open _root_.AddCircle in
theorem exists_timeL2_tensorHsInclusion_eq_iteratedParameterDerivativeSource
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))) {T : ℝ}
    (a : timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (bHigh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) T)
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ)))
    (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)))
    (hWc : ContinuousOn W (_root_.Set.Icc 0 T))
    (U : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2))) :
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let Qh := parameterSecondDerivativeHs g (k + 2)
    let Rw := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + k ≤ k + 2 by omega) :
        ((1 + k : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))
    let Ra := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
        ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A₁ := (iteratedParameterDerivativeHs g 1 1).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show 1 + 1 ≤ k + 3 by omega) :
          ((1 + 1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
    let E₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let D := E₀.comp ((iteratedParameterDerivativeHs g 0 (k + 2)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((0 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))))
    let W₁ := (iteratedParameterDerivativeHs g 1 (k + 1)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((1 + (k + 1) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let m := scalarH0ContinuousMul g
    (∀ᵐ t ∂timeMeasure T, ∀ i, J (bHigh t i) = b t i) →
    (∀ᵐ t ∂timeMeasure T, ∀ i, W t i = K (U t i)) →
    ∃ S : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T,
      ∀ᵐ t ∂timeMeasure T, ∀ i, Z (S t i) =
      Z (iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k
        (Ra (a t)) (Rw (Qh (P (f₀ i) + U t i)))) +
        m (C (A (a t))) (D (Qh (P (f₀ i)))) +
          ((k + 2 : ℕ) : ℝ) • m (C (A₁ (a t))) (Z (W₁ (Qh (P (f₀ i))))) + D (b t i) := by
  intro P K J Qh Rw Ra A A₁ E₀ D W₁ Z C m hb hW
  let B := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ) + 2)
  let Qlow := (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by push_cast; linarith : ((1 + k : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ))).comp
      ((parameterSecondDerivativeHs g (k + 1)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ))))
  obtain ⟨S, hS⟩ := exists_timeL2_iteratedParameterDerivativeSourceHs_of_continuousOn
    g k f₀ a bHigh W hWc
  refine ⟨S, ?_⟩
  have hcoordinate : ∀ i, ∀ᵐ t ∂timeMeasure T,
      Z (iteratedParameterDerivativeSourceHs g k (f₀ i) (a t) (bHigh t i)
        (Qlow (B (f₀ i) + W t i))) =
      Z (iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k
        (Ra (a t)) (Rw (Qh (P (f₀ i) + U t i)))) +
        m (C (A (a t))) (D (Qh (P (f₀ i)))) +
          ((k + 2 : ℕ) : ℝ) • m (C (A₁ (a t))) (Z (W₁ (Qh (P (f₀ i))))) + D (b t i) := by
    intro i
    apply tensorHsInclusion_iteratedParameterDerivativeSourceHs_ae_eq
      g k (f₀ i) a (fun t => bHigh t i) (fun t => b t i)
        (fun t => W t i) (fun t => U t i)
    · filter_upwards [hb] with t ht
      exact ht i
    · filter_upwards [hW] with t ht
      exact ht i
  have hall := ae_all_iff.mpr hcoordinate
  filter_upwards [hS, hall] with t ht hh
  intro i
  rw [ht i]
  exact hh i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_timeL2_tensorHsInclusion_eq_iteratedParameterDerivativeSource then
    throwError "Refusing to shadow existing declaration AddCircle.exists_timeL2_tensorHsInclusion_eq_iteratedParameterDerivativeSource"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_timeL2_tensorHsInclusion_eq_iteratedParameterDerivativeSource ``Submission.AddCircle.exists_timeL2_tensorHsInclusion_eq_iteratedParameterDerivativeSource

end AddCircle

end
