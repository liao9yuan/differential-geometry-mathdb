import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleIteratedDerivative
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivativeLift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
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
theorem exists_continuousOn_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ)
    {s : Set X} {σ : ℝ} (hσ : σ ≤ ((n + 1 : ℕ) : ℝ))
    (u : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 + m : ℕ) : ℝ)))
    (v : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 : ℕ) : ℝ)))
    (hu : ContinuousOn u s) (hv : ContinuousOn v s)
    (h : ∀ x ∈ s, ∀ i : ι,
      tensorHsInclusion hσ (iteratedParameterDerivativeHs g (n + 1) m (u x i)) =
        tensorHsInclusion (hσ.trans (by push_cast; linarith :
          ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ))) (v x i)) :
    ∃ w : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 + m : ℕ) : ℝ)),
      ContinuousOn w s ∧ ∀ x ∈ s,
        ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith :
              ((n + 1 + m : ℕ) : ℝ) ≤ ((n + 2 + m : ℕ) : ℝ))) (w x) = u x := by
  induction m with
  | zero =>
      refine ⟨v, hv, ?_⟩
      intro x hx
      apply PiLp.ext
      intro i
      apply tensorHsInclusion_injective hσ
      simpa only [ContinuousLinearMap.piLpMap_apply,
        ← tensorHsInclusion_trans_apply, iteratedParameterDerivativeHs_zero,
        ContinuousLinearMap.id_apply] using (h x hx i).symm
  | succ m ih =>
      let P :=
        ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        (parameterDerivativeHs g (n + 1 + m)).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith :
              ((n + 1 + m : ℕ) : ℝ) + 1 ≤ ((n + 1 + (m + 1) : ℕ) : ℝ))))
      obtain ⟨du, hdu, hduproj⟩ := ih (fun x => P (u x))
        (P.continuous.comp_continuousOn hu) (by
          intro x hx i
          simpa only [P, ContinuousLinearMap.piLpMap_apply,
            ContinuousLinearMap.comp_apply, iteratedParameterDerivativeHs_succ_apply]
            using h x hx i)
      let J :=
        ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith :
            ((n + m : ℕ) : ℝ) + 2 ≤ ((n + 1 + (m + 1) : ℕ) : ℝ)))
      let K :=
        ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith :
            ((n + m : ℕ) : ℝ) + 2 ≤ ((n + 2 + m : ℕ) : ℝ)))
      obtain ⟨w, hw, hwproj⟩ :=
        exists_continuousOn_tensorHsInclusion_eq_of_parameterDerivative_lift
          g (n + m) (σ := ((n + 1 + m : ℕ) : ℝ)) (by push_cast; linarith)
          (fun x => J (u x)) (fun x => K (du x))
          (J.continuous.comp_continuousOn hu) (K.continuous.comp_continuousOn hdu) (by
            intro x hx i
            have hi := congrArg (fun z => z i) (hduproj x hx)
            simp only [P, ContinuousLinearMap.piLpMap_apply,
              ContinuousLinearMap.comp_apply] at hi
            simp only [J, K, ContinuousLinearMap.piLpMap_apply,
              ← tensorHsInclusion_trans_apply]
            have hc := parameterDerivativeHs_tensorHsInclusion g
              (show n + m + 1 ≤ n + 1 + m by omega)
              (tensorHsInclusion (g := g) (r := 0) (s := 0)
                (by push_cast; linarith :
                  ((n + 1 + m : ℕ) : ℝ) + 1 ≤ ((n + 1 + (m + 1) : ℕ) : ℝ))
                (u x i))
            have hp := congrArg (tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by push_cast; linarith :
                ((n + 1 + m : ℕ) : ℝ) ≤ ((n + m + 1 : ℕ) : ℝ))) hc
            simp only [← tensorHsInclusion_trans_apply,
              tensorHsInclusion_refl_apply] at hp
            exact hp.trans hi.symm)
      let L :=
        ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith :
            ((n + 2 + (m + 1) : ℕ) : ℝ) ≤ ((n + m + 1 : ℕ) : ℝ) + 2))
      refine ⟨fun x => L (w x), L.continuous.comp_continuousOn hw, ?_⟩
      intro x hx
      apply PiLp.ext
      intro i
      have hi := congrArg (fun z => z i) (hwproj x hx)
      have hp := congrArg (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((n + 1 + (m + 1) : ℕ) : ℝ) ≤ ((n + m : ℕ) : ℝ) + 2)) hi
      simpa only [J, L, ContinuousLinearMap.piLpMap_apply,
        ← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply] using hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_continuousOn_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift then
    throwError "Refusing to shadow existing declaration AddCircle.exists_continuousOn_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_continuousOn_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift ``Submission.AddCircle.exists_continuousOn_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift

open _root_.AddCircle in
private def derivativePredecessor
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 + (m + 1) : ℕ) : ℝ))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 + m : ℕ) : ℝ))) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    (parameterDerivativeHs g (n + 1 + m)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((n + 1 + m : ℕ) : ℝ) + 1 ≤ ((n + 1 + (m + 1) : ℕ) : ℝ))))

run_cmd do
  let target := ``Submission.AddCircle.derivativePredecessor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.derivativePredecessor target :: scope.openDecls } }

open _root_.AddCircle in
private def derivativePredecessorProjection
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 2 + m : ℕ) : ℝ))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 + m : ℕ) : ℝ))) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show n + 1 + m ≤ n + 2 + m by omega) :
        ((n + 1 + m : ℕ) : ℝ) ≤ ((n + 2 + m : ℕ) : ℝ)))

run_cmd do
  let target := ``Submission.AddCircle.derivativePredecessorProjection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.derivativePredecessorProjection target :: scope.openDecls } }

open _root_.AddCircle in
private def derivativeStateNormalization
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 + (m + 1) : ℕ) : ℝ))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + m : ℕ) : ℝ) + 2)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((n + m : ℕ) : ℝ) + 2 ≤ ((n + 1 + (m + 1) : ℕ) : ℝ)))

run_cmd do
  let target := ``Submission.AddCircle.derivativeStateNormalization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.derivativeStateNormalization target :: scope.openDecls } }

open _root_.AddCircle in
private def derivativePredecessorNormalization
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 2 + m : ℕ) : ℝ))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + m : ℕ) : ℝ) + 2)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((n + m : ℕ) : ℝ) + 2 ≤ ((n + 2 + m : ℕ) : ℝ)))

run_cmd do
  let target := ``Submission.AddCircle.derivativePredecessorNormalization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.derivativePredecessorNormalization target :: scope.openDecls } }

open _root_.AddCircle in
private def derivativeReconstructionNormalization
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + m + 1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 2 + (m + 1) : ℕ) : ℝ))) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((n + 2 + (m + 1) : ℕ) : ℝ) ≤ ((n + m + 1 : ℕ) : ℝ) + 2))

run_cmd do
  let target := ``Submission.AddCircle.derivativeReconstructionNormalization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.derivativeReconstructionNormalization target :: scope.openDecls } }

open _root_.AddCircle in
private def derivativeReconstructionProjection
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + m + 1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + m : ℕ) : ℝ) + 2)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((n + m : ℕ) : ℝ) + 2 ≤ ((n + m + 1 : ℕ) : ℝ) + 2))

run_cmd do
  let target := ``Submission.AddCircle.derivativeReconstructionProjection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.derivativeReconstructionProjection target :: scope.openDecls } }

open _root_.AddCircle in
private def derivativeStateProjection
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 2 + (m + 1) : ℕ) : ℝ))) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 + (m + 1) : ℕ) : ℝ))) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show n + 1 + (m + 1) ≤ n + 2 + (m + 1) by omega) :
        ((n + 1 + (m + 1) : ℕ) : ℝ) ≤ ((n + 2 + (m + 1) : ℕ) : ℝ)))

run_cmd do
  let target := ``Submission.AddCircle.derivativeStateProjection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.derivativeStateProjection target :: scope.openDecls } }

open _root_.AddCircle in
private theorem parameterDerivative_compLpL_eq_of_predecessor_projection
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ)
    {T : ℝ}
    (u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 + (m + 1) : ℕ) : ℝ))) T)
    (wD : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 + m : ℕ) : ℝ))) T)
    (hwD : (derivativePredecessorProjection g n m).compLpL 2 (timeMeasure T) wD =
      (derivativePredecessor g n m).compLpL 2 (timeMeasure T) u) : ∀ᵐ t ∂timeMeasure T, ∀ i : ι,
      tensorHsInclusion
          (by exact_mod_cast (show n + 1 + m ≤ n + m + 1 by omega) :
            ((n + 1 + m : ℕ) : ℝ) ≤ ((n + m + 1 : ℕ) : ℝ))
          (parameterDerivativeHs g (n + m + 1)
            (tensorHsInclusion (by push_cast; linarith :
              ((n + m + 1 : ℕ) : ℝ) + 1 ≤ ((n + m : ℕ) : ℝ) + 2)
                (((derivativeStateNormalization g n m).compLpL 2 (timeMeasure T) u) t i))) =
        tensorHsInclusion (by push_cast; linarith :
          ((n + 1 + m : ℕ) : ℝ) ≤ ((n + m : ℕ) : ℝ) + 2)
          (((derivativePredecessorNormalization g n m).compLpL 2 (timeMeasure T) wD) t i) := by
  let P := derivativePredecessor (ι := ι) g n m
  let du : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 + m : ℕ) : ℝ)))) T :=
    P.compLpL 2 (timeMeasure T) u
  let K := derivativePredecessorProjection (ι := ι) g n m
  change K.compLpL 2 (timeMeasure T) wD = du at hwD
  let A := derivativeStateNormalization (ι := ι) g n m
  let B := derivativePredecessorNormalization (ι := ι) g n m
  let U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + m : ℕ) : ℝ) + 2))) T :=
    A.compLpL 2 (timeMeasure T) u
  let V : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + m : ℕ) : ℝ) + 2))) T :=
    B.compLpL 2 (timeMeasure T) wD
  have hstep : ∀ᵐ t ∂timeMeasure T, ∀ i : ι,
      tensorHsInclusion
          (by exact_mod_cast (show n + 1 + m ≤ n + m + 1 by omega) :
            ((n + 1 + m : ℕ) : ℝ) ≤ ((n + m + 1 : ℕ) : ℝ))
          (parameterDerivativeHs g (n + m + 1)
            (tensorHsInclusion (by push_cast; linarith :
              ((n + m + 1 : ℕ) : ℝ) + 1 ≤ ((n + m : ℕ) : ℝ) + 2)
                (U t i))) =
        tensorHsInclusion (by push_cast; linarith :
          ((n + 1 + m : ℕ) : ℝ) ≤ ((n + m : ℕ) : ℝ) + 2) (V t i) := by
    filter_upwards [A.coeFn_compLpL u, B.coeFn_compLpL wD,
      K.coeFn_compLpL wD, P.coeFn_compLpL u] with t hA hB hK hP
    intro i
    have hEq : K (wD t) = P (u t) := by
      rw [← hK, hwD]
      exact hP
    have hi := congrArg (fun z => z i) hEq
    change U t = A (u t) at hA
    change V t = B (wD t) at hB
    rw [hA, hB]
    simp only [A, B, K, P, derivativeStateNormalization, derivativePredecessorNormalization,
      derivativePredecessorProjection, derivativePredecessor, ContinuousLinearMap.piLpMap_apply,
      ContinuousLinearMap.comp_apply, ← tensorHsInclusion_trans_apply] at hi ⊢
    have hc := parameterDerivativeHs_tensorHsInclusion g
      (show n + m + 1 ≤ n + 1 + m by omega)
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((n + 1 + m : ℕ) : ℝ) + 1 ≤ ((n + 1 + (m + 1) : ℕ) : ℝ))
        (u t i))
    have hp := congrArg (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((n + 1 + m : ℕ) : ℝ) ≤ ((n + m + 1 : ℕ) : ℝ))) hc
    simp only [← tensorHsInclusion_trans_apply,
      tensorHsInclusion_refl_apply] at hp
    exact hp.trans hi.symm
  exact hstep

run_cmd do
  let target := ``Submission.AddCircle.parameterDerivative_compLpL_eq_of_predecessor_projection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.parameterDerivative_compLpL_eq_of_predecessor_projection target :: scope.openDecls } }

open _root_.AddCircle in
private theorem derivativeStateProjection_compLpL_eq
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ)
    {T : ℝ}
    (u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 + (m + 1) : ℕ) : ℝ))) T)
    (W : timeL2
      (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + m + 1 : ℕ) : ℝ) + 2))) T)
    (hW : (derivativeReconstructionProjection g n m).compLpL 2 (timeMeasure T) W =
      (derivativeStateNormalization g n m).compLpL 2 (timeMeasure T) u) :
    (derivativeStateProjection g n m).compLpL 2 (timeMeasure T)
      ((derivativeReconstructionNormalization g n m).compLpL 2 (timeMeasure T) W) = u := by
  let A := derivativeStateNormalization (ι := ι) g n m
  let C := derivativeReconstructionNormalization (ι := ι) g n m
  let J := derivativeReconstructionProjection (ι := ι) g n m
  let R := derivativeStateProjection (ι := ι) g n m
  change J.compLpL 2 (timeMeasure T) W = A.compLpL 2 (timeMeasure T) u at hW
  change R.compLpL 2 (timeMeasure T) (C.compLpL 2 (timeMeasure T) W) = u
  apply Lp.ext
  filter_upwards [R.coeFn_compLpL (C.compLpL 2 (timeMeasure T) W),
    C.coeFn_compLpL W, J.coeFn_compLpL W, A.coeFn_compLpL u]
      with t hR hC hJ hA
  rw [hR, hC]
  apply PiLp.ext
  intro i
  apply tensorHsInclusion_injective
    (by push_cast; linarith :
      ((n + m : ℕ) : ℝ) + 2 ≤ ((n + 1 + (m + 1) : ℕ) : ℝ))
  have heq : J (W t) = A (u t) := by
    rw [← hJ, hW]
    exact hA
  have hi := congrArg (fun z => z i) heq
  simpa only [R, C, J, A, derivativeStateProjection, derivativeReconstructionNormalization,
      derivativeReconstructionProjection, derivativeStateNormalization,
      ContinuousLinearMap.piLpMap_apply,
    ← tensorHsInclusion_trans_apply] using hi

run_cmd do
  let target := ``Submission.AddCircle.derivativeStateProjection_compLpL_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.derivativeStateProjection_compLpL_eq target :: scope.openDecls } }

open _root_.AddCircle in
private theorem exists_timeL2_tensorHsInclusion_eq_of_derivative_predecessor_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ)
    {T : ℝ}
    (u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 + (m + 1) : ℕ) : ℝ))) T)
    (wD : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 + m : ℕ) : ℝ))) T)
    (hwD : (derivativePredecessorProjection g n m).compLpL 2 (timeMeasure T) wD =
      (derivativePredecessor g n m).compLpL 2 (timeMeasure T) u) :
    ∃ w : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 + (m + 1) : ℕ) : ℝ))) T,
      (derivativeStateProjection g n m).compLpL 2 (timeMeasure T) w = u := by
  let A := derivativeStateNormalization (ι := ι) g n m
  let B := derivativePredecessorNormalization (ι := ι) g n m
  let U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + m : ℕ) : ℝ) + 2))) T :=
    A.compLpL 2 (timeMeasure T) u
  let V : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + m : ℕ) : ℝ) + 2))) T :=
    B.compLpL 2 (timeMeasure T) wD
  have hstep := parameterDerivative_compLpL_eq_of_predecessor_projection g n m u wD hwD
  obtain ⟨W, hW⟩ := exists_timeL2_tensorHsInclusion_eq_of_parameterDerivative_lift
    g (n + m)
    (by exact_mod_cast (show n + 1 + m ≤ n + m + 1 by omega) :
            ((n + 1 + m : ℕ) : ℝ) ≤ ((n + m + 1 : ℕ) : ℝ)) U V hstep
  refine ⟨(derivativeReconstructionNormalization g n m).compLpL
    2 (timeMeasure T) W, ?_⟩
  exact derivativeStateProjection_compLpL_eq g n m u W hW

run_cmd do
  let target := ``Submission.AddCircle.exists_timeL2_tensorHsInclusion_eq_of_derivative_predecessor_lift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.exists_timeL2_tensorHsInclusion_eq_of_derivative_predecessor_lift target :: scope.openDecls } }


open _root_.AddCircle in
theorem exists_timeL2_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ)
    {T σ : ℝ} (hσ : σ ≤ ((n + 1 : ℕ) : ℝ))
    (u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 + m : ℕ) : ℝ))) T)
    (v : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 : ℕ) : ℝ))) T)
    (h : ∀ᵐ t ∂timeMeasure T, ∀ i : ι,
      tensorHsInclusion hσ (iteratedParameterDerivativeHs g (n + 1) m (u t i)) =
        tensorHsInclusion (hσ.trans (by exact_mod_cast (show n + 1 ≤ n + 2 by omega) :
          ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ)))
          (v t i)) :
    ∃ w : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 + m : ℕ) : ℝ))) T,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by exact_mod_cast (show n + 1 + m ≤ n + 2 + m by omega) :
            ((n + 1 + m : ℕ) : ℝ) ≤ ((n + 2 + m : ℕ) : ℝ)))).compLpL
            2 (timeMeasure T) w = u := by
  induction m with
  | zero =>
      refine ⟨v, ?_⟩
      let K : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 2 : ℕ) : ℝ))) →L[ℝ]
          PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ))) :=
        ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by exact_mod_cast (show n + 1 ≤ n + 2 by omega) :
          ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ)))
      change K.compLpL 2 (timeMeasure T) v = u
      apply Lp.ext
      filter_upwards [K.coeFn_compLpL v, h] with t ht hh
      rw [ht]
      apply PiLp.ext
      intro i
      apply tensorHsInclusion_injective hσ
      simpa only [K, ContinuousLinearMap.piLpMap_apply,
        ← tensorHsInclusion_trans_apply, iteratedParameterDerivativeHs_zero,
        ContinuousLinearMap.id_apply] using (hh i).symm
  | succ m ih =>
      let P : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 + (m + 1) : ℕ) : ℝ))) →L[ℝ]
          PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 + m : ℕ) : ℝ))) :=
        ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        (parameterDerivativeHs g (n + 1 + m)).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith :
              ((n + 1 + m : ℕ) : ℝ) + 1 ≤ ((n + 1 + (m + 1) : ℕ) : ℝ))))
      let du : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 + m : ℕ) : ℝ)))) T :=
        P.compLpL 2 (timeMeasure T) u
      have hdu : ∀ᵐ t ∂timeMeasure T, ∀ i : ι,
          tensorHsInclusion hσ
              (iteratedParameterDerivativeHs g (n + 1) m (du t i)) =
            tensorHsInclusion
              (hσ.trans (by exact_mod_cast (show n + 1 ≤ n + 2 by omega) :
          ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ))) (v t i) := by
        filter_upwards [P.coeFn_compLpL u, h] with t ht hh
        intro i
        change du t = P (u t) at ht
        rw [ht]
        simpa only [P, ContinuousLinearMap.piLpMap_apply,
          ContinuousLinearMap.comp_apply, iteratedParameterDerivativeHs_succ_apply]
          using hh i
      obtain ⟨wD, hwD⟩ := ih du hdu
      simpa only [derivativeStateProjection] using
        exists_timeL2_tensorHsInclusion_eq_of_derivative_predecessor_lift
          g n m u wD hwD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_timeL2_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift then
    throwError "Refusing to shadow existing declaration AddCircle.exists_timeL2_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_timeL2_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift ``Submission.AddCircle.exists_timeL2_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift

end AddCircle
