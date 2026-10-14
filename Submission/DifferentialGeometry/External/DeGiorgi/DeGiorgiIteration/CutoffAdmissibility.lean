-- Modified 2026-04-28: updated internal import paths for project namespace
import Submission.DifferentialGeometry.External.DeGiorgi.PositivePart
import Submission.DifferentialGeometry.External.DeGiorgi.BallExtension
import Submission.DifferentialGeometry.External.DeGiorgi.WeakFormulation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# De Giorgi Iteration: Cutoff Admissibility

This module packages the truncation and cutoff-admissibility layer used at the
start of the De Giorgi iteration.
-/

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter
open scoped _root_.NNReal

namespace DeGiorgi

/-- Positive-part truncation `(u-k)₊`. -/
def positivePartSub {α : Type*} (u : α → ℝ) (k : ℝ) : α → ℝ :=
  fun x => _root_.Max.max (u x - k) 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.positivePartSub then
    throwError "Refusing to shadow existing declaration DeGiorgi.positivePartSub"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.positivePartSub ``Submission.DeGiorgi.positivePartSub

lemma positivePartSub_nonneg {α : Type*} {u : α → ℝ} {k : ℝ} {x : α} :
    0 ≤ positivePartSub u k x := by
  simp [positivePartSub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.positivePartSub_nonneg then
    throwError "Refusing to shadow existing declaration DeGiorgi.positivePartSub_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.positivePartSub_nonneg ``Submission.DeGiorgi.positivePartSub_nonneg

lemma positivePartSub_sq_ge_gap_sq_of_lt
    {α : Type*} {u : α → ℝ} {θ lam : ℝ} {x : α}
    (hθl : θ < lam) (hxl : lam < u x) :
    (lam - θ) ^ 2 ≤ |positivePartSub u θ x| ^ 2 := by
  have hgap_pos : 0 < lam - θ := sub_pos.mpr hθl
  have hpos : 0 < u x - θ := by linarith
  have hle : lam - θ ≤ u x - θ := by linarith
  have hpp : positivePartSub u θ x = u x - θ := by
    simp [positivePartSub, max_eq_left (le_of_lt hpos)]
  rw [hpp, abs_of_nonneg (le_of_lt hpos)]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.positivePartSub_sq_ge_gap_sq_of_lt then
    throwError "Refusing to shadow existing declaration DeGiorgi.positivePartSub_sq_ge_gap_sq_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.positivePartSub_sq_ge_gap_sq_of_lt ``Submission.DeGiorgi.positivePartSub_sq_ge_gap_sq_of_lt

section CutoffAdmissibility

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-- Generalized De Giorgi cutoff test `η² (u-k)₊` for an arbitrary scalar
cutoff `η`. -/
def deGiorgiCutoffTestGeneral
    (η u : E → ℝ) (k : ℝ) : E → ℝ :=
  fun x => η x * (η x * positivePartSub u k x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.deGiorgiCutoffTestGeneral then
    throwError "Refusing to shadow existing declaration DeGiorgi.deGiorgiCutoffTestGeneral"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.deGiorgiCutoffTestGeneral ``Submission.DeGiorgi.deGiorgiCutoffTestGeneral

omit [NeZero d] in
lemma eq_zero_of_not_mem_tsupport
    {f : E → ℝ} {x : E} (hx : x ∉ tsupport f) : f x = 0 := by
  by_contra hfx
  exact hx (subset_tsupport f (Function.mem_support.mpr hfx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.eq_zero_of_not_mem_tsupport then
    throwError "Refusing to shadow existing declaration DeGiorgi.eq_zero_of_not_mem_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.eq_zero_of_not_mem_tsupport ``Submission.DeGiorgi.eq_zero_of_not_mem_tsupport

omit [NeZero d] in
lemma hasCompactSupport_of_tsupport_subset_ball
    {f : E → ℝ} {x₀ : E} {s : ℝ}
    (hsub : tsupport f ⊆ Metric.ball x₀ s) :
    HasCompactSupport f := by
  apply HasCompactSupport.intro' (_root_.ProperSpace.isCompact_closedBall x₀ s) _root_.Metric.isClosed_closedBall
  intro x hx
  apply eq_zero_of_not_mem_tsupport
  intro hxt
  exact hx <| Metric.ball_subset_closedBall (hsub hxt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.hasCompactSupport_of_tsupport_subset_ball then
    throwError "Refusing to shadow existing declaration DeGiorgi.hasCompactSupport_of_tsupport_subset_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.hasCompactSupport_of_tsupport_subset_ball ``Submission.DeGiorgi.hasCompactSupport_of_tsupport_subset_ball

omit [NeZero d] in
lemma deGiorgiCutoffTestGeneral_hasCompactSupport
    {η u : E → ℝ} {k : ℝ}
    (hη_comp : HasCompactSupport η) :
    HasCompactSupport (deGiorgiCutoffTestGeneral η u k) := by
  let h : HasCompactSupport (deGiorgiCutoffTestGeneral η u k) :=
    hη_comp.smul_right (f' := fun x => η x * positivePartSub u k x)
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.deGiorgiCutoffTestGeneral_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DeGiorgi.deGiorgiCutoffTestGeneral_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.deGiorgiCutoffTestGeneral_hasCompactSupport ``Submission.DeGiorgi.deGiorgiCutoffTestGeneral_hasCompactSupport

omit [NeZero d] in
lemma deGiorgiCutoffTestGeneral_tsupport_subset
    {Ω : Set E} {η u : E → ℝ} {k : ℝ}
    (hη_sub : tsupport η ⊆ Ω) :
    tsupport (deGiorgiCutoffTestGeneral η u k) ⊆ Ω := by
  let h : tsupport (deGiorgiCutoffTestGeneral η u k) ⊆ Ω :=
    (tsupport_smul_subset_left η (fun x => η x * positivePartSub u k x)).trans hη_sub
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.deGiorgiCutoffTestGeneral_tsupport_subset then
    throwError "Refusing to shadow existing declaration DeGiorgi.deGiorgiCutoffTestGeneral_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.deGiorgiCutoffTestGeneral_tsupport_subset ``Submission.DeGiorgi.deGiorgiCutoffTestGeneral_tsupport_subset

private noncomputable def positivePartSub_memW1pWitness
    {Ω : Set E} [_root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω) {u : E → ℝ}
    (hw : MemW1pWitness 2 u Ω) (k : ℝ)
    (happroxShift :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => ψ n x - (u x - k)) 2 (volume.restrict Ω))
          _root_.Filter.atTop (nhds 0) ∧
        (∀ i : Fin d,
          _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
            (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            2 (volume.restrict Ω))
          _root_.Filter.atTop (nhds 0))) :
    MemW1pWitness 2 (positivePartSub u k) Ω := by
  let hwShift : MemW1pWitness 2 (fun x => u x - k) Ω := hw.subConst hΩ k
  let h : MemW1pWitness 2 (positivePartSub u k) Ω :=
    hwShift.posPart hΩ happroxShift
  exact h

run_cmd do
  let target := ``Submission.DeGiorgi.positivePartSub_memW1pWitness
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.positivePartSub_memW1pWitness target :: scope.openDecls } }

theorem deGiorgiCutoffTest_memW01p_of_truncWitness
    {Ω : Set E} [_root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω)
    {u η : E → ℝ} {k : ℝ}
    (hw_trunc : MemW1pWitness 2 (positivePartSub u k) Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C₀ C₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁)
    (hη_comp : HasCompactSupport η)
    (hη_sub : tsupport η ⊆ Ω) :
    MemW01p 2 (deGiorgiCutoffTestGeneral η u k) Ω := by
  let _ := (inferInstance : (MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict Ω)))
  let hwη :=
    hw_trunc.mulSmoothBounded hΩ hη
      (C₀ := C₀) (C₁ := C₁) hC₀ hC₁ hη_bound hη_grad_bound
  let hwηθ : MemW1pWitness 2 (deGiorgiCutoffTestGeneral η u k) Ω :=
    hwη.mulSmoothBounded hΩ hη
      (C₀ := C₀) (C₁ := C₁) hC₀ hC₁ hη_bound hη_grad_bound
  have hv_comp : HasCompactSupport (deGiorgiCutoffTestGeneral η u k) :=
    deGiorgiCutoffTestGeneral_hasCompactSupport hη_comp
  have hv_sub : tsupport (deGiorgiCutoffTestGeneral η u k) ⊆ Ω :=
    deGiorgiCutoffTestGeneral_tsupport_subset hη_sub
  have hwηθ_memW1p_real :
      MemW1p (ENNReal.ofReal 2) (deGiorgiCutoffTestGeneral η u k) Ω := by
    simpa using hwηθ.memW1p
  simpa using
    (memW01p_of_memW1p_of_tsupport_subset
      hΩ (by norm_num : (1 : ℝ) < 2) hwηθ_memW1p_real hv_comp hv_sub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.deGiorgiCutoffTest_memW01p_of_truncWitness then
    throwError "Refusing to shadow existing declaration DeGiorgi.deGiorgiCutoffTest_memW01p_of_truncWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.deGiorgiCutoffTest_memW01p_of_truncWitness ``Submission.DeGiorgi.deGiorgiCutoffTest_memW01p_of_truncWitness

/-- General cutoff admissibility theorem, parameterized by a positive-part
witness theorem. This packages the reusable cutoff argument while keeping the
localization argument in
`memW01p_of_memW1p_of_tsupport_subset`. -/
theorem deGiorgiCutoffTest_memW01p_of_posPart
    {Ω : Set E} [_root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω)
    {u η : E → ℝ}
    (hw : MemW1pWitness 2 u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C₀ C₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁)
    (hη_comp : HasCompactSupport η)
    (hη_sub : tsupport η ⊆ Ω)
    (k : ℝ)
    (hpos :
      ∀ {v : E → ℝ},
        MemW1pWitness 2 v Ω →
          MemW1pWitness 2 (fun x => _root_.Max.max (v x) 0) Ω) :
    MemW01p 2 (deGiorgiCutoffTestGeneral η u k) Ω := by
  let hwShift : MemW1pWitness 2 (fun x => u x - k) Ω := hw.subConst hΩ k
  have hw_trunc : MemW1pWitness 2 (positivePartSub u k) Ω := by
    let h : MemW1pWitness 2 (positivePartSub u k) Ω := hpos hwShift
    exact h
  exact
    deGiorgiCutoffTest_memW01p_of_truncWitness
      hΩ hw_trunc hη hC₀ hC₁ hη_bound hη_grad_bound hη_comp hη_sub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.deGiorgiCutoffTest_memW01p_of_posPart then
    throwError "Refusing to shadow existing declaration DeGiorgi.deGiorgiCutoffTest_memW01p_of_posPart"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.deGiorgiCutoffTest_memW01p_of_posPart ``Submission.DeGiorgi.deGiorgiCutoffTest_memW01p_of_posPart

/-- Concrete cutoff admissibility theorem using the Chapter 02 positive-part
witness constructor and an explicit smooth-approximation package for `u - k`. -/
theorem deGiorgiCutoffTest_memW01p_of_posPartApprox
    {Ω : Set E} [_root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω)
    {u η : E → ℝ}
    (hw : MemW1pWitness 2 u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C₀ C₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁)
    (hη_comp : HasCompactSupport η)
    (hη_sub : tsupport η ⊆ Ω)
    (k : ℝ)
    (happroxShift :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => ψ n x - (u x - k)) 2 (volume.restrict Ω))
          _root_.Filter.atTop (nhds 0) ∧
        (∀ i : Fin d,
          _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
            (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            2 (volume.restrict Ω))
          _root_.Filter.atTop (nhds 0))) :
    MemW01p 2 (deGiorgiCutoffTestGeneral η u k) Ω := by
  let hw_trunc : MemW1pWitness 2 (positivePartSub u k) Ω :=
    positivePartSub_memW1pWitness hΩ hw k happroxShift
  exact
    deGiorgiCutoffTest_memW01p_of_truncWitness
      hΩ hw_trunc hη hC₀ hC₁ hη_bound hη_grad_bound hη_comp hη_sub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.deGiorgiCutoffTest_memW01p_of_posPartApprox then
    throwError "Refusing to shadow existing declaration DeGiorgi.deGiorgiCutoffTest_memW01p_of_posPartApprox"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.deGiorgiCutoffTest_memW01p_of_posPartApprox ``Submission.DeGiorgi.deGiorgiCutoffTest_memW01p_of_posPartApprox

/-- Ball version of generalized cutoff admissibility. This avoids any
dependence on the legacy `Cutoff` structure. -/
theorem deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPart
    {u η : E → ℝ} {x₀ : E} {s Cη : ℝ}
    (_hs : 0 < s)
    (hw : MemW1pWitness 2 u (Metric.ball x₀ s))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hCη : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s)
    (k : ℝ)
    (hposBall :
      ∀ {v : E → ℝ},
        MemW1pWitness 2 v (Metric.ball x₀ s) →
          MemW1pWitness 2 (fun x => _root_.Max.max (v x) 0) (Metric.ball x₀ s)) :
    MemW01p 2 (deGiorgiCutoffTestGeneral η u k) (Metric.ball x₀ s) := by
  let _ := _hs
  have : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (Metric.ball x₀ s)) := by
    rw [_root_.MeasureTheory.isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  have hη_comp : HasCompactSupport η :=
    hasCompactSupport_of_tsupport_subset_ball hη_sub_ball
  exact
    deGiorgiCutoffTest_memW01p_of_posPart
      _root_.Metric.isOpen_ball hw hη (by norm_num) hCη hη_bound hη_grad_bound hη_comp
      hη_sub_ball k hposBall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPart then
    throwError "Refusing to shadow existing declaration DeGiorgi.deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPart"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPart ``Submission.DeGiorgi.deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPart

/-- Ball version of cutoff admissibility driven by the concrete Chapter 02
positive-part witness constructor. -/
theorem deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPartApprox
    {u η : E → ℝ} {x₀ : E} {s Cη : ℝ}
    (_hs : 0 < s)
    (hw : MemW1pWitness 2 u (Metric.ball x₀ s))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hCη : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s)
    (k : ℝ)
    (happroxBallShift :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        _root_.Filter.Tendsto
          (fun n =>
            _root_.MeasureTheory.eLpNorm (fun x => ψ n x - (u x - k)) 2
              (volume.restrict (Metric.ball x₀ s)))
          _root_.Filter.atTop (nhds 0) ∧
        (∀ i : Fin d,
          _root_.Filter.Tendsto
            (fun n =>
              _root_.MeasureTheory.eLpNorm
                (fun x =>
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
                2 (volume.restrict (Metric.ball x₀ s)))
            _root_.Filter.atTop (nhds 0))) :
    MemW01p 2 (deGiorgiCutoffTestGeneral η u k) (Metric.ball x₀ s) := by
  let _ := _hs
  have : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (Metric.ball x₀ s)) := by
    rw [_root_.MeasureTheory.isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  have hη_comp : HasCompactSupport η :=
    hasCompactSupport_of_tsupport_subset_ball hη_sub_ball
  exact
    deGiorgiCutoffTest_memW01p_of_posPartApprox
      _root_.Metric.isOpen_ball hw hη (by norm_num) hCη hη_bound hη_grad_bound hη_comp
      hη_sub_ball k happroxBallShift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPartApprox then
    throwError "Refusing to shadow existing declaration DeGiorgi.deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPartApprox"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPartApprox ``Submission.DeGiorgi.deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPartApprox

/-- Concrete truncation witness on a ball, obtained from the Chapter 02
positive-part constructor applied to `u - k`. -/
noncomputable def positivePartSubMemW1pWitnessOnBall
    {u : E → ℝ} {x₀ : E} {s : ℝ}
    (_hs : 0 < s)
    (hw : MemW1pWitness 2 u (Metric.ball x₀ s))
    (k : ℝ)
    (happroxBallShift :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        _root_.Filter.Tendsto
          (fun n =>
            _root_.MeasureTheory.eLpNorm (fun x => ψ n x - (u x - k)) 2
              (volume.restrict (Metric.ball x₀ s)))
          _root_.Filter.atTop (nhds 0) ∧
        (∀ i : Fin d,
          _root_.Filter.Tendsto
            (fun n =>
              _root_.MeasureTheory.eLpNorm
                (fun x =>
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
                2 (volume.restrict (Metric.ball x₀ s)))
            _root_.Filter.atTop (nhds 0))) :
    MemW1pWitness 2 (positivePartSub u k) (Metric.ball x₀ s) := by
  let _ := _hs
  have hΩ : IsOpen (Metric.ball x₀ s) := _root_.Metric.isOpen_ball
  haveI : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (Metric.ball x₀ s)) := by
    rw [_root_.MeasureTheory.isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  exact positivePartSub_memW1pWitness hΩ hw k happroxBallShift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.positivePartSubMemW1pWitnessOnBall then
    throwError "Refusing to shadow existing declaration DeGiorgi.positivePartSubMemW1pWitnessOnBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.positivePartSubMemW1pWitnessOnBall ``Submission.DeGiorgi.positivePartSubMemW1pWitnessOnBall

end CutoffAdmissibility

end DeGiorgi
