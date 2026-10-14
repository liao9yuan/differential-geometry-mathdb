import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.MinimizerNonnegativity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Reparametrization
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}


theorem lLength_nonneg_of_scalar_nonneg
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) {tau : ℝ} (htau : 0 ≤ tau)
    (hscalar : ∀ s ∈ _root_.Set.Icc 0 tau, ∀ x : M, 0 ≤ S.scalar (T - s) x) (gamma : ℝ → M) :
    0 ≤ lLength S T gamma 0 tau := by
  apply intervalIntegral.integral_nonneg htau
  intro s hs
  exact mul_nonneg (Real.sqrt_nonneg s) (add_nonneg (hscalar s hs (gamma s))
    (lSpeedSq_nonneg S T gamma s))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lLength_nonneg_of_scalar_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lLength_nonneg_of_scalar_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lLength_nonneg_of_scalar_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lLength_nonneg_of_scalar_nonneg


theorem lCost_nonneg_of_scalar_nonneg
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) {tau : ℝ} (htau : 0 ≤ tau)
    (hscalar : ∀ s ∈ _root_.Set.Icc 0 tau, ∀ x : M, 0 ≤ S.scalar (T - s) x) (p q : M) :
    0 ≤ lCost S T p q tau := by
  apply Real.sInf_nonneg
  rintro value ⟨alpha, _hsmooth, _hstart, _hend, rfl⟩
  exact lLength_nonneg_of_scalar_nonneg S T htau hscalar (squareRootReparametrization alpha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lCost_nonneg_of_scalar_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lCost_nonneg_of_scalar_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lCost_nonneg_of_scalar_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lCost_nonneg_of_scalar_nonneg


theorem lCost_le_stationary_path
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) {tau : ℝ} (htau : 0 ≤ tau)
    (hscalar : ∀ s ∈ _root_.Set.Icc 0 tau, ∀ x : M, 0 ≤ S.scalar (T - s) x) (p : M) :
    lCost S T p p tau ≤ lLength S T (fun _ => p) 0 tau := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro value ⟨alpha, _hsmooth, _hstart, _hend, rfl⟩
    exact lLength_nonneg_of_scalar_nonneg S T htau hscalar (squareRootReparametrization alpha)
  · exact ⟨fun _ => p, contMDiff_const, rfl, rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lCost_le_stationary_path then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lCost_le_stationary_path"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lCost_le_stationary_path ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lCost_le_stationary_path


theorem reducedCost_at_pole_le
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) {tau : ℝ} (htau : 0 < tau)
    (hscalar : ∀ s ∈ _root_.Set.Icc 0 tau, ∀ x : M, 0 ≤ S.scalar (T - s) x) (p : M)
    {C : ℝ} (hbound : ∀ s ∈ _root_.Set.Icc 0 tau, S.scalar (T - s) p ≤ C)
    (hcontinuous : ContinuousOn (fun s : ℝ => S.scalar (T - s) p) (_root_.Set.Icc 0 tau)) :
    lCost S T p p tau / (2 * Real.sqrt tau) ≤ C * tau / 3 := by
  have hsqrt : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hsqrtSq : (Real.sqrt tau) ^ 2 = tau := Real.sq_sqrt htau.le
  have hcost := lCost_le_stationary_path S T htau.le hscalar p
  change lCost S T p p tau ≤
    lLength S T (squareRootReparametrization (fun _ => p)) 0 tau at hcost
  rw [lLength_squareRootReparametrization_eq_lRegularizedAction
    S T (fun _ => p) tau htau.le] at hcost
  have hlag : lRegularizedLagrangian S T (fun _ => p) =
      fun s : ℝ => 2 * s ^ 2 * S.scalar (T - s ^ 2) p := by
    funext s
    have hvel : lVelocity (I := I) (fun _ : ℝ => p) s = 0 := by
      simp only [lVelocity, mfderiv_const]
      rfl
    simp only [lRegularizedLagrangian, hvel, map_zero, _root_.MulZeroClass.mul_zero, zero_add]
  have hsquares (s : ℝ) (hs : s ∈ _root_.Set.uIcc 0 (Real.sqrt tau)) : s ^ 2 ∈ _root_.Set.Icc 0 tau := by
    rw [_root_.Set.uIcc_of_le hsqrt.le] at hs
    exact ⟨sq_nonneg s, (pow_le_pow_left₀ hs.1 hs.2 2).trans_eq hsqrtSq⟩
  have hscalarContinuous : ContinuousOn (fun s : ℝ => S.scalar (T - s ^ 2) p)
      (_root_.Set.uIcc 0 (Real.sqrt tau)) :=
    hcontinuous.comp (continuous_pow 2).continuousOn hsquares
  have hleft : IntervalIntegrable
      (fun s : ℝ => 2 * s ^ 2 * S.scalar (T - s ^ 2) p) _root_.MeasureTheory.MeasureSpace.volume 0 (Real.sqrt tau) :=
    ((continuous_const.mul (continuous_pow 2)).continuousOn.mul
      hscalarContinuous).intervalIntegrable
  have hright : IntervalIntegrable (fun s : ℝ => 2 * s ^ 2 * C)
      volume 0 (Real.sqrt tau) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hint : (∫ s in (0 : ℝ)..Real.sqrt tau, 2 * s ^ 2 * S.scalar (T - s ^ 2) p) ≤
      ∫ s in (0 : ℝ)..Real.sqrt tau, 2 * s ^ 2 * C := by
    apply intervalIntegral.integral_mono_on hsqrt.le hleft hright
    intro s hs
    apply mul_le_mul_of_nonneg_left (hbound (s ^ 2) (hsquares s ?_)) (by positivity)
    simpa only [_root_.Set.uIcc_of_le hsqrt.le] using hs
  have hintegral : (∫ s in (0 : ℝ)..Real.sqrt tau, 2 * s ^ 2 * C) =
      2 * C * (Real.sqrt tau) ^ 3 / 3 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      integral_pow]
    norm_num
    ring
  have hcostBound : lCost S T p p tau ≤ 2 * C * (Real.sqrt tau) ^ 3 / 3 := by
    change lCost S T p p tau ≤
      ∫ s in (0 : ℝ)..Real.sqrt tau, lRegularizedLagrangian S T (fun _ => p) s at hcost
    rw [hlag] at hcost
    exact hcost.trans (hint.trans_eq hintegral)
  calc
    lCost S T p p tau / (2 * Real.sqrt tau) ≤
        (2 * C * (Real.sqrt tau) ^ 3 / 3) / (2 * Real.sqrt tau) :=
      div_le_div_of_nonneg_right hcostBound (by positivity)
    _ = C * tau / 3 := by
      rw [pow_succ, hsqrtSq]
      field_simp [hsqrt.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reducedCost_at_pole_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reducedCost_at_pole_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reducedCost_at_pole_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.reducedCost_at_pole_le

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
