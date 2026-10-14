import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem redLength_squareRootReparametrization_le_of_action_eq_lCost
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (alpha : ℝ → M)
    (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) (x y : M)
    {s tau : ℝ} (hs : 0 < s) (hst : s ≤ tau)
    (hstart : alpha 0 = x) (hend : alpha (Real.sqrt tau) = y)
    (hscalar : ∀ r ∈ _root_.Set.Icc 0 tau, ∀ z : M, 0 ≤ S.scalar (T - r) z)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume 0 (Real.sqrt tau))
    (hcost : lRegularizedAction S T alpha 0 (Real.sqrt tau) =
      lCost S T x (alpha (Real.sqrt tau)) tau) :
    redLength S T x (alpha (Real.sqrt s)) s ≤
      (Real.sqrt tau / Real.sqrt s) * redLength S T x y tau := by
  have htau : 0 < tau := hs.trans_le hst
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have htauSqrt : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hsqrtLe : Real.sqrt s ≤ Real.sqrt tau := Real.sqrt_le_sqrt hst
  have hcostLower : BddBelow {v : ℝ | ∃ beta : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 beta ∧ beta 0 = x ∧ beta (Real.sqrt s) = alpha (Real.sqrt s) ∧
      lLength S T (squareRootReparametrization beta) 0 s = v} := by
    refine ⟨0, ?_⟩
    rintro v ⟨beta, _, _, _, rfl⟩
    apply intervalIntegral.integral_nonneg hs.le
    intro r hr
    exact mul_nonneg (Real.sqrt_nonneg r)
      (add_nonneg (hscalar r ⟨hr.1, hr.2.trans hst⟩ _)
        (lSpeedSq_nonneg S T (squareRootReparametrization beta) r))
  have hprefix : lCost S T x (alpha (Real.sqrt s)) s ≤
      lRegularizedAction S T alpha 0 (Real.sqrt s) := by
    rw [← lLength_squareRootReparametrization_eq_lRegularizedAction S T alpha s hs.le]
    exact csInf_le hcostLower ⟨alpha, halpha, hstart, rfl, rfl⟩
  have hheadInt : IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume 0 (Real.sqrt s) :=
    hint.mono_set (by
      rw [_root_.Set.uIcc_of_le hsqrt.le, _root_.Set.uIcc_of_le htauSqrt.le]
      exact _root_.Set.Icc_subset_Icc le_rfl hsqrtLe)
  have htailInt : IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume
      (Real.sqrt s) (Real.sqrt tau) := hint.mono_set (by
    rw [_root_.Set.uIcc_of_le hsqrtLe, _root_.Set.uIcc_of_le htauSqrt.le]
    exact _root_.Set.Icc_subset_Icc hsqrt.le le_rfl)
  have htail : 0 ≤ lRegularizedAction S T alpha (Real.sqrt s) (Real.sqrt tau) := by
    apply intervalIntegral.integral_nonneg hsqrtLe
    intro r hr
    have hr0 : 0 ≤ r := hsqrt.le.trans hr.1
    have hr2 : r ^ 2 ≤ tau :=
      (pow_le_pow_left₀ hr0 hr.2 2).trans_eq (Real.sq_sqrt htau.le)
    have hpot := hscalar (r ^ 2) ⟨sq_nonneg r, hr2⟩ (alpha r)
    change 0 ≤ (1 / 2 : ℝ) * lRegularizedSpeedSq S T alpha r +
      2 * r ^ 2 * S.scalar (T - r ^ 2) (alpha r)
    exact add_nonneg (mul_nonneg (by norm_num) (lRegularizedSpeedSq_nonneg S T alpha r))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg r)) hpot)
  have haction := lRegularizedAction_add S T alpha 0 (Real.sqrt s) (Real.sqrt tau)
    hheadInt htailInt
  have hcostLe : lCost S T x (alpha (Real.sqrt s)) s ≤ lCost S T x y tau := by
    rw [← hend, ← hcost]
    linarith
  calc
    redLength S T x (alpha (Real.sqrt s)) s =
        lCost S T x (alpha (Real.sqrt s)) s / (2 * Real.sqrt s) := rfl
    _ ≤ lCost S T x y tau / (2 * Real.sqrt s) :=
      (div_le_div_iff_of_pos_right (by positivity)).mpr hcostLe
    _ = (Real.sqrt tau / Real.sqrt s) * redLength S T x y tau := by
      unfold redLength
      field_simp [hsqrt.ne', htauSqrt.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_squareRootReparametrization_le_of_action_eq_lCost then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_squareRootReparametrization_le_of_action_eq_lCost"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_squareRootReparametrization_le_of_action_eq_lCost ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_squareRootReparametrization_le_of_action_eq_lCost

end DifferentialGeometry.PDE.RicciFlow.Perelman
