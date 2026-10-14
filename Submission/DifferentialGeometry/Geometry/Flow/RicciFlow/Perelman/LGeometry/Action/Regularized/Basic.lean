import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegularizedSpeedSq_nonneg
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (s : Real) : 0 ≤ lRegularizedSpeedSq S T alpha s := by
  unfold lRegularizedSpeedSq
  by_cases hzero : lVelocity (I := I) alpha s = 0
  · rw [hzero]
    simp
  · exact ((S.base.metric (T - s ^ 2)).pos (alpha s) _ hzero).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedSpeedSq_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedSpeedSq_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedSpeedSq_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedSpeedSq_nonneg

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegularizedAction_add
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (a b c : Real)
    (hab : IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hbc : IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume b c) :
    lRegularizedAction S T alpha a b + lRegularizedAction S T alpha b c =
      lRegularizedAction S T alpha a c := by
  exact intervalIntegral.integral_add_adjacent_intervals hab hbc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_add ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_add

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegularizedAction_sum
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) {t : ℕ → Real} {n : ℕ}
    (hint : ∀ k < n,
      IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume (t k) (t (k + 1))) :
    (∑ k ∈ Finset.range n, lRegularizedAction S T alpha (t k) (t (k + 1))) =
      lRegularizedAction S T alpha (t 0) (t n) := by
  exact intervalIntegral.sum_integral_adjacent_intervals hint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_sum ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_sum

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegularizedAction_congr
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha beta : Real → M) (a b : Real)
    (h : Set.EqOn alpha beta (Set.uIoo a b)) :
    lRegularizedAction S T alpha a b = lRegularizedAction S T beta a b := by
  unfold lRegularizedAction
  apply intervalIntegral.integral_congr_ae
  filter_upwards
    [MeasureTheory.Measure.ae_ne MeasureTheory.volume (_root_.Max.max a b)]
      with s hsmax hs
  change s ∈ Set.Ioc (_root_.Min.min a b) (_root_.Max.max a b) at hs
  have hsIoo : s ∈ Set.Ioo (_root_.Min.min a b) (_root_.Max.max a b) :=
    ⟨hs.1, lt_of_le_of_ne hs.2 hsmax⟩
  have hev : alpha =ᶠ[𝓝 s] beta := by
    filter_upwards [Ioo_mem_nhds hsIoo.1 hsIoo.2] with r hr
    exact h (by simpa only [Set.uIoo] using hr)
  have hval : alpha s = beta s := hev.self_of_nhds
  have hmf :
      mfderiv 𝓘(Real, Real) I alpha s =
        mfderiv 𝓘(Real, Real) I beta s :=
    Filter.EventuallyEq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I) hev
  have hvel : lVelocity (I := I) alpha s = lVelocity (I := I) beta s := by
    with_unfolding_all exact
      (congrArg (fun L => L (1 : Real)) hmf)
  simp only [lRegularizedLagrangian]
  rw [hval, hvel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_congr ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_congr


omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegularizedAction_const
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M) (a b : ℝ) :
    lRegularizedAction S T (fun _ => p) a b =
      ∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) p := by
  have hv (s : ℝ) : lVelocity (I := I) (fun _ : ℝ => p) s = 0 := by
    simp only [lVelocity, mfderiv_const]
    rfl
  simp only [lRegularizedAction, lRegularizedLagrangian, hv, map_zero, _root_.MulZeroClass.mul_zero, zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_const ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_const

end DifferentialGeometry.PDE.RicciFlow.Perelman
