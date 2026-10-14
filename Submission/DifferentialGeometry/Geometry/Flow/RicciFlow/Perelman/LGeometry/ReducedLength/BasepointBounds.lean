import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.Identities

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem redLength_self_le_of_scalar_bounds [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (p : M) {tau : ℝ} (htau : 0 < tau) (K : ℝ)
    (htime : ∀ s ∈ _root_.Set.Icc 0 tau, T - s ∈ D.carrier)
    (hscalar : ∀ s ∈ _root_.Set.Icc 0 tau, ∀ z : M, 0 ≤ S.scalar (T - s) z)
    (hupper : ∀ s ∈ _root_.Set.Icc 0 tau, S.scalar (T - s) p ≤ K) :
    redLength S T p p tau ≤ K * tau / 3 := by
  have hsqrt := Real.sqrt_pos.mpr htau
  have hsquare (s : ℝ) (hs : s ∈ _root_.Set.Icc 0 (Real.sqrt tau)) : s ^ 2 ∈ _root_.Set.Icc 0 tau := by
    refine ⟨sq_nonneg s, ?_⟩
    calc
      s ^ 2 ≤ (Real.sqrt tau) ^ 2 := (sq_le_sq₀ hs.1 hsqrt.le).mpr hs.2
      _ = tau := Real.sq_sqrt htau.le
  have hcont : ContinuousOn (fun s : ℝ => S.scalar (T - s ^ 2) p)
      (_root_.Set.Icc 0 (Real.sqrt tau)) := by
    have hmap : ContinuousOn (fun s : ℝ => (T - s ^ 2, p)) (_root_.Set.Icc 0 (Real.sqrt tau)) :=
      (continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk continuousOn_const
    have hc : ContinuousOn (fun z : ℝ × M => S.scalar z.1 z.2) (D.carrier ×ˢ _root_.Set.univ) := hS.scalarCont
    have hh := hc.comp hmap (fun s hs => ⟨htime _ (hsquare s hs), _root_.Set.mem_univ _⟩)
    exact hh
  have hleft : IntervalIntegrable (fun s : ℝ => 2 * s ^ 2 * S.scalar (T - s ^ 2) p)
      volume 0 (Real.sqrt tau) := by
    apply ContinuousOn.intervalIntegrable
    rw [_root_.Set.uIcc_of_le hsqrt.le]
    exact (continuousOn_const.mul (continuousOn_id.pow 2)).mul hcont
  have hright : IntervalIntegrable (fun s : ℝ => 2 * s ^ 2 * K) _root_.MeasureTheory.MeasureSpace.volume 0 (Real.sqrt tau) :=
    (by fun_prop : Continuous (fun s : ℝ => 2 * s ^ 2 * K)).intervalIntegrable _ _
  have hle := intervalIntegral.integral_mono_on hsqrt.le hleft hright
    (fun s hs => mul_le_mul_of_nonneg_left (hupper _ (hsquare s hs)) (by positivity))
  have hint : (∫ s in (0 : ℝ)..Real.sqrt tau, 2 * s ^ 2 * K) =
      2 * K * (Real.sqrt tau) ^ 3 / 3 := by
    simp_rw [mul_right_comm (2 : ℝ) _ K]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  have hcost := lCost_le_lRegularizedAction_of_scalar_nonneg S htau.le hscalar
    (fun _ : ℝ => p) contMDiff_const
  rw [lRegularizedAction_const] at hcost
  rw [hint] at hle
  unfold redLength
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt tau)).mpr
  calc
    lCost S T p p tau ≤ 2 * K * (Real.sqrt tau) ^ 3 / 3 := hcost.trans hle
    _ = K * tau / 3 * (2 * Real.sqrt tau) := by
      rw [pow_succ, Real.sq_sqrt htau.le]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_self_le_of_scalar_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_self_le_of_scalar_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_self_le_of_scalar_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_self_le_of_scalar_bounds

theorem exists_redLength_self_lt_scalar_mul [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (p : M) {delta : ℝ} (hdelta : 0 < delta)
    (htime : ∀ s ∈ _root_.Set.Icc 0 delta, T - s ∈ D.carrier)
    (hscalar : ∀ s ∈ _root_.Set.Icc 0 delta, ∀ z : M, 0 ≤ S.scalar (T - s) z)
    (hpos : 0 < S.scalar T p) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ delta ∧ ∀ tau ∈ _root_.Set.Ioo 0 epsilon,
      redLength S T p p tau < tau * S.scalar (T - tau) p := by
  have hc : ContinuousOn (fun z : ℝ × M => S.scalar z.1 z.2) (D.carrier ×ˢ _root_.Set.univ) := hS.scalarCont
  have hmap : ContinuousOn (fun s : ℝ => (T - s, p)) (_root_.Set.Icc 0 delta) :=
    (continuous_const.sub continuous_id).continuousOn.prodMk continuousOn_const
  have hcont : ContinuousOn (fun s : ℝ => S.scalar (T - s) p) (_root_.Set.Icc 0 delta) := by
    have hh := hc.comp hmap (fun s hs => ⟨htime s hs, _root_.Set.mem_univ _⟩)
    exact hh
  obtain ⟨r, hr, hnear⟩ := Metric.continuousWithinAt_iff.mp
    (hcont 0 ⟨le_rfl, hdelta.le⟩) (S.scalar T p / 2) (by positivity)
  refine ⟨min r delta, lt_min hr hdelta, min_le_right _ _, ?_⟩
  intro tau htau
  have hsub : _root_.Set.Icc 0 tau ⊆ _root_.Set.Icc 0 delta :=
    _root_.Set.Icc_subset_Icc le_rfl (htau.2.le.trans (min_le_right _ _))
  have hbound (s : ℝ) (hs : s ∈ _root_.Set.Icc 0 tau) :
      |S.scalar (T - s) p - S.scalar T p| < S.scalar T p / 2 := by
    have hdist : _root_.Dist.dist s 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      exact hs.2.trans_lt (htau.2.trans_le (min_le_left _ _))
    simpa only [Real.dist_eq, sub_zero] using hnear (hsub hs) hdist
  have hupper : ∀ s ∈ _root_.Set.Icc 0 tau, S.scalar (T - s) p ≤ 3 * S.scalar T p / 2 := by
    intro s hs
    have h := (abs_lt.mp (hbound s hs)).2
    linarith
  have hlower : S.scalar T p / 2 < S.scalar (T - tau) p := by
    have h := (abs_lt.mp (hbound tau ⟨htau.1.le, le_rfl⟩)).1
    linarith
  calc
    redLength S T p p tau ≤ (3 * S.scalar T p / 2) * tau / 3 :=
      redLength_self_le_of_scalar_bounds S hS T p htau.1 (3 * S.scalar T p / 2)
        (fun s hs => htime s (hsub hs)) (fun s hs => hscalar s (hsub hs)) hupper
    _ = tau * (S.scalar T p / 2) := by ring
    _ < tau * S.scalar (T - tau) p := mul_lt_mul_of_pos_left hlower htau.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_redLength_self_lt_scalar_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_redLength_self_lt_scalar_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_redLength_self_lt_scalar_mul ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_redLength_self_lt_scalar_mul

theorem scalar_eq_zero_of_hamiltonNormalized_redLength [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (p : M) {delta : ℝ} (hdelta : 0 < delta)
    (htime : ∀ s ∈ _root_.Set.Icc 0 delta, T - s ∈ D.carrier)
    (hscalar : ∀ s ∈ _root_.Set.Icc 0 delta, ∀ z : M, 0 ≤ S.scalar (T - s) z)
    (hnormal : ∀ tau ∈ _root_.Set.Ioo 0 delta,
      ∃ hf : ContMDiff I 𝓘(ℝ) ∞ (fun x => redLength S T p x tau),
        Geometry.hamiltonNormalized (S.base.metric (T - tau))
          ⟨(fun x => redLength S T p x tau), hf⟩ (1 / tau)) :
    S.scalar T p = 0 := by
  have hn : 0 ≤ S.scalar T p := by
    simpa only [sub_zero] using hscalar 0 ⟨le_rfl, hdelta.le⟩ p
  apply le_antisymm _ hn
  by_contra h
  have hp : 0 < S.scalar T p := lt_of_not_ge h
  obtain ⟨epsilon, hepsilon, he, hlt⟩ :=
    exists_redLength_self_lt_scalar_mul S hS T p hdelta htime hscalar hp
  have ht : epsilon / 2 ∈ _root_.Set.Ioo 0 epsilon := ⟨half_pos hepsilon, half_lt_self hepsilon⟩
  obtain ⟨hf, hh⟩ := hnormal (epsilon / 2) ⟨ht.1, ht.2.trans_le he⟩
  have hnorm := hh p
  change S.scalar (T - epsilon / 2) p +
    (S.base.metric (T - epsilon / 2)).inner p
      (Geometry.Operator.gradFun (S.base.metric (T - epsilon / 2))
        (fun x => redLength S T p x (epsilon / 2)) p)
      (Geometry.Operator.gradFun (S.base.metric (T - epsilon / 2))
        (fun x => redLength S T p x (epsilon / 2)) p) =
      1 / (epsilon / 2) * redLength S T p p (epsilon / 2) at hnorm
  have hg := Geometry.Operator.normGradSqFun_nonneg (S.base.metric (T - epsilon / 2))
    (fun x => redLength S T p x (epsilon / 2)) p
  rw [Geometry.Operator.normGradSqFun_def] at hg
  have hle : (epsilon / 2) * S.scalar (T - epsilon / 2) p ≤
      redLength S T p p (epsilon / 2) := by
    calc
      _ ≤ (epsilon / 2) * (1 / (epsilon / 2) * redLength S T p p (epsilon / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hnorm, hg]) ht.1.le
      _ = _ := by rw [one_div, ← mul_assoc, mul_inv_cancel₀ ht.1.ne', one_mul]
  exact (not_lt_of_ge hle) (hlt _ ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_eq_zero_of_hamiltonNormalized_redLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_eq_zero_of_hamiltonNormalized_redLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_eq_zero_of_hamiltonNormalized_redLength ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_eq_zero_of_hamiltonNormalized_redLength

end DifferentialGeometry.PDE.RicciFlow.Perelman
