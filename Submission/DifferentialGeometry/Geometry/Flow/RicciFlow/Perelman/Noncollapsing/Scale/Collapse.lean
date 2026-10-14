import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs
import Submission.DifferentialGeometry.Analysis.Calculus.DyadicScale
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.SmallBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

open _root_.Submission.DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

namespace FlowMetricBall

variable {S : SolutionOn (I := I) (M := M) D}
variable {time : RealTimeInterval.FlowTime D}

def shrink (B : FlowMetricBall S time) (q : ℝ) (hq : 0 < q) :
    FlowMetricBall S time where
  center := B.center
  radius := q * B.radius
  radius_pos := mul_pos hq B.radius_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink

def dyadic (B : FlowMetricBall S time) (j : ℕ) : FlowMetricBall S time :=
  B.shrink ((1 / 2 : ℝ) ^ j) (by positivity)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.dyadic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.dyadic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.dyadic ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.dyadic

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
omit [IsManifold I 1 M] in
@[simp] theorem dyadic_radius (B : FlowMetricBall S time) (j : ℕ) :
    (B.dyadic j).radius = (1 / 2 : ℝ) ^ j * B.radius := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.dyadic_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.dyadic_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.dyadic_radius ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.dyadic_radius

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
omit [IsManifold I 1 M] in
theorem dyadic_succ_radius (B : FlowMetricBall S time) (j : ℕ) :
    (B.dyadic (j + 1)).radius = (B.dyadic j).radius / 2 := by
  simp only [dyadic_radius, pow_succ]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.dyadic_succ_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.dyadic_succ_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.dyadic_succ_radius ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.dyadic_succ_radius

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
omit [IsManifold I 1 M] in
theorem shrink_setAt
    (B : FlowMetricBall S time) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (t : ℝ) :
    (B.shrink q hq).setAt t ⊆ B.setAt t := by
  intro x hx
  have hqr : q * B.radius ≤ B.radius := by
    nlinarith [B.radius_pos]
  exact lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hqr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink_setAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink_setAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink_setAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink_setAt

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
omit [IsManifold I 1 M] in
theorem shrink_nested
    (B : FlowMetricBall S time) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    (B.shrink q hq).Nested B :=
  shrink_setAt B hq hq1 time

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink_nested then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink_nested"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink_nested ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink_nested

omit [SigmaCompactSpace M] in
theorem shrink_rm
    (B : FlowMetricBall S time) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hB : B.IsRmControlled) :
    (B.shrink q hq).IsRmControlled := by
  have hq0 : 0 ≤ q := hq.le
  have hqr0 : 0 ≤ q * B.radius := mul_nonneg hq0 B.radius_pos.le
  have hqr : q * B.radius ≤ B.radius := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq1 B.radius_pos.le
  have hsq : (q * B.radius) ^ 2 ≤ B.radius ^ 2 := by
    exact pow_le_pow_left₀ hqr0 hqr 2
  constructor
  · intro t ht
    apply hB.1
    constructor
    · exact le_trans (by nlinarith : (time : ℝ) - B.radius ^ 2 ≤
          (time : ℝ) - (q * B.radius) ^ 2) ht.1
    · exact ht.2
  · intro t ht x hx
    have ht' : t ∈ Set.Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) := by
      constructor
      · exact le_trans (by nlinarith : (time : ℝ) - B.radius ^ 2 ≤
            (time : ℝ) - (q * B.radius) ^ 2) ht.1
      · exact ht.2
    have hx' : x ∈ B.setAt t := shrink_setAt B hq hq1 t hx
    have hcurv := hB.2 t ht' x hx'
    have hrpow : (q * B.radius) ^ 4 ≤ B.radius ^ 4 := by
      exact pow_le_pow_left₀ hqr0 hqr 4
    have hRm0 : 0 ≤ rmNormSq S t x := by
      exact normSq0S_nonneg (I := I) (S.base.metric t) x 4 (S.base.rm04 t x)
    exact (mul_le_mul_of_nonneg_right hrpow hRm0).trans hcurv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.shrink_rm

theorem exists_coll_scale
    [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless]
    [T2Space (TangentBundle I M)] [T3Space M] [ConnectedSpace M]
    [CompactSpace M]
    (B : FlowMetricBall S time) (hB : B.IsRmControlled) :
    ∃ B' : FlowMetricBall S time,
      B'.Nested B ∧ B'.radius ≤ B.radius ∧ B'.IsRmControlled ∧
      B'.volume.toReal / B'.radius ^ Module.finrank ℝ E ≤
        B.volume.toReal / B.radius ^ Module.finrank ℝ E ∧
      B'.volume.toReal < (2 : ℝ) ^ (Module.finrank ℝ E + 1) *
        (volumeMeasureOn (I := I) (M := M) S.family time
          {x : M | DifferentialGeometry.riemannianEDistOf
            (I := I) (S.base.metric (time : ℝ)) B'.center x <
              ENNReal.ofReal (B'.radius / 2)}).toReal := by
  let n : ℕ := Module.finrank ℝ E
  let V : ℕ → ℝ := fun j => (B.dyadic j).volume.toReal
  let W : ℕ → ℝ := fun j => V j / (B.dyadic j).radius ^ n
  obtain ⟨ε, ρ, hε, hρ, hvol⟩ :=
    DifferentialGeometry.Geometry.Riemannian.VolumeComparison.exists_edist_vol
      (I := I) (g := S.base.metric (time : ℝ)) B.center
  have hr_tend : Filter.Tendsto (fun j : ℕ => (B.dyadic j).radius)
      Filter.atTop (nhds 0) := by
    simpa only [dyadic_radius, _root_.MulZeroClass.zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
          B.radius
  have hr_small : ∀ᶠ j : ℕ in Filter.atTop, (B.dyadic j).radius ≤ ρ := by
    filter_upwards [hr_tend.eventually_lt_const hρ] with j hj
    exact hj.le
  have hW : ∀ j : ℕ, 0 ≤ W j := by
    intro j
    exact div_nonneg ENNReal.toReal_nonneg (pow_nonneg (B.dyadic j).radius_pos.le _)
  have hlow : ∀ᶠ j : ℕ in Filter.atTop, ε ≤ W j := by
    filter_upwards [hr_small] with j hj
    have hjvol := hvol (B.dyadic j).radius (B.dyadic j).radius_pos hj
    have hjvol' : ε * (B.dyadic j).radius ^ n ≤ V j := by
      simpa only [n, V, FlowMetricBall.volume, FlowMetricBall.set,
        FlowMetricBall.setAt, volumeMeasureOn_eq_metric, SolutionOn.family_metric,
        dyadic, shrink] using hjvol
    exact (le_div_iff₀ (pow_pos (B.dyadic j).radius_pos n)).2 hjvol'
  obtain ⟨j, hjdrop, hjbase⟩ :=
    DifferentialGeometry.Analysis.Calculus.exists_drop_lower W
      (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hW hε hlow
  refine ⟨B.dyadic j, ?_, ?_, ?_, ?_, ?_⟩
  · apply shrink_nested B (by positivity)
    exact pow_le_one₀ (by norm_num) (by norm_num)
  · rw [dyadic_radius]
    exact mul_le_of_le_one_left B.radius_pos.le
      (pow_le_one₀ (by norm_num) (by norm_num))
  · exact shrink_rm B (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num)) hB
  · simpa only [W, V, n, dyadic, shrink, pow_zero, one_mul] using hjbase
  · have hrj : 0 < (B.dyadic j).radius := (B.dyadic j).radius_pos
    have hrn : 0 < (B.dyadic j).radius ^ n := pow_pos hrj n
    have hsuc : (B.dyadic (j + 1)).radius ^ n =
        (B.dyadic j).radius ^ n / (2 : ℝ) ^ n := by
      rw [dyadic_succ_radius, div_pow]
    have hdrop : (1 / 2 : ℝ) *
        (V j / (B.dyadic j).radius ^ n) <
          V (j + 1) / ((B.dyadic j).radius ^ n / (2 : ℝ) ^ n) := by
      simpa only [W, hsuc] using hjdrop
    have htwo : 0 < (2 : ℝ) ^ n := by positivity
    have hscaled := mul_lt_mul_of_pos_right hdrop hrn
    have hV : V j < (2 : ℝ) ^ (n + 1) * V (j + 1) := by
      field_simp at hscaled
      rw [pow_succ]
      nlinarith
    rw [← dyadic_succ_radius]
    change V j < (2 : ℝ) ^ (n + 1) * V (j + 1)
    exact hV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.exists_coll_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.exists_coll_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.exists_coll_scale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall.exists_coll_scale

end FlowMetricBall

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
