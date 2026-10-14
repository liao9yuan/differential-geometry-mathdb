import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCompleteLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardBoundedDistance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

theorem StandardSolution.terminalRegularRegion_eq_bot (S : StandardSolution) :
    terminalRegularRegion S.val.metric 0 1 = ⊥ := by
  apply bot_unique
  intro p hp
  obtain ⟨U, hpU, a, ha, K, _hK, hbound⟩ := hp
  let time : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 4)
  have htime (n : ℕ) : time n ∈ _root_.Set.Ico (0 : ℝ) 1 := by
    have hd : 0 < (n : ℝ) + 4 := by positivity
    have hdiv : 1 / ((n : ℝ) + 4) ≤ 1 := (div_le_one hd).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact ⟨by dsimp [time]; linarith, by dsimp [time]; exact sub_lt_self _ (div_pos zero_lt_one hd)⟩
  have hlate (n : ℕ) : 3 / 4 ≤ time n := by
    have hd : 0 < (n : ℝ) + 4 := by positivity
    have hdiv : 1 / ((n : ℝ) + 4) ≤ 1 / 4 := (div_le_iff₀ hd).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [time]
    linarith
  have hlim : _root_.Filter.Tendsto time _root_.Filter.atTop (𝓝 1) := by
    have hnat : _root_.Filter.Tendsto (fun n : ℕ => (n : ℝ) + 4) _root_.Filter.atTop atTop :=
      _root_.Filter.tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ) + 4)
        tendsto_natCast_atTop_atTop
    have hz : _root_.Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 4)) _root_.Filter.atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnat
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hz
  have hdom (n : ℕ) : time n ∈ S.val.domain := by
    apply (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos _).mpr
    rw [S.lifetime_eq_one]
    exact ⟨(htime n).1, ENNReal.ofReal_lt_one.mpr (htime n).2⟩
  have hbase : ∀ᶠ n in _root_.Filter.atTop, metricScalarAt (S.val.metric (time n)) p ≤ 9 * K := by
    filter_upwards [hlim.eventually (Ioi_mem_nhds ha.2)] with n hn
    have hrm := hbound p hpU (time n) ⟨hn.le, (htime n).2⟩
    have hsc := scalar_abs_le_rm (S.val.metric (time n)) p
    change |metricScalarAt (S.val.metric (time n)) p| ≤
      (Module.finrank ℝ E3 : ℝ) ^ 2 * _ at hsc
    norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] at hsc
    exact (le_abs_self _).trans (hsc.trans (mul_le_mul_of_nonneg_left hrm (by norm_num)))
  have hballs : ∀ r : ℝ, 0 < r → ∃ A : ℝ, ∀ᶠ n in _root_.Filter.atTop,
      ∀ y ∈ riemannianClosedBallOf (S.val.metric (time n)) p r,
        metricScalarAt (S.val.metric (time n)) y ≤ A := by
    intro r hr
    obtain ⟨A, hb⟩ := exists_standard_scalar_bound_at_bounded_distance (9 * K) r hr.le
    refine ⟨A, hbase.mono fun n hn y hy => hb S.val (time n) (hdom n) (hlate n)
      (htime n).2 p y hn hy⟩
  obtain ⟨P, hcanonical, _hconn, _hpre, _hconnected, _hnested, A, hA⟩ :=
    exists_standard_complete_terminal_limit_of_bounded_scalar_on_balls
      (fun _ => S.val) time (fun _ => p) (by norm_num : (0 : ℝ) < 3 / 4)
      (fun n => ⟨hdom n, hlate n, (htime n).2⟩) hballs
  exact S.not_exists_complete_bounded_terminal_limit time p htime hlim ⟨P, hcanonical, A, hA⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardSolution.terminalRegularRegion_eq_bot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardSolution.terminalRegularRegion_eq_bot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardSolution.terminalRegularRegion_eq_bot ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardSolution.terminalRegularRegion_eq_bot

theorem exists_standard_scalar_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (S : StandardSolution) (x : E3),
      ∀ t ∈ _root_.Set.Ico (0 : ℝ) 1, c / (1 - t) ≤ metricScalarAt (S.val.metric t) x := by
  obtain ⟨c, hc, hb⟩ := exists_standard_scalar_lower_bound_at_nonregular_point
  refine ⟨c, hc, fun S x t ht => hb S.val S.one_le_lifetime x ?_ t ht⟩
  rw [S.terminalRegularRegion_eq_bot]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_standard_scalar_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_standard_scalar_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_standard_scalar_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_standard_scalar_lower_bound

end DifferentialGeometry.PDE.RicciFlow
