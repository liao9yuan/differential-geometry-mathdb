import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.CarrierWeakConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.CarrierKineticEnergy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierWeakH1
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.CarrierIntegrability
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.CarrierAction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Compactness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.LowerSemicontinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {D : RealTimeInterval}

private theorem liminf_add_tendsto
    {q r : ℕ → ℝ} {q₀ r₀ : ℝ}
    (hq : q₀ ≤ _root_.Filter.liminf q _root_.Filter.atTop)
    (hq_lo : _root_.Filter.IsBoundedUnder (· ≥ ·) _root_.Filter.atTop q)
    (hq_hi : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop q)
    (hr : _root_.Filter.Tendsto r _root_.Filter.atTop (nhds r₀)) :
    q₀ + r₀ ≤ _root_.Filter.liminf (fun n ↦ q n + r n) atTop := by
  calc
    q₀ + r₀ ≤ _root_.Filter.liminf q _root_.Filter.atTop + r₀ := add_le_add_left hq r₀
    _ = _root_.Filter.liminf q _root_.Filter.atTop + _root_.Filter.liminf r atTop := by rw [hr.liminf_eq]
    _ ≤ _root_.Filter.liminf (fun n ↦ q n + r n) atTop := by
      with_unfolding_all
        exact le_liminf_add hq_lo hq_hi
          hr.isBoundedUnder_ge hr.isCoboundedUnder_ge

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.liminf_add_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.liminf_add_tendsto target :: scope.openDecls } }

private theorem sum_liminf_le
    {ι : Type*} (s : Finset ι) (q : ι → ℕ → ℝ)
    (hlo : ∀ i ∈ s, _root_.Filter.IsBoundedUnder (· ≥ ·) _root_.Filter.atTop (q i))
    (hhi : ∀ i ∈ s, _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop (q i)) :
    (∑ i ∈ s, _root_.Filter.liminf (q i) _root_.Filter.atTop) ≤
      liminf (∑ i ∈ s, q i) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change 0 ≤ _root_.Filter.liminf (fun _ : ℕ ↦ (0 : ℝ)) _root_.Filter.atTop
      rw [_root_.Filter.liminf_const]
  | @insert i s hi ih =>
      have hi_lo := hlo i (Finset.mem_insert_self i s)
      have hi_hi := hhi i (Finset.mem_insert_self i s)
      have hs_lo : ∀ j ∈ s, _root_.Filter.IsBoundedUnder (· ≥ ·) _root_.Filter.atTop (q j) :=
        fun j hj ↦ hlo j (Finset.mem_insert_of_mem hj)
      have hs_hi : ∀ j ∈ s, _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop (q j) :=
        fun j hj ↦ hhi j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (add_le_add_right (ih hs_lo hs_hi) _).trans
        (le_liminf_add hi_lo hi_hi
          (_root_.Filter.isBoundedUnder_ge_sum s hs_lo)
          (_root_.Filter.isBoundedUnder_le_sum s hs_hi).isCoboundedUnder_ge)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.sum_liminf_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.sum_liminf_le target :: scope.openDecls } }

theorem lKinetic_liminf_of_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hS : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (T a b : Real) (hab : a ≤ b)
    (p : M) (alpha : ℕ → Real → M)
    (u : ℕ → timeH1 E (b - a))
    (hsrc : ∀ n, _root_.Set.MapsTo (alpha n) (_root_.Set.Icc a b) (chartAt H p).source)
    (hrep : ∀ n, _root_.Set.EqOn (u n).toFun
      (fun r ↦ extChartAt I p (alpha n (a + r))) (_root_.Set.Icc (0 : Real) (b - a)))
    (uLim : timeH1 E (b - a)) {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ (extChartAt I p).target)
    (huK : ∀ n (r : _root_.Set.Icc (0 : Real) (b - a)),
      (u n).toFun r.1 ∈ K)
    (huLimK : ∀ r : _root_.Set.Icc (0 : Real) (b - a),
      uLim.toFun r.1 ∈ K)
    (hu : TendstoUniformly
      (fun n (r : _root_.Set.Icc (0 : Real) (b - a)) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) _root_.Filter.atTop)
    (hdu : ∀ z : timeL2 E (b - a), _root_.Filter.Tendsto
      (fun n ↦ _root_.Inner.inner Real (u n).deriv z) _root_.Filter.atTop
      (nhds (_root_.Inner.inner Real uLim.deriv z)))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    (∫ r in (0 : Real)..b - a, (1 / 2 : Real) * _root_.Inner.inner Real
      (chartGramOp (I := I) S.family p
        (T - (a + r) ^ 2, uLim.toFun r) (uLim.deriv r))
      (uLim.deriv r)) ≤
      _root_.Filter.liminf (fun n ↦ ∫ s in a..b, (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)) atTop := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hτc : ContinuousOn (fun r : Real ↦ T - (a + r) ^ 2)
      (_root_.Set.Icc (0 : Real) (b - a)) :=
    (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
  have hτregularity : _root_.Set.MapsTo (fun r : Real ↦ T - (a + r) ^ 2)
      (_root_.Set.Icc (0 : Real) (b - a)) D.carrier := by
    intro r hr
    exact hreg (a + r) ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  have hlim := chartKin_liminf_of_carrier (I := I) hS p hba
    (fun r : Real ↦ T - (a + r) ^ 2) hτc hτregularity hKc hKchart
    u uLim huK huLimK hu hdu
  have hseq :
      (fun n ↦ ∫ r in (0 : Real)..b - a, (1 / 2 : Real) * _root_.Inner.inner Real
        (chartGramOp (I := I) S.family p
          (T - (a + r) ^ 2, (u n).toFun r) ((u n).deriv r))
        ((u n).deriv r)) =
      (fun n ↦ ∫ s in a..b, (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)) := by
    funext n
    simpa only [smul_apply, real_inner_smul_left] using
      (lKinetic_eq_chart_integral S T (alpha n) p a b hab (u n)
        (hsrc n) (hrep n)).symm
  rw [hseq] at hlim
  exact hlim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lKinetic_liminf_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lKinetic_liminf_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lKinetic_liminf_of_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lKinetic_liminf_of_carrier

variable {N : Type u} [UniformSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N]

theorem lRegularizedAction_lim_compact_of_carrier
    (S : SolutionOn (I := I) (M := N) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := N) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := N) S)
    (T a b : Real) (hab : a ≤ b)
    (p : N) (alpha : ℕ → Real → N)
    (u : ℕ → timeH1 E (b - a))
    (hsrc : ∀ n, _root_.Set.MapsTo (alpha n) (_root_.Set.Icc a b) (chartAt H p).source)
    (hrep : ∀ n, _root_.Set.EqOn (u n).toFun
      (fun r ↦ extChartAt I p (alpha n (a + r))) (_root_.Set.Icc (0 : Real) (b - a)))
    (alphaLim : Real → N) (uLim : timeH1 E (b - a))
    (Q : Set N) (hQ : IsCompact Q)
    (hval : ∀ n s, s ∈ _root_.Set.Icc a b → alpha n s ∈ Q)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ (extChartAt I p).target)
    (huK : ∀ n (r : _root_.Set.Icc (0 : Real) (b - a)), (u n).toFun r.1 ∈ K)
    (huLimK : ∀ r : _root_.Set.Icc (0 : Real) (b - a), uLim.toFun r.1 ∈ K)
    (hu : TendstoUniformly
      (fun n (r : _root_.Set.Icc (0 : Real) (b - a)) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) _root_.Filter.atTop)
    (hdu : ∀ z : timeL2 E (b - a), _root_.Filter.Tendsto
      (fun n ↦ _root_.Inner.inner Real (u n).deriv z) _root_.Filter.atTop
      (nhds (_root_.Inner.inner Real uLim.deriv z)))
    (halpha : TendstoUniformly
      (fun n (s : _root_.Set.Icc a b) ↦ alpha n s.1)
      (fun s ↦ alphaLim s.1) _root_.Filter.atTop)
    (hact : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop
      (fun n ↦ lRegularizedAction S T (alpha n) a b))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    (∫ r in (0 : Real)..b - a, (1 / 2 : Real) * _root_.Inner.inner Real
        (chartGramOp (I := I) S.family p
          (T - (a + r) ^ 2, uLim.toFun r) (uLim.deriv r))
        (uLim.deriv r)) +
      (∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alphaLim s)) ≤
        liminf (fun n ↦ lRegularizedAction S T (alpha n) a b) atTop := by
  let kin : ℕ → Real := fun n ↦ ∫ s in a..b, (1 / 2 : Real) *
    (S.base.metric (T - s ^ 2)).inner (alpha n s)
      (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)
  let kinLim : Real := ∫ r in (0 : Real)..b - a, (1 / 2 : Real) * _root_.Inner.inner Real
    (chartGramOp (I := I) S.family p
      (T - (a + r) ^ 2, uLim.toFun r) (uLim.deriv r)) (uLim.deriv r)
  let pot : ℕ → Real := fun n ↦
    ∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s)
  let potLim : Real :=
    ∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alphaLim s)
  change kinLim + potLim ≤
    _root_.Filter.liminf (fun n ↦ lRegularizedAction S T (alpha n) a b) _root_.Filter.atTop
  have hkin : kinLim ≤ _root_.Filter.liminf kin atTop := by
    exact lKinetic_liminf_of_carrier S hMet T a b hab p alpha u hsrc hrep
      uLim hKc hKchart huK huLimK hu hdu hreg
  have hcont (n : ℕ) : ContinuousOn (alpha n) (_root_.Set.Icc a b) :=
    curve_cont_local I p (alpha n) (u n) hab (hsrc n) (hrep n)
  have hcarrier : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier :=
    fun s hs ↦ hreg s hs
  have hpot : _root_.Filter.Tendsto pot _root_.Filter.atTop (nhds potLim) := by
    exact lScalar_tendsto_compact (I := I) S hSc T a b hab hcarrier Q hQ
      alpha alphaLim hcont hval halpha
  have hkinInt (n : ℕ) : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s)
          (lVelocity (I := I) (alpha n) s)) _root_.MeasureTheory.MeasureSpace.volume a b :=
    intervalIntegrable_lKinetic_of_chartH1_of_carrier S hMet T (alpha n) p a b hab (u n)
      (hsrc n) (hrep n) hreg
  have hpotInt (n : ℕ) : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s)) _root_.MeasureTheory.MeasureSpace.volume a b :=
    lScalar_int (I := I) S hSc T a b (alpha n) (by
      simpa only [_root_.Set.uIcc_of_le hab] using hcarrier) (by
      simpa only [_root_.Set.uIcc_of_le hab] using hcont n)
  have hsplit (n : ℕ) :
      lRegularizedAction S T (alpha n) a b = kin n + pot n := by
    simpa only [lRegularizedAction, lRegularizedLagrangian, kin, pot] using
      intervalIntegral.integral_add (hkinInt n) (hpotInt n)
  have hkin_nonneg (n : ℕ) : 0 ≤ kin n := by
    change 0 ≤ ∫ s in a..b, (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)
    rw [lKinetic_eq_chart_integral S T (alpha n) p a b hab (u n)
      (hsrc n) (hrep n)]
    apply intervalIntegral.integral_nonneg (sub_nonneg.mpr hab)
    intro r _hr
    rw [smul_apply, real_inner_smul_left]
    exact mul_nonneg (by norm_num)
      (chartGramOp_nonneg (I := I) S.family p
        (T - (a + r) ^ 2, (u n).toFun r) ((u n).deriv r))
  have hkin_lo : _root_.Filter.IsBoundedUnder (· ≥ ·) _root_.Filter.atTop kin :=
    _root_.Filter.isBoundedUnder_of_eventually_ge (Eventually.of_forall hkin_nonneg)
  have hkin_hi : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop kin := by
    rcases hact with ⟨A, hA⟩
    change ∀ᶠ n in _root_.Filter.atTop, lRegularizedAction S T (alpha n) a b ≤ A at hA
    rcases hpot.isBoundedUnder_ge with ⟨B, hB⟩
    change ∀ᶠ n in _root_.Filter.atTop, pot n ≥ B at hB
    refine ⟨A - B, ?_⟩
    change ∀ᶠ n in _root_.Filter.atTop, kin n ≤ A - B
    filter_upwards [hA, hB] with n hn hpn
    rw [hsplit n] at hn
    linarith
  have hsum := liminf_add_tendsto hkin hkin_lo hkin_hi hpot
  have hseq : (fun n ↦ kin n + pot n) =
      (fun n ↦ lRegularizedAction S T (alpha n) a b) := by
    funext n
    exact (hsplit n).symm
  rw [hseq] at hsum
  exact hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_lim_compact_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_lim_compact_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_lim_compact_of_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_lim_compact_of_carrier

theorem lRegularizedAction_fin_compact_of_carrier
    (S : SolutionOn (I := I) (M := N) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := N) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := N) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → N) (alpha : Nat → Real → N) (gamma : Real → N)
    (Q : Set N) (hQ : IsCompact Q)
    (hval : ∀ n s, s ∈ _root_.Set.Icc a b → alpha n s ∈ Q)
    (u : (i : Fin m) → Nat → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i n, _root_.Set.MapsTo (alpha n)
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i n, _root_.Set.EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)))
    (K : Fin m → Set E) (hKc : ∀ i, IsCompact (K i))
    (hKchart : ∀ i, K i ⊆ (extChartAt I (p i)).target)
    (huK : ∀ i n (r : _root_.Set.Icc (0 : Real) (partitionIntervalLength t i)),
      (u i n).toFun r.1 ∈ K i)
    (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hu : ∀ i, TendstoUniformly
      (fun n (r : _root_.Set.Icc (0 : Real) (partitionIntervalLength t i)) ↦ (u i n).toFun r.1)
      (fun r ↦ (uLim i).toFun r.1) _root_.Filter.atTop)
    (hdu : ∀ i (z : timeL2 E (partitionIntervalLength t i)), _root_.Filter.Tendsto
      (fun n ↦ _root_.Inner.inner Real (u i n).deriv z) _root_.Filter.atTop
      (nhds (_root_.Inner.inner Real (uLim i).deriv z)))
    (halpha : TendstoUniformly
      (fun n (s : _root_.Set.Icc a b) ↦ alpha n s.1)
      (fun s ↦ gamma s.1) _root_.Filter.atTop)
    (hact : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop
      (fun n ↦ lRegularizedAction S T (alpha n) a b))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    (∑ i : Fin m, (
      (∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * _root_.Inner.inner Real
        (chartGramOp (I := I) S.family (p i)
          (T - (t i.castSucc + r) ^ 2, (uLim i).toFun r)
          ((uLim i).deriv r))
        ((uLim i).deriv r)) +
      (∫ s in (t i.castSucc)..(t i.succ),
        2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s)))) ≤
      liminf (fun n ↦ lRegularizedAction S T (alpha n) a b) atTop := by
  classical
  have hab : a ≤ b := by
    rw [← ht0, ← htlast]
    exact htmono (Fin.zero_le _)
  have hleft (i : Fin m) : a ≤ t i.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hright (i : Fin m) : t i.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hreg_i (i : Fin m) (s : Real) (hs : s ∈ _root_.Set.Icc (t i.castSucc) (t i.succ)) :
      T - s ^ 2 ∈ D.carrier :=
    hreg s ⟨(hleft i).trans hs.1, hs.2.trans (hright i)⟩
  have hcarrier : ∀ s ∈ _root_.Set.uIcc a b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    apply hreg s
    simpa only [_root_.Set.uIcc_of_le hab] using hs
  have hcarrier_i (i : Fin m) :
      ∀ s ∈ _root_.Set.uIcc (t i.castSucc) (t i.succ), T - s ^ 2 ∈ D.carrier := by
    intro s hs
    apply hreg_i i s
    simpa only [_root_.Set.uIcc_of_le (hseg i)] using hs
  have hcont (i : Fin m) (n : Nat) :
      ContinuousOn (alpha n) (_root_.Set.Icc (t i.castSucc) (t i.succ)) :=
    curve_cont_local I (p i) (alpha n) (u i n) (hseg i) (hsrc i n) (hrep i n)
  have hkinInt (i : Fin m) (n : Nat) : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s))
      volume (t i.castSucc) (t i.succ) :=
    intervalIntegrable_lKinetic_of_chartH1_of_carrier S hMet T (alpha n) (p i) (t i.castSucc) (t i.succ)
      (hseg i) (u i n) (hsrc i n) (hrep i n) (hreg_i i)
  have hpotInt (i : Fin m) (n : Nat) : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s))
      volume (t i.castSucc) (t i.succ) :=
    lScalar_int (I := I) S hSc T (t i.castSucc) (t i.succ) (alpha n)
      (hcarrier_i i) (by
        simpa only [_root_.Set.uIcc_of_le (hseg i)] using hcont i n)
  have hLag (i : Fin m) (n : Nat) : IntervalIntegrable
      (lRegularizedLagrangian S T (alpha n)) _root_.MeasureTheory.MeasureSpace.volume (t i.castSucc) (t i.succ) := by
    with_unfolding_all exact (hkinInt i n).add (hpotInt i n)
  let q : Fin m → Nat → Real := fun i n ↦
    lRegularizedAction S T (alpha n) (t i.castSucc) (t i.succ)
  let kin : Fin m → Nat → Real := fun i n ↦
    ∫ s in t i.castSucc..t i.succ, (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)
  let pot : Fin m → Nat → Real := fun i n ↦
    ∫ s in t i.castSucc..t i.succ,
      2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s)
  have hsplit (i : Fin m) (n : Nat) : q i n = kin i n + pot i n := by
    simpa only [q, kin, pot, lRegularizedAction, lRegularizedLagrangian] using
      intervalIntegral.integral_add (hkinInt i n) (hpotInt i n)
  have hkinNonneg (i : Fin m) (n : Nat) : 0 ≤ kin i n := by
    change 0 ≤ ∫ s in t i.castSucc..t i.succ, (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)
    rw [lKinetic_eq_chart_integral S T (alpha n) (p i) (t i.castSucc) (t i.succ)
      (hseg i) (u i n) (hsrc i n) (hrep i n)]
    apply intervalIntegral.integral_nonneg (sub_nonneg.mpr (hseg i))
    intro r _hr
    rw [smul_apply, real_inner_smul_left]
    exact mul_nonneg (by norm_num)
      (chartGramOp_nonneg (I := I) S.family (p i)
        (T - (t i.castSucc + r) ^ 2, (u i n).toFun r) ((u i n).deriv r))
  obtain ⟨C, hC⟩ := lScalar_lower_compact (I := I) S hSc T a b hcarrier Q hQ
  have hpotLower (i : Fin m) (n : Nat) : C * partitionIntervalLength t i ≤ pot i n := by
    have hmono := intervalIntegral.integral_mono_on (hseg i)
      intervalIntegrable_const (hpotInt i n) (fun s hs ↦
        hC s (by
          simpa only [_root_.Set.uIcc_of_le hab] using
            ⟨(hleft i).trans hs.1, hs.2.trans (hright i)⟩) (alpha n s)
          (hval n s ⟨(hleft i).trans hs.1, hs.2.trans (hright i)⟩))
    rw [intervalIntegral.integral_const] at hmono
    simpa only [pot, partitionIntervalLength, smul_eq_mul, mul_comm] using hmono
  have hqLower (i : Fin m) (n : Nat) : C * partitionIntervalLength t i ≤ q i n := by
    rw [hsplit]
    linarith [hkinNonneg i n, hpotLower i n]
  let tNat : Nat → Real := fun k ↦
    if hk : k < m + 1 then t ⟨k, hk⟩ else b
  have hsum (n : Nat) : (∑ i : Fin m, q i n) =
      lRegularizedAction S T (alpha n) a b := by
    calc
      (∑ i : Fin m, q i n) =
          ∑ k ∈ Finset.range m,
            lRegularizedAction S T (alpha n) (tNat k) (tNat (k + 1)) := by
        rw [Finset.sum_fin_eq_sum_range]
        simp only [q]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < m := Finset.mem_range.mp hk
        have hk0 : k ≤ m := Nat.le_of_lt hk'
        have hk1 : k + 1 ≤ m := Nat.succ_le_of_lt hk'
        rw [dif_pos hk']
        simp only [tNat, Nat.lt_succ_iff, dif_pos hk0, dif_pos hk1]
        congr 2
      _ = lRegularizedAction S T (alpha n) (tNat 0) (tNat m) :=
        lRegularizedAction_sum S T (alpha n) (fun k hk ↦ by
          have hk' : k < m := hk
          simp only [tNat, dif_pos (Nat.lt_trans hk' (Nat.lt_succ_self m)),
            dif_pos (Nat.succ_lt_succ hk')]
          with_unfolding_all exact hLag ⟨k, hk'⟩ n)
      _ = lRegularizedAction S T (alpha n) a b := by
        simp only [tNat, dif_pos (Nat.succ_pos m),
          dif_pos (Nat.lt_succ_self m)]
        change lRegularizedAction S T (alpha n) (t 0) (t (Fin.last m)) =
          lRegularizedAction S T (alpha n) a b
        rw [ht0, htlast]
  obtain ⟨A, hA⟩ := hact
  change ∀ᶠ n in _root_.Filter.atTop, lRegularizedAction S T (alpha n) a b ≤ A at hA
  have hqUpper (i : Fin m) : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop (q i) := by
    refine ⟨A - (∑ j ∈ (Finset.univ.erase i), C * partitionIntervalLength t j), ?_⟩
    change ∀ᶠ n in _root_.Filter.atTop,
      q i n ≤ A - (∑ j ∈ (Finset.univ.erase i), C * partitionIntervalLength t j)
    filter_upwards [hA] with n hn
    rw [← hsum n] at hn
    have hrest : (∑ j ∈ (Finset.univ.erase i), C * partitionIntervalLength t j) ≤
        ∑ j ∈ (Finset.univ.erase i), q j n :=
      Finset.sum_le_sum fun j hj ↦ hqLower j n
    have hdecomp : q i n + (∑ j ∈ (Finset.univ.erase i), q j n) =
        ∑ j : Fin m, q j n :=
      Finset.add_sum_erase Finset.univ (fun j ↦ q j n) (Finset.mem_univ i)
    linarith
  have huLimK (i : Fin m) (r : _root_.Set.Icc (0 : Real) (partitionIntervalLength t i)) :
      (uLim i).toFun r.1 ∈ K i := by
    apply (hKc i).isClosed.mem_of_tendsto ((hu i).tendsto_at r)
    exact Eventually.of_forall fun n ↦ huK i n r
  have hlocal (i : Fin m) :
      (∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * _root_.Inner.inner Real
          (chartGramOp (I := I) S.family (p i)
            (T - (t i.castSucc + r) ^ 2, (uLim i).toFun r)
            ((uLim i).deriv r))
          ((uLim i).deriv r)) +
        (∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s)) ≤
        liminf (q i) atTop := by
    let inc : _root_.Set.Icc (t i.castSucc) (t i.succ) → _root_.Set.Icc a b := fun s ↦
      ⟨s.1, (hleft i).trans s.2.1, s.2.2.trans (hright i)⟩
    have halpha_i := halpha.comp inc
    apply lRegularizedAction_lim_compact_of_carrier S hMet hSc T (t i.castSucc) (t i.succ) (hseg i)
      (p i) alpha (u i) (hsrc i) (hrep i) gamma (uLim i) Q hQ
      (fun n s hs ↦ hval n s
        ⟨(hleft i).trans hs.1, hs.2.trans (hright i)⟩)
      (hKc i) (hKchart i) (huK i) (huLimK i) (hu i) (hdu i)
    · with_unfolding_all exact halpha_i
    · exact hqUpper i
    · exact hreg_i i
  have hlo : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      IsBoundedUnder (· ≥ ·) _root_.Filter.atTop (q i) := fun i _ ↦
    _root_.Filter.isBoundedUnder_of_eventually_ge (Eventually.of_forall (hqLower i))
  have hhi : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      IsBoundedUnder (· ≤ ·) _root_.Filter.atTop (q i) := fun i _ ↦ hqUpper i
  have hsumlim : (∑ i : Fin m, _root_.Filter.liminf (q i) _root_.Filter.atTop) ≤
      liminf (fun n ↦ ∑ i : Fin m, q i n) atTop := by
    have hsumfun : (∑ i : Fin m, q i) = fun n ↦ ∑ i : Fin m, q i n := by
      funext n
      simp only [Finset.sum_apply]
    rw [← hsumfun]
    simpa using sum_liminf_le (Finset.univ : Finset (Fin m)) q hlo hhi
  calc
    (∑ i : Fin m, (
      (∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * _root_.Inner.inner Real
        (chartGramOp (I := I) S.family (p i)
          (T - (t i.castSucc + r) ^ 2, (uLim i).toFun r)
          ((uLim i).deriv r))
        ((uLim i).deriv r)) +
      (∫ s in (t i.castSucc)..(t i.succ),
        2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s)))) ≤
        ∑ i : Fin m, _root_.Filter.liminf (q i) atTop :=
      Finset.sum_le_sum fun i _ ↦ hlocal i
    _ ≤ _root_.Filter.liminf (fun n ↦ ∑ i : Fin m, q i n) atTop := hsumlim
    _ = _root_.Filter.liminf (fun n ↦ lRegularizedAction S T (alpha n) a b) atTop := by
      congr 1
      funext n
      exact hsum n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_fin_compact_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_fin_compact_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_fin_compact_of_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_fin_compact_of_carrier


end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology _root_.Submission.Topology _root_.Interval
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [UniformSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem exists_chartH1_representation_of_tendstoUniformly_of_lRegularizedAction_le_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b A : ℝ) (hab : a ≤ b)
    (alpha : ℕ → ℝ → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (alpha n) (_root_.Set.Icc a b))
    (Q : Set M) (hQ : IsCompact Q)
    (hval : ∀ n s, s ∈ _root_.Set.Icc a b → alpha n s ∈ Q)
    (hact : ∀ n, lRegularizedAction S T (alpha n) a b ≤ A)
    (gamma : ℝ → M)
    (hconvG : TendstoUniformly (fun n (s : _root_.Set.Icc a b) ↦ alpha n s.1)
      (fun s ↦ gamma s.1) _root_.Filter.atTop)
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (p : Fin m → M)
      (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      Monotone t ∧ t 0 = a ∧ t (Fin.last m) = b ∧
      (∀ i, _root_.Set.MapsTo gamma (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source) ∧
      (∀ i, _root_.Set.EqOn (uLim i).toFun
        (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
        (_root_.Set.Icc (0 : ℝ) (partitionIntervalLength t i))) ∧
      IntervalIntegrable (lRegularizedLagrangian S T gamma) _root_.MeasureTheory.MeasureSpace.volume a b ∧
      ∃ chi : ℕ → ℕ, StrictMono chi ∧
        lRegularizedAction S T gamma a b ≤
          liminf (fun n ↦ lRegularizedAction S T (alpha (chi n)) a b) atTop := by
  classical
  have hLag (n : ℕ) : IntervalIntegrable (lRegularizedLagrangian S T (alpha n)) _root_.MeasureTheory.MeasureSpace.volume a b :=
    intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier S hMet hSc T a b hab
      (alpha n) (halpha n) hreg
  have hgamma : ContinuousOn gamma (_root_.Set.Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hconvG.continuous
      ((Eventually.of_forall fun n ↦ (halpha n).continuousOn.domRestrict).frequently)
  let : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  obtain ⟨q, hq0, hqmono, ⟨m, hqm⟩, hpieces⟩ :=
    DifferentialGeometry.Geometry.exists_compact_chart_subdivision (H := H) hab
      hgamma
  let t : Fin (m + 1) → Real := fun i ↦ (q i).1
  have htmono : Monotone t := fun i j hij ↦ hqmono hij
  have ht0 : t 0 = a := congrArg Subtype.val hq0
  have htlast : t (Fin.last m) = b := congrArg Subtype.val (hqm m le_rfl)
  choose p Kman hKman hKsrc hgammaK using fun i : Fin m ↦ hpieces i
  obtain ⟨N, Kcoord, u, hKc, hKchart, hsrc, hrep, huK⟩ :=
    exists_chartH1_coordinates_with_compact_range_of_tendstoUniformly (I := I) a b t htmono ht0 htlast p Kman hKman hKsrc
      gamma hgamma (fun i ↦ hgammaK i)
      alpha halpha hconvG
  let beta : Nat → Real → M := fun n ↦ alpha (n + N)
  have hLagBeta : ∀ n, IntervalIntegrable (lRegularizedLagrangian S T (beta n)) _root_.MeasureTheory.MeasureSpace.volume a b :=
    fun n ↦ hLag _
  have hactBeta : ∀ n, lRegularizedAction S T (beta n) a b ≤ A := fun n ↦ hact _
  obtain ⟨psi, uLim, hpsi, hdu, hu⟩ :=
    exists_chartH1_weakly_convergent_subsequence_of_compact_range_carrier
      S hMet hSc T a b t htmono ht0 htlast p beta Q hQ
      (fun n s hs ↦ hval (n + N) s hs) hLagBeta u
      (fun i n ↦ by simpa only [beta, Nat.add_comm] using hsrc i n)
      (fun i n ↦ by simpa only [beta, Nat.add_comm] using hrep i n)
      Kcoord hKc (fun i ↦ (hKchart i).trans interior_subset) (fun i n r ↦ by
        simpa only [beta, Nat.add_comm] using huK i n r)
      hactBeta hreg
  let chi : Nat → Nat := fun n ↦ psi n + N
  have hpsiN : StrictMono (fun n ↦ psi n + N) := fun i j hij ↦
    by simpa only [Nat.add_comm] using add_lt_add_right (hpsi hij) N
  have hchi : StrictMono chi := hpsiN
  have hconv : TendstoUniformly
      (fun n (s : _root_.Set.Icc a b) ↦ alpha (chi n) s.1)
      (fun s ↦ gamma s.1) atTop := by
    intro V hV
    obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (hconvG V hV)
    filter_upwards [hpsi.tendsto_atTop.eventually (_root_.Filter.eventually_ge_atTop k)]
      with n hn
    exact hk (psi n + N) (hn.trans (Nat.le_add_right _ _))
  have hsrc' (i : Fin m) (n : Nat) : _root_.Set.MapsTo (alpha (chi n))
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source := by
    simpa only [chi, beta, Nat.add_comm] using hsrc i (psi n)
  have hrep' (i : Fin m) (n : Nat) : _root_.Set.EqOn (u i (psi n)).toFun
      (fun r ↦ extChartAt I (p i) (alpha (chi n) (t i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)) := by
    simpa only [chi, beta, Nat.add_comm] using hrep i (psi n)
  have huK' (i : Fin m) (n : Nat) (r : _root_.Set.Icc (0 : Real) (partitionIntervalLength t i)) :
      (u i (psi n)).toFun r.1 ∈ Kcoord i := by
    simpa only [beta, Nat.add_comm] using huK i (psi n) r
  have hgammaSource (i : Fin m) : _root_.Set.MapsTo gamma
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source :=
    (hgammaK i).mono_right (interior_subset.trans (hKsrc i))
  have hlimRep (i : Fin m) : _root_.Set.EqOn (uLim i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)) := by
    intro r hr
    have hpoint : _root_.Filter.Tendsto (fun n ↦ alpha (chi n) (t i.castSucc + r)) _root_.Filter.atTop
        (nhds (gamma (t i.castSucc + r))) := by
      have hsub : t i.castSucc + r ∈ _root_.Set.Icc a b := by
        have hleft : a ≤ t i.castSucc := by rw [← ht0]; exact htmono (Fin.zero_le _)
        have hright : t i.succ ≤ b := by rw [← htlast]; exact htmono (Fin.le_last _)
        change r ∈ _root_.Set.Icc (0 : Real) (t i.succ - t i.castSucc) at hr
        exact ⟨by linarith [hleft, hr.1], by linarith [hr.2, hright]⟩
      exact hconv.tendsto_at ⟨t i.castSucc + r, hsub⟩
    have hrpiece : t i.castSucc + r ∈ _root_.Set.Icc (t i.castSucc) (t i.succ) := by
      change r ∈ _root_.Set.Icc (0 : Real) (t i.succ - t i.castSucc) at hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    let rsub : _root_.Set.Icc (0 : Real) (partitionIntervalLength t i) := ⟨r, hr⟩
    have hExtSource : gamma (t i.castSucc + r) ∈ (extChartAt I (p i)).source := by
      rw [extChartAt_source]
      exact hgammaSource i hrpiece
    have hchart : _root_.Filter.Tendsto (fun n ↦
        extChartAt I (p i) (alpha (chi n) (t i.castSucc + r))) _root_.Filter.atTop
        (nhds (extChartAt I (p i) (gamma (t i.castSucc + r)))) :=
      (continuousAt_extChartAt' (I := I) hExtSource).tendsto.comp hpoint
    have huPoint := (hu i).tendsto_at rsub
    have huChart : _root_.Filter.Tendsto (fun n ↦
        extChartAt I (p i) (alpha (chi n) (t i.castSucc + r))) _root_.Filter.atTop
        (nhds ((uLim i).toFun r)) := by
      apply huPoint.congr'
      filter_upwards with n
      exact hrep' i n rsub.2
    exact tendsto_nhds_unique huChart hchart
  have hactBound : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop
      (fun n ↦ lRegularizedAction S T (alpha (chi n)) a b) :=
    _root_.Filter.isBoundedUnder_of_eventually_le (Eventually.of_forall fun n ↦ hact (chi n))
  have hlsc := lRegularizedAction_fin_compact_of_carrier S hMet hSc T a b t htmono ht0 htlast p
    (fun n ↦ alpha (chi n)) gamma Q hQ
    (fun n s hs ↦ hval (psi n + N) s hs)
    (fun i n ↦ u i (psi n))
    hsrc' hrep' Kcoord hKc (fun i ↦ (hKchart i).trans interior_subset) huK' uLim
    (fun i ↦ by intro V hV; exact hu i V hV)
    (fun i z ↦ by simpa only using hdu i z)
    hconv hactBound hreg
  have haction := lRegularizedAction_chart_of_carrier S hMet hSc T a b t htmono ht0 htlast
    p gamma uLim hgammaSource hlimRep hreg
  have hLagLim := intervalIntegrable_lRegularizedLagrangian_of_chartH1_partition_of_carrier
    S hMet hSc T a b t htmono ht0 htlast p gamma uLim hgammaSource hlimRep hreg
  refine ⟨m, t, p, uLim, htmono, ht0, htlast, hgammaSource, hlimRep, hLagLim,
    chi, hchi, ?_⟩
  rw [haction]
  exact hlsc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_chartH1_representation_of_tendstoUniformly_of_lRegularizedAction_le_on_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_chartH1_representation_of_tendstoUniformly_of_lRegularizedAction_le_on_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_chartH1_representation_of_tendstoUniformly_of_lRegularizedAction_le_on_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_chartH1_representation_of_tendstoUniformly_of_lRegularizedAction_le_on_carrier

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
