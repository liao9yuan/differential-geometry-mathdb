import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierKineticAction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.TwoPieceSplicing
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.KineticEnergy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.Scalar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped _root_.BigOperators _root_.ContDiff _root_.Manifold _root_.Topology _root_.Interval

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [UniformSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private theorem integral_fin_partition
    {m : ℕ} (t : Fin (m + 1) → ℝ) (f : ℝ → ℝ)
    (hint : ∀ i : Fin m, IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume (t i.castSucc) (t i.succ)) :
    IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume (t 0) (t (Fin.last m)) ∧
      (∑ i : Fin m, ∫ s in t i.castSucc..t i.succ, f s) =
        ∫ s in t 0..t (Fin.last m), f s := by
  classical
  let tNat : ℕ → ℝ := fun k ↦ if hk : k < m + 1 then t ⟨k, hk⟩ else t (Fin.last m)
  have hNat (k : ℕ) (hk : k < m) :
      IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume (tNat k) (tNat (k + 1)) := by
    dsimp only [tNat]
    rw [dif_pos (Nat.lt_trans hk (Nat.lt_succ_self m)), dif_pos (Nat.succ_lt_succ hk)]
    convert hint ⟨k, hk⟩ using 1 <;> rfl
  have hwhole := IntervalIntegrable.trans_iterate hNat
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hNat
  have hends : tNat 0 = t 0 ∧ tNat m = t (Fin.last m) := by
    constructor <;> simp only [tNat, dif_pos (Nat.succ_pos m),
      dif_pos (Nat.lt_succ_self m)] <;> rfl
  refine ⟨by simpa only [hends.1, hends.2] using hwhole, ?_⟩
  calc
    (∑ i : Fin m, ∫ s in t i.castSucc..t i.succ, f s) =
        ∑ k ∈ Finset.range m, ∫ s in tNat k..tNat (k + 1), f s := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < m := Finset.mem_range.mp hk
      have hk0 : k ≤ m := Nat.le_of_lt hk'
      have hk1 : k + 1 ≤ m := Nat.succ_le_of_lt hk'
      rw [dif_pos hk']
      simp only [tNat, Nat.lt_succ_iff, dif_pos hk0, dif_pos hk1]
      congr 2
    _ = ∫ s in t 0..t (Fin.last m), f s := by
      simpa only [hends.1, hends.2] using hsum

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.integral_fin_partition
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.integral_fin_partition target :: scope.openDecls } }

private theorem action_partition_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) {m : ℕ} (t : Fin (m + 1) → ℝ)
    (htmono : Monotone t) (ht0 : t 0 = a) (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : ℝ → M)
    (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i, _root_.Set.MapsTo gamma (_root_.Set.Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrep : ∀ i, _root_.Set.EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (_root_.Set.Icc (0 : ℝ) (partitionIntervalLength t i)))
    (hback : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    IntervalIntegrable (lRegularizedLagrangian S T gamma) _root_.MeasureTheory.MeasureSpace.volume a b ∧
      lRegularizedAction S T gamma a b =
        ∑ i : Fin m, lRegularizedAction S T gamma (t i.castSucc) (t i.succ) := by
  have hleft (i : Fin m) : a ≤ t i.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hright (i : Fin m) : t i.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hint (i : Fin m) : IntervalIntegrable (lRegularizedLagrangian S T gamma) _root_.MeasureTheory.MeasureSpace.volume
      (t i.castSucc) (t i.succ) := by
    apply lRegLag_integrable_chart_on_carrier S hMet hSc T
      (t i.castSucc) (t i.succ) (htmono Fin.castSucc_lt_succ.le)
      (p i) gamma (u i) (hsrc i) (hrep i)
    intro s hs
    apply hback s
    exact ⟨(hleft i).trans hs.1, hs.2.trans (hright i)⟩
  obtain ⟨hwhole, hsum⟩ := integral_fin_partition t (lRegularizedLagrangian S T gamma) hint
  refine ⟨by simpa only [ht0, htlast] using hwhole, ?_⟩
  simpa only [lRegularizedAction, ht0, htlast] using hsum.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.action_partition_on_carrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.action_partition_on_carrier target :: scope.openDecls } }

private theorem action_split_chart_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) (hab : a ≤ b) (p : M) (alpha : ℝ → M)
    (u : timeH1 E (b - a))
    (hsrc : _root_.Set.MapsTo alpha (_root_.Set.Icc a b) (chartAt H p).source)
    (hrep : _root_.Set.EqOn u.toFun (fun r ↦ extChartAt I p (alpha (a + r)))
      (_root_.Set.Icc (0 : ℝ) (b - a)))
    (hback : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    lRegularizedAction S T alpha a b =
      (∫ r in (0 : ℝ)..b - a, (1 / 2 : ℝ) * _root_.Inner.inner ℝ
        (chartGramOp S.family p (T - (a + r) ^ 2, u.toFun r) (u.deriv r))
        (u.deriv r)) +
      (∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) := by
  have hLag := lRegLag_integrable_chart_on_carrier S hMet hSc T a b hab
    p alpha u hsrc hrep hback
  have hPot := lScalar_int (I := I) S hSc T a b alpha
    (by simpa only [_root_.Set.uIcc_of_le hab] using hback)
    (by simpa only [_root_.Set.uIcc_of_le hab] using curve_cont_local I p alpha u hab hsrc hrep)
  have hKin : IntervalIntegrable (fun s ↦ (1 / 2 : ℝ) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) _root_.MeasureTheory.MeasureSpace.volume a b := by
    simpa only [lRegularizedLagrangian, Pi.sub_apply, add_sub_cancel_right] using hLag.sub hPot
  have hsplit := intervalIntegral.integral_add hKin hPot
  have hcoord := lKinetic_eq_chart_integral S T alpha p a b hab u hsrc hrep
  change lRegularizedAction S T alpha a b = _ at hsplit
  rw [hcoord] at hsplit
  simpa only [smul_apply, real_inner_smul_left] using hsplit

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.action_split_chart_on_carrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.action_split_chart_on_carrier target :: scope.openDecls } }

private theorem action_chart_tendsto_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) (hab : a ≤ b) (p : M)
    (alpha : ℕ → ℝ → M) (gamma : ℝ → M)
    (u : ℕ → timeH1 E (b - a)) (uLim : timeH1 E (b - a))
    (hsrc : ∀ n, _root_.Set.MapsTo (alpha n) (_root_.Set.Icc a b) (chartAt H p).source)
    (hrep : ∀ n, _root_.Set.EqOn (u n).toFun
      (fun r ↦ extChartAt I p (alpha n (a + r))) (_root_.Set.Icc (0 : ℝ) (b - a)))
    (hsrcLim : _root_.Set.MapsTo gamma (_root_.Set.Icc a b) (chartAt H p).source)
    (hrepLim : _root_.Set.EqOn uLim.toFun
      (fun r ↦ extChartAt I p (gamma (a + r))) (_root_.Set.Icc (0 : ℝ) (b - a)))
    (K : Set E) (hKc : IsCompact K) (hKchart : K ⊆ interior (extChartAt I p).target)
    (huK : ∀ n (r : _root_.Set.Icc (0 : ℝ) (b - a)), (u n).toFun r.1 ∈ K)
    (huLimK : ∀ r : _root_.Set.Icc (0 : ℝ) (b - a), uLim.toFun r.1 ∈ K)
    (hu : _root_.Filter.Tendsto u _root_.Filter.atTop (𝓝 uLim))
    (hunif : TendstoUniformly (fun n (s : _root_.Set.Icc a b) ↦ alpha n s.1)
      (fun s ↦ gamma s.1) _root_.Filter.atTop)
    (hback : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    _root_.Filter.Tendsto (fun n ↦ lRegularizedAction S T (alpha n) a b) _root_.Filter.atTop
      (𝓝 (lRegularizedAction S T gamma a b)) := by
  have hclock : _root_.Set.MapsTo (fun r : ℝ ↦ T - (a + r) ^ 2)
      (_root_.Set.Icc (0 : ℝ) (b - a)) D.carrier := by
    intro r hr
    exact hback (a + r) ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hkin := chartKin_tendsto_on_carrier hMet p (sub_nonneg.mpr hab)
    (fun r : ℝ ↦ T - (a + r) ^ 2)
    (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
    hclock hKc hKchart u uLim huK huLimK hu
  let Q : Set M := (extChartAt I p).symm '' K
  have hQc : IsCompact Q := hKc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := I) p).mono
      (fun z hz ↦ interior_subset (hKchart hz)))
  have hval : ∀ n s, s ∈ _root_.Set.Icc a b → alpha n s ∈ Q := by
    intro n s hs
    have hr : s - a ∈ _root_.Set.Icc (0 : ℝ) (b - a) :=
      ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩
    refine ⟨extChartAt I p (alpha n s), ?_, ?_⟩
    · have h := huK n ⟨s - a, hr⟩
      rw [hrep n hr] at h
      have hshift : a + (s - a) = s := by ring
      simpa only [hshift] using h
    · exact (extChartAt I p).left_inv (by
        rw [extChartAt_source]
        exact hsrc n hs)
  have hpot := lScalar_tendsto_compact (I := I) S hSc T a b hab hback Q hQc
    alpha gamma (fun n ↦ curve_cont_local I p (alpha n) (u n) hab (hsrc n) (hrep n))
    hval hunif
  have hsum := hkin.add hpot
  have hseq : (fun n ↦ lRegularizedAction S T (alpha n) a b) =
      (fun n ↦
        (∫ r in (0 : ℝ)..b - a, (1 / 2 : ℝ) * _root_.Inner.inner ℝ
          (chartGramOp S.family p (T - (a + r) ^ 2, (u n).toFun r) ((u n).deriv r))
          ((u n).deriv r)) +
        (∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s))) := by
    funext n
    exact action_split_chart_on_carrier S hMet hSc T a b hab p (alpha n)
      (u n) (hsrc n) (hrep n) hback
  rw [hseq, action_split_chart_on_carrier S hMet hSc T a b hab p gamma
    uLim hsrcLim hrepLim hback]
  exact hsum

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.action_chart_tendsto_on_carrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.action_chart_tendsto_on_carrier target :: scope.openDecls } }

private theorem action_finite_tendsto_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) {m : ℕ} (t : Fin (m + 1) → ℝ)
    (htmono : Monotone t) (ht0 : t 0 = a) (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (alpha : ℕ → ℝ → M) (gamma : ℝ → M)
    (u : (i : Fin m) → ℕ → timeH1 E (partitionIntervalLength t i))
    (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i n, _root_.Set.MapsTo (alpha n) (_root_.Set.Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrep : ∀ i n, _root_.Set.EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (_root_.Set.Icc (0 : ℝ) (partitionIntervalLength t i)))
    (hsrcLim : ∀ i, _root_.Set.MapsTo gamma (_root_.Set.Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrepLim : ∀ i, _root_.Set.EqOn (uLim i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (_root_.Set.Icc (0 : ℝ) (partitionIntervalLength t i)))
    (K : Fin m → Set E) (hKc : ∀ i, IsCompact (K i))
    (hKchart : ∀ i, K i ⊆ interior (extChartAt I (p i)).target)
    (huK : ∀ i n (r : _root_.Set.Icc (0 : ℝ) (partitionIntervalLength t i)), (u i n).toFun r.1 ∈ K i)
    (huLimK : ∀ i (r : _root_.Set.Icc (0 : ℝ) (partitionIntervalLength t i)), (uLim i).toFun r.1 ∈ K i)
    (hu : ∀ i, _root_.Filter.Tendsto (u i) _root_.Filter.atTop (𝓝 (uLim i)))
    (hunif : TendstoUniformly (fun n (s : _root_.Set.Icc a b) ↦ alpha n s.1)
      (fun s ↦ gamma s.1) _root_.Filter.atTop)
    (hback : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    _root_.Filter.Tendsto (fun n ↦ lRegularizedAction S T (alpha n) a b) _root_.Filter.atTop
      (𝓝 (lRegularizedAction S T gamma a b)) := by
  have hsub (i : Fin m) : _root_.Set.Icc (t i.castSucc) (t i.succ) ⊆ _root_.Set.Icc a b := by
    apply _root_.Set.Icc_subset_Icc
    · rw [← ht0]
      exact htmono (Fin.zero_le _)
    · rw [← htlast]
      exact htmono (Fin.le_last _)
  have hpiece (i : Fin m) : _root_.Filter.Tendsto
      (fun n ↦ lRegularizedAction S T (alpha n) (t i.castSucc) (t i.succ)) _root_.Filter.atTop
      (𝓝 (lRegularizedAction S T gamma (t i.castSucc) (t i.succ))) := by
    apply action_chart_tendsto_on_carrier S hMet hSc T (t i.castSucc) (t i.succ)
      (htmono Fin.castSucc_lt_succ.le) (p i) alpha gamma (u i) (uLim i)
      (hsrc i) (hrep i) (hsrcLim i) (hrepLim i)
      (K i) (hKc i) (hKchart i) (huK i) (huLimK i) (hu i)
    · exact hunif.comp (fun s : _root_.Set.Icc (t i.castSucc) (t i.succ) ↦
        (⟨s.1, hsub i s.2⟩ : _root_.Set.Icc a b))
    · exact fun s hs ↦ hback s (hsub i hs)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ ↦ hpiece i)
  have hseq : (fun n ↦ lRegularizedAction S T (alpha n) a b) =
      (fun n ↦ ∑ i : Fin m, lRegularizedAction S T (alpha n) (t i.castSucc) (t i.succ)) := by
    funext n
    exact (action_partition_on_carrier S hMet hSc T a b t htmono ht0 htlast
      p (alpha n) (fun i ↦ u i n) (fun i ↦ hsrc i n) (fun i ↦ hrep i n) hback).2
  rw [hseq, (action_partition_on_carrier S hMet hSc T a b t htmono ht0 htlast
    p gamma uLim hsrcLim hrepLim hback).2]
  exact hsum

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.action_finite_tendsto_on_carrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.action_finite_tendsto_on_carrier target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private theorem exists_flat_chart_approx
    (p : M) {L : ℝ} (hL : 0 ≤ L) (uLim : timeH1 E L)
    (htar : ∀ r : _root_.Set.Icc (0 : ℝ) L, uLim.toFun r.1 ∈ (extChartAt I p).target) :
    ∃ K : Set E, ∃ w : ℕ → timeH1 E L, ∃ v : ℕ → ℝ → E,
      IsCompact K ∧ K ⊆ (extChartAt I p).target ∧
      (∀ r : _root_.Set.Icc (0 : ℝ) L, uLim.toFun r.1 ∈ K) ∧
      (∀ n, ContDiff ℝ 1 (v n)) ∧
      (∀ n, _root_.Set.EqOn (w n).toFun (v n) (_root_.Set.Icc (0 : ℝ) L)) ∧
      (∀ n, v n 0 = uLim.toFun 0) ∧ (∀ n, v n L = uLim.toFun L) ∧
      (∀ n, v n =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ v n 0) ∧
      (∀ n, v n =ᶠ[𝓝 L] fun _ ↦ v n L) ∧
      (∀ n (r : _root_.Set.Icc (0 : ℝ) L), v n r.1 ∈ K) ∧
      _root_.Filter.Tendsto w _root_.Filter.atTop (𝓝 uLim) ∧
      TendstoUniformly (fun n (r : _root_.Set.Icc (0 : ℝ) L) ↦ v n r.1)
        (fun r ↦ uLim.toFun r.1) atTop := by
  classical
  obtain ⟨K, hKc, _hKclosed, hKint, hKtar⟩ :=
    exists_compact_closed_between
      (isCompact_Icc.image_of_continuousOn uLim.continuousOn_toFun)
      (isOpen_extChartAt_target (I := I) p)
      (by rintro _ ⟨r, hr, rfl⟩; exact htar ⟨r, hr⟩)
  have hLimInt (r : _root_.Set.Icc (0 : ℝ) L) : uLim.toFun r.1 ∈ interior K :=
    hKint ⟨r.1, r.2, rfl⟩
  have hflat : ∃ w : ℕ → timeH1 E L, ∃ v : ℕ → ℝ → E,
      (∀ n, ContDiff ℝ 1 (v n)) ∧
      (∀ n, _root_.Set.EqOn (w n).toFun (v n) (_root_.Set.Icc (0 : ℝ) L)) ∧
      (∀ n, v n 0 = uLim.toFun 0) ∧ (∀ n, v n L = uLim.toFun L) ∧
      (∀ n, v n =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ uLim.toFun 0) ∧
      (∀ n, v n =ᶠ[𝓝 L] fun _ ↦ uLim.toFun L) ∧
      Tendsto w _root_.Filter.atTop (𝓝 uLim) := by
    rcases hL.eq_or_lt with hL0 | hLpos
    · subst L
      refine ⟨fun _ ↦ uLim, fun _ _ ↦ uLim.toFun 0,
        fun _ ↦ contDiff_const, ?_, fun _ ↦ rfl, fun _ ↦ rfl,
        fun _ ↦ Eventually.of_forall fun _ ↦ rfl,
        fun _ ↦ Eventually.of_forall fun _ ↦ rfl, tendsto_const_nhds⟩
      intro n r hr
      have hr0 : r = 0 := le_antisymm hr.2 hr.1
      subst r
      rfl
    · obtain ⟨w, v, hv, hwv, hv0, hvL, hvg0, hvgL, hw, _hderiv⟩ :=
        exists_flat_dense hLpos uLim
      exact ⟨w, v, hv, hwv, hv0, hvL, hvg0, hvgL, hw⟩
  obtain ⟨w, v, hv, hwv, hv0, hvL, hvg0, hvgL, hw⟩ := hflat
  have hvlim : TendstoUniformly (fun n (r : _root_.Set.Icc (0 : ℝ) L) ↦ v n r.1)
      (fun r ↦ uLim.toFun r.1) atTop := by
    exact (tendstoUniformly_congr
      (F := fun n (r : _root_.Set.Icc (0 : ℝ) L) ↦ (w n).toFun r.1)
      (F' := fun n r ↦ v n r.1)
      (Eventually.of_forall fun n ↦ funext fun r ↦ hwv n r.2)).mp
      (DifferentialGeometry.Analysis.timeH1_tendstoUniformly w uLim hw)
  have hcompact : IsCompact (_root_.Set.range fun r : _root_.Set.Icc (0 : ℝ) L ↦ uLim.toFun r.1) :=
    isCompact_range uLim.continuousOn_toFun.domRestrict
  obtain ⟨delta, hdelta, hthick⟩ := hcompact.exists_thickening_subset_open
    isOpen_interior (by rintro _ ⟨r, rfl⟩; exact hLimInt r)
  have hev : ∀ᶠ n in _root_.Filter.atTop, ∀ r : _root_.Set.Icc (0 : ℝ) L, v n r.1 ∈ K := by
    filter_upwards [(Metric.tendstoUniformly_iff.mp hvlim) delta hdelta] with n hn
    intro r
    apply interior_subset
    apply hthick
    exact Metric.mem_thickening_iff.mpr
      ⟨uLim.toFun r.1, _root_.Set.mem_range_self r, by simpa only [dist_comm] using hn r⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨K, (fun n ↦ w (n + N)), (fun n ↦ v (n + N)), hKc, hKtar,
    (fun r ↦ interior_subset (hLimInt r)), (fun n ↦ hv (n + N)),
    (fun n ↦ hwv (n + N)), (fun n ↦ hv0 (n + N)), (fun n ↦ hvL (n + N)),
    ?_, ?_, ?_, hw.comp (_root_.Filter.tendsto_add_atTop_nat N), ?_⟩
  · exact fun n ↦ (hvg0 (n + N)).trans
      (Eventually.of_forall fun _ ↦ (hv0 (n + N)).symm)
  · exact fun n ↦ (hvgL (n + N)).trans
      (Eventually.of_forall fun _ ↦ (hvL (n + N)).symm)
  · exact fun n r ↦ hN (n + N) (Nat.le_add_left N n) r
  · intro U hU
    exact (_root_.Filter.tendsto_add_atTop_nat N).eventually (hvlim U hU)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_flat_chart_approx
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.exists_flat_chart_approx target :: scope.openDecls } }

theorem exists_lRegAction_c1_approx_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) {m : ℕ} (t : Fin (m + 1) → ℝ)
    (htmono : Monotone t) (ht0 : t 0 = a) (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : ℝ → M)
    (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrcLim : ∀ i, _root_.Set.MapsTo gamma (_root_.Set.Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrepLim : ∀ i, _root_.Set.EqOn (uLim i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (_root_.Set.Icc (0 : ℝ) (partitionIntervalLength t i)))
    (hback : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    ∃ alpha : ℕ → ℝ → M,
      (∀ n, ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 (alpha n)) ∧
      (∀ n, alpha n a = gamma a) ∧ (∀ n, alpha n b = gamma b) ∧
      _root_.Filter.Tendsto (fun n ↦ lRegularizedAction S T (alpha n) a b) _root_.Filter.atTop
        (𝓝 (lRegularizedAction S T gamma a b)) := by
  classical
  have htar (i : Fin m) (r : _root_.Set.Icc (0 : ℝ) (partitionIntervalLength t i)) :
      (uLim i).toFun r.1 ∈ (extChartAt I (p i)).target := by
    rw [hrepLim i r.2]
    apply (extChartAt I (p i)).map_source
    rw [extChartAt_source]
    apply hsrcLim i
    have hr2 : r.1 ≤ t i.succ - t i.castSucc := r.2.2
    exact ⟨by linarith [r.2.1], by linarith [hr2]⟩
  choose K u v hKc hKtar huLimK hvC1 huv hv0 hvL hvg0 hvgL hvK hu hvlim using
    fun i : Fin m ↦ exists_flat_chart_approx (p i)
      (sub_nonneg.mpr (htmono Fin.castSucc_lt_succ.le)) (uLim i) (htar i)
  obtain ⟨alpha, halpha, ha, hb, hrepV, hsrc, hunif⟩ :=
    exists_c1_of_flat a b t htmono ht0 htlast p gamma uLim hsrcLim hrepLim
      K hKc hKtar v hvC1 hvg0 hvgL hv0 hvL hvK huLimK hvlim
  have hrep (i : Fin m) (n : ℕ) : _root_.Set.EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (_root_.Set.Icc (0 : ℝ) (partitionIntervalLength t i)) :=
    (huv i n).trans (hrepV i n)
  have huK (i : Fin m) (n : ℕ) (r : _root_.Set.Icc (0 : ℝ) (partitionIntervalLength t i)) :
      (u i n).toFun r.1 ∈ K i := by
    rw [huv i n r.2]
    exact hvK i n r
  have hKchart (i : Fin m) : K i ⊆ interior (extChartAt I (p i)).target := by
    rw [(isOpen_extChartAt_target (I := I) (p i)).interior_eq]
    exact hKtar i
  exact ⟨alpha, halpha, ha, hb,
    action_finite_tendsto_on_carrier S hMet hSc T a b t htmono ht0 htlast
      p alpha gamma u uLim hsrc hrep hsrcLim hrepLim K hKc hKchart
      huK huLimK hu hunif hback⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_lRegAction_c1_approx_on_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_lRegAction_c1_approx_on_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_lRegAction_c1_approx_on_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_lRegAction_c1_approx_on_carrier

theorem exists_lRegAction_join_lt_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T b : ℝ) {c : ℝ} (hc : 0 < c) (hcb : c < b)
    (alpha beta : ℝ → M)
    (halpha : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 alpha (_root_.Set.Icc (0 : ℝ) c))
    (hbeta : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 beta (_root_.Set.Icc c b))
    (hnode : alpha c = beta c)
    (hback : ∀ s ∈ _root_.Set.Icc (0 : ℝ) b, T - s ^ 2 ∈ D.carrier)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ gamma : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 gamma ∧
      gamma 0 = alpha 0 ∧ gamma b = beta b ∧
      lRegularizedAction S T gamma 0 b <
        lRegularizedAction S T alpha 0 c + lRegularizedAction S T beta c b + epsilon := by
  obtain ⟨eta, m, t, p, u, heqHead, heqTail, htmono, ht0, htlast,
      _hnodeTime, hsrc, hrep⟩ :=
    exists_chartH1_join (I := I) 0 c b hc hcb alpha beta halpha hbeta hnode
  obtain ⟨delta, hdelta, hdelta0, hdeltab, hlimit⟩ :=
    exists_lRegAction_c1_approx_on_carrier S hMet hSc T 0 b t htmono ht0 htlast
      p eta u hsrc hrep hback
  have hInt := (action_partition_on_carrier S hMet hSc T 0 b t htmono ht0 htlast
    p eta u hsrc hrep hback).1
  have hb : 0 ≤ b := (hc.trans hcb).le
  have hIntHead : IntervalIntegrable (lRegularizedLagrangian S T eta) _root_.MeasureTheory.MeasureSpace.volume 0 c :=
    hInt.mono_set (by
      rw [_root_.Set.uIcc_of_le hc.le, _root_.Set.uIcc_of_le hb]
      exact _root_.Set.Icc_subset_Icc le_rfl hcb.le)
  have hIntTail : IntervalIntegrable (lRegularizedLagrangian S T eta) _root_.MeasureTheory.MeasureSpace.volume c b :=
    hInt.mono_set (by
      rw [_root_.Set.uIcc_of_le hcb.le, _root_.Set.uIcc_of_le hb]
      exact _root_.Set.Icc_subset_Icc hc.le le_rfl)
  have hHead : lRegularizedAction S T eta 0 c = lRegularizedAction S T alpha 0 c := by
    apply lRegularizedAction_congr
    intro s hs
    have hs' : s ∈ _root_.Set.Ioo (0 : ℝ) c := by simpa only [_root_.Set.uIoo_of_le hc.le] using hs
    exact heqHead ⟨hs'.1.le, hs'.2.le⟩
  have hTail : lRegularizedAction S T eta c b = lRegularizedAction S T beta c b := by
    apply lRegularizedAction_congr
    intro s hs
    have hs' : s ∈ _root_.Set.Ioo c b := by simpa only [_root_.Set.uIoo_of_le hcb.le] using hs
    exact heqTail ⟨hs'.1.le, hs'.2.le⟩
  have hAction : lRegularizedAction S T eta 0 b =
      lRegularizedAction S T alpha 0 c + lRegularizedAction S T beta c b := by
    rw [← lRegularizedAction_add S T eta 0 c b hIntHead hIntTail, hHead, hTail]
  have hevent : ∀ᶠ n in _root_.Filter.atTop,
      lRegularizedAction S T (delta n) 0 b < lRegularizedAction S T eta 0 b + epsilon :=
    hlimit.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hepsilon))
  obtain ⟨n, hn⟩ := hevent.exists
  refine ⟨delta n, hdelta n, ?_, ?_, ?_⟩
  · exact (hdelta0 n).trans (heqHead ⟨le_rfl, hc.le⟩)
  · exact (hdeltab n).trans (heqTail ⟨hcb.le, le_rfl⟩)
  · simpa only [hAction] using hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_lRegAction_join_lt_on_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_lRegAction_join_lt_on_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_lRegAction_join_lt_on_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_lRegAction_join_lt_on_carrier

end DifferentialGeometry.PDE.RicciFlow

end
