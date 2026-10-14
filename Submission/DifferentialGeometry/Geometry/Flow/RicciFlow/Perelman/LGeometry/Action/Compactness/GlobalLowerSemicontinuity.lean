import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.WeakH1
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Compactness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.LowerSemicontinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology _root_.Submission.Topology _root_.Interval

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] in
theorem lAction_chart_lsc
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t0 t1 : Real) (gRef : SmoothRiemannianMetric I M)
    (a b A : Real) (hab : a ≤ b)
    (htime : _root_.Set.Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ _root_.Set.Icc t0 t1)
    (alpha : Nat → Real → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (_root_.Set.Icc a b))
    (hE : ∀ n, _root_.MeasureTheory.IntegrableOn
      (fun s ↦ gRef.inner (alpha n s) (lVelocity (I := I) (alpha n) s)
        (lVelocity (I := I) (alpha n) s)) (_root_.Set.Icc a b))
    (hLag : ∀ n, IntervalIntegrable (lRegularizedLagrangian S T (alpha n)) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hact : ∀ n, lRegularizedAction S T (alpha n) a b ≤ A)
    (x y : M) (hfixa : ∀ n, alpha n a = x)
    (hfixb : ∀ n, alpha n b = y)
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.regular) :
    ∃ (m : Nat) (t : Fin (m + 1) → Real) (p : Fin m → M)
      (chi : Nat → Nat) (gamma : Real → M)
      (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      StrictMono chi ∧ Continuous gamma ∧ gamma a = x ∧ gamma b = y ∧
      TendstoUniformly
        (fun n (s : _root_.Set.Icc a b) ↦ alpha (chi n) s.1)
        (fun s ↦ gamma s.1) _root_.Filter.atTop ∧
      Monotone t ∧ t 0 = a ∧ t (Fin.last m) = b ∧
      (∀ i, _root_.Set.MapsTo gamma (_root_.Set.Icc (t i.castSucc) (t i.succ))
        (chartAt H (p i)).source) ∧
      (∀ i, _root_.Set.EqOn (uLim i).toFun
        (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
        (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i))) ∧
      (∑ i : Fin m, (
        (∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * _root_.Inner.inner Real
          (chartGramOp (I := I) S.family (p i)
            (T - (t i.castSucc + r) ^ 2, (uLim i).toFun r)
            ((uLim i).deriv r)) ((uLim i).deriv r)) +
        (∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s)))) ≤
        liminf (fun n ↦ lRegularizedAction S T (alpha (chi n)) a b) atTop := by
  have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
    hS.smoothMetric
  have hSc : ScalarSTContOn (I := I) (M := M) S :=
    ⟨hS.scalarCont⟩
  obtain ⟨phi0, g, hphi0, hconv0, hga, hgb⟩ :=
    lAction_subseq_fix (I := I) S hS T t0 t1 gRef a b A hab htime hback
      alpha halpha hE hLag hact x y hfixa hfixb
  let gamma : Real → M := Set.IccExtend hab g
  have hgamma : Continuous gamma := by
    dsimp only [gamma, Set.IccExtend, Function.comp_apply]
    exact g.continuous.comp continuous_projIcc
  have hgamma_eq (s : _root_.Set.Icc a b) : gamma s.1 = g s := by
    exact Set.IccExtend_of_mem hab g s.2
  have hga' : gamma a = x := by
    rw [hgamma_eq ⟨a, le_rfl, hab⟩]
    exact hga
  have hgb' : gamma b = y := by
    rw [hgamma_eq ⟨b, hab, le_rfl⟩]
    exact hgb
  have hconvG : TendstoUniformly
      (fun n (s : _root_.Set.Icc a b) ↦ alpha (phi0 n) s.1)
      (fun s ↦ gamma s.1) atTop := by
    convert hconv0 using 1
    funext s
    exact hgamma_eq s
  obtain ⟨q, hq0, hqmono, ⟨m, hqm⟩, hpieces⟩ :=
    DifferentialGeometry.Geometry.exists_compact_chart_subdivision (H := H) hab
      hgamma.continuousOn
  let t : Fin (m + 1) → Real := fun i ↦ (q i).1
  have htmono : Monotone t := fun i j hij ↦
    hqmono hij
  have ht0 : t 0 = a := by
    exact congrArg Subtype.val hq0
  have htlast : t (Fin.last m) = b := by
    exact congrArg Subtype.val (hqm m le_rfl)
  choose p Kman hKc hKsrc hgammaK using fun i : Fin m ↦ hpieces i
  obtain ⟨N, K, u, hKc', hKchart, hsrc, hrep, huK⟩ :=
    exists_chartH1_coordinates_with_compact_range_of_tendstoUniformly (I := I) a b t htmono ht0 htlast p Kman hKc hKsrc
      gamma hgamma.continuousOn (fun i ↦ hgammaK i)
      (fun n ↦ alpha (phi0 n)) (fun n ↦ halpha (phi0 n)) hconvG
  let beta : Nat → Real → M := fun n ↦ alpha (phi0 (n + N))
  have hLagBeta : ∀ n, IntervalIntegrable (lRegularizedLagrangian S T (beta n)) _root_.MeasureTheory.MeasureSpace.volume a b :=
    fun n ↦ hLag _
  have hactBeta : ∀ n, lRegularizedAction S T (beta n) a b ≤ A :=
    fun n ↦ hact _
  obtain ⟨psi, uLim, hpsi, hdu, hu⟩ :=
    exists_chartH1_weakly_convergent_subsequence_of_lRegularizedAction_le S hMet hSc T a b t htmono ht0 htlast p beta hLagBeta
      u (fun i n ↦ by simpa only [beta, Nat.add_comm] using hsrc i n)
      (fun i n ↦ by simpa only [beta, Nat.add_comm] using hrep i n)
      K hKc' hKchart (fun i n r ↦ by
        simpa only [beta, Nat.add_comm] using huK i n r)
      hactBeta hreg
  let chi : Nat → Nat := fun n ↦ phi0 (psi n + N)
  have hpsiN : StrictMono (fun n ↦ psi n + N) := fun i j hij ↦
    by simpa only [Nat.add_comm] using add_lt_add_right (hpsi hij) N
  have hchi : StrictMono chi := hphi0.comp hpsiN
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
      (u i (psi n)).toFun r.1 ∈ K i := by
    simpa only [beta, Nat.add_comm] using huK i (psi n) r
  have hgammaSource (i : Fin m) : _root_.Set.MapsTo gamma
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source :=
    (hgammaK i).mono_right (interior_subset.trans (hKsrc i))
  have hlimRep (i : Fin m) : _root_.Set.EqOn (uLim i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)) := by
    intro r hr
    have hseg : t i.castSucc ≤ t i.succ :=
      htmono Fin.castSucc_lt_succ.le
    have hpoint : _root_.Filter.Tendsto (fun n ↦ alpha (chi n) (t i.castSucc + r)) _root_.Filter.atTop
        (nhds (gamma (t i.castSucc + r))) := by
      have hsub : t i.castSucc + r ∈ _root_.Set.Icc a b := by
        have hleft : a ≤ t i.castSucc := by
          rw [← ht0]
          exact htmono (Fin.zero_le _)
        have hright : t i.succ ≤ b := by
          rw [← htlast]
          exact htmono (Fin.le_last _)
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
        (nhds (extChartAt I (p i) (gamma (t i.castSucc + r)))) := by
      apply (continuousAt_extChartAt' (I := I) hExtSource).tendsto.comp hpoint
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
  have hlsc := lRegularizedAction_fin_lsc S hMet hSc T a b t htmono ht0 htlast p
    (fun n ↦ alpha (chi n)) gamma (fun i n ↦ u i (psi n))
    hsrc' hrep' K hKc' hKchart huK' uLim
    (fun i ↦ by
      intro V hV
      exact (hu i V hV))
    (fun i z ↦ by simpa only using hdu i z)
    hconv hactBound hreg
  exact ⟨m, t, p, chi, gamma, uLim, hchi, hgamma, hga', hgb', hconv,
    htmono, ht0, htlast, hgammaSource, hlimRep, hlsc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lAction_chart_lsc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lAction_chart_lsc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lAction_chart_lsc ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lAction_chart_lsc

omit [NeZero (Module.finrank Real E)] in
theorem lAction_liminf
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t0 t1 : Real) (gRef : SmoothRiemannianMetric I M)
    (a b A : Real) (hab : a ≤ b)
    (htime : _root_.Set.Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ _root_.Set.Icc t0 t1)
    (alpha : Nat → Real → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (_root_.Set.Icc a b))
    (hE : ∀ n, _root_.MeasureTheory.IntegrableOn
      (fun s ↦ gRef.inner (alpha n s) (lVelocity (I := I) (alpha n) s)
        (lVelocity (I := I) (alpha n) s)) (_root_.Set.Icc a b))
    (hLag : ∀ n, IntervalIntegrable (lRegularizedLagrangian S T (alpha n)) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hact : ∀ n, lRegularizedAction S T (alpha n) a b ≤ A)
    (x y : M) (hfixa : ∀ n, alpha n a = x)
    (hfixb : ∀ n, alpha n b = y)
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.regular) :
    ∃ (chi : Nat → Nat) (gamma : Real → M),
      StrictMono chi ∧ Continuous gamma ∧ gamma a = x ∧ gamma b = y ∧
      TendstoUniformly
        (fun n (s : _root_.Set.Icc a b) ↦ alpha (chi n) s.1)
        (fun s ↦ gamma s.1) _root_.Filter.atTop ∧
      lRegularizedAction S T gamma a b ≤
        liminf (fun n ↦ lRegularizedAction S T (alpha (chi n)) a b) atTop := by
  obtain ⟨m, t, p, chi, gamma, uLim, hchi, hgamma, hga, hgb, hconv,
      htmono, ht0, htlast, hsrc, hrep, hchart⟩ :=
    lAction_chart_lsc (I := I) S hS T t0 t1 gRef a b A hab htime hback
      alpha halpha hE hLag hact x y hfixa hfixb hreg
  have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
    hS.smoothMetric
  have hSc : ScalarSTContOn (I := I) (M := M) S :=
    ⟨hS.scalarCont⟩
  refine ⟨chi, gamma, hchi, hgamma, hga, hgb, hconv, ?_⟩
  rw [lRegularizedAction_chart S hMet hSc T a b t htmono ht0 htlast p gamma uLim
    hsrc hrep hreg]
  exact hchart

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lAction_liminf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lAction_liminf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lAction_liminf ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lAction_liminf

end DifferentialGeometry.PDE.RicciFlow.Perelman
