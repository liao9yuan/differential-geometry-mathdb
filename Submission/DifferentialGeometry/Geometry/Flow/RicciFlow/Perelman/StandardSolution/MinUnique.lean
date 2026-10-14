import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinPrefix
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.C1Regularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.TwoPieceSplicing
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.EndpointVariation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Uniqueness
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Curve.Partition
import Mathlib.Topology.Piecewise
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow

private theorem exists_continuous_interval_join
    {X : Type*} [TopologicalSpace X] {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (alpha beta : ℝ → X)
    (halpha : ContinuousOn alpha (_root_.Set.Icc a c))
    (hbeta : ContinuousOn beta (_root_.Set.Icc c b))
    (hnode : alpha c = beta c) :
    ∃ gamma : ℝ → X, Continuous gamma ∧
      EqOn gamma alpha (_root_.Set.Icc a c) ∧ _root_.Set.EqOn gamma beta (_root_.Set.Icc c b) := by
  classical
  let raw : ℝ → X := (_root_.Set.Iic c).piecewise alpha beta
  have hab : a ≤ b := (hac.trans hcb).le
  have hraw : ContinuousOn raw (_root_.Set.Icc a b) := by
    apply ContinuousOn.piecewise
    · intro s hs
      have hsc : s = c := by simpa only [frontier_Iic, _root_.Set.mem_singleton_iff] using hs.2
      simpa only [hsc] using hnode
    · apply halpha.mono
      intro s hs
      exact ⟨hs.1.1, by simpa only [isClosed_Iic.closure_eq, _root_.Set.mem_Iic] using hs.2⟩
    · apply hbeta.mono
      intro s hs
      exact ⟨by simpa only [_root_.Set.compl_Iic, closure_Ioi, _root_.Set.mem_Ici] using hs.2, hs.1.2⟩
  let gamma : ℝ → X := fun s ↦ raw (_root_.Set.projIcc a b hab s)
  have hgamma : Continuous gamma :=
    hraw.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun s ↦ (_root_.Set.projIcc a b hab s).property)
  have hsame (s : ℝ) (hs : s ∈ _root_.Set.Icc a b) : gamma s = raw s := by
    simp only [gamma, _root_.Set.projIcc_of_mem hab hs]
  refine ⟨gamma, hgamma, ?_, ?_⟩
  · intro s hs
    rw [hsame s ⟨hs.1, hs.2.trans hcb.le⟩]
    exact (_root_.Set.Iic c).piecewise_eq_of_mem alpha beta hs.2
  · intro s hs
    rw [hsame s ⟨hac.le.trans hs.1, hs.2⟩]
    rcases eq_or_lt_of_le hs.1 with hsc | hsc
    · subst s
      exact ((_root_.Set.Iic c).piecewise_eq_of_mem alpha beta (le_rfl : c ≤ c)).trans hnode
    · exact (_root_.Set.Iic c).piecewise_eq_of_notMem alpha beta (not_le.mpr hsc)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_continuous_interval_join
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.exists_continuous_interval_join target :: scope.openDecls } }

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem velocity_eq_of_interval_agreement
    {alpha beta : ℝ → M} {a b s : ℝ} (hab : a < b)
    (hs : s ∈ _root_.Set.Icc a b)
    (halpha : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha s)
    (hbeta : MDifferentiableAt 𝓘(ℝ, ℝ) I beta s)
    (heq : _root_.Set.EqOn alpha beta (_root_.Set.Icc a b)) :
    lVelocity (I := I) alpha s = lVelocity (I := I) beta s := by
  have hder := mfderivWithin_congr_of_mem
    (I := 𝓘(ℝ, ℝ)) (I' := I) heq hs
  have huniq := ((uniqueDiffOn_Icc hab) s hs).uniqueMDiffWithinAt
  rw [mfderivWithin_eq_mfderiv huniq halpha,
    mfderivWithin_eq_mfderiv huniq hbeta] at hder
  unfold lVelocity
  rw [hder]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.velocity_eq_of_interval_agreement
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.velocity_eq_of_interval_agreement target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private theorem min_ray_action_eq_cost
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    {Z : TangentSpace I x} {tau : ℝ} (htau : 0 < tau)
    (hmin : (Z, tau) ∈ lMinDomain S T x) :
    lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) =
      lCost S T x (lExp S T x Z tau) tau := by
  calc
    lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) =
        lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 tau :=
      (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T (lRegularizedCurve S T x Z) tau htau.le).symm
    _ = lCost S T x (lExp S T x Z tau) tau :=
      ((mem_lMinDomain S T x Z tau).mp hmin).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.min_ray_action_eq_cost
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.min_ray_action_eq_cost target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem lMinVec_unique_lt_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    {Z W : TangentSpace I x} {sigma tau : ℝ}
    (hZ : (Z, tau) ∈ lMinDomain S T x)
    (hlt : sigma < tau)
    (hW : (W, sigma) ∈ lMinDomain S T x)
    (hend : lExp S T x W sigma = lExp S T x Z sigma)
    (hbddTau : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = x ∧
        alpha (Real.sqrt tau) = lExp S T x Z tau ∧
        lRegularizedAction S T alpha 0 (Real.sqrt tau) = r}) :
    W = Z := by
  by_cases hzero : Module.finrank ℝ E = 0
  · let _ : Subsingleton E := Module.finrank_zero_iff.mp hzero
    exact @Subsingleton.elim E inferInstance W Z
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hzero⟩
    classical
    have hsigma : 0 < sigma := lMinDomain_pos S T x W sigma hW
    have hbddSigma := lRegularizedCosts_prefix_bdd_of_min S hS T x Z hZ hsigma hlt.le hbddTau
    have htau : 0 < tau := hsigma.trans hlt
    have hZsmall : (Z, sigma) ∈ lMinDomain S T x :=
      lMinDomain_down_of_bdd S hS T x Z hZ hsigma hlt.le hbddSigma hbddTau
    have hZpos := ((mem_lMinDomain S T x Z tau).mp hZ).1
    have hZsmallPos := ((mem_lMinDomain S T x Z sigma).mp hZsmall).1
    have hWpos := ((mem_lMinDomain S T x W sigma).mp hW).1
    let b : ℝ := Real.sqrt tau
    let c : ℝ := Real.sqrt sigma
    let alpha : ℝ → M := lRegularizedCurve S T x W
    let beta : ℝ → M := lRegularizedCurve S T x Z
    have hc : 0 < c := Real.sqrt_pos.mpr hsigma
    have hcb : c < b := Real.sqrt_lt_sqrt hsigma.le hlt
    have hb : 0 < b := hc.trans hcb
    have hbZ : b ∈ lRegularizedDomain S T x Z :=
      ((mem_lExpPosDom S T x Z tau).mp hZpos).2.2
    have hcZ : c ∈ lRegularizedDomain S T x Z :=
      ((mem_lExpPosDom S T x Z sigma).mp hZsmallPos).2.2
    have hcW : c ∈ lRegularizedDomain S T x W :=
      ((mem_lExpPosDom S T x W sigma).mp hWpos).2.2
    have hclock (s : ℝ) (hs : s ∈ _root_.Set.Icc (0 : ℝ) b) :
        T - s ^ 2 ∈ D.regular :=
      lExpPosDom_regularity S T x Z hZpos hs
    have hcosts : BddBelow {r : ℝ | ∃ delta : ℝ → M,
        ContMDiff 𝓘(ℝ, ℝ) I 1 delta ∧ delta 0 = x ∧
          delta b = beta b ∧ lRegularizedAction S T delta 0 b = r} :=
      hbddTau
    have halpha : ContMDiffOn 𝓘(ℝ, ℝ) I 1 alpha (_root_.Set.Icc (0 : ℝ) c) :=
      lRegularizedCurve_c1On S hS T x W hcW
    have hbeta : ContMDiffOn 𝓘(ℝ, ℝ) I 1 beta (_root_.Set.Icc (0 : ℝ) b) :=
      lRegularizedCurve_c1On S hS T x Z hbZ
    have hleft : _root_.Set.Icc (0 : ℝ) c ⊆ _root_.Set.Icc (0 : ℝ) b :=
      fun _ hs ↦ ⟨hs.1, hs.2.trans hcb.le⟩
    have hright : _root_.Set.Icc c b ⊆ _root_.Set.Icc (0 : ℝ) b :=
      fun _ hs ↦ ⟨hc.le.trans hs.1, hs.2⟩
    have hbetaTail : ContMDiffOn 𝓘(ℝ, ℝ) I 1 beta (_root_.Set.Icc c b) :=
      hbeta.mono hright
    have hnode : alpha c = beta c := hend
    obtain ⟨gamma, hgamma, hgammaLeft, hgammaRight⟩ :=
      exists_continuous_interval_join hc hcb alpha beta
        halpha.continuousOn hbetaTail.continuousOn hnode
    have hgammaLeftC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc (0 : ℝ) c) :=
      halpha.congr hgammaLeft
    have hgammaRightC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc c b) :=
      hbetaTail.congr hgammaRight
    have hint {a d : ℝ} {eta : ℝ → M} (had : a ≤ d)
        (heta : ContMDiffOn 𝓘(ℝ, ℝ) I 1 eta (_root_.Set.Icc a d))
        (hsub : _root_.Set.Icc a d ⊆ _root_.Set.Icc (0 : ℝ) b) :
        IntervalIntegrable (lRegularizedLagrangian S T eta) _root_.MeasureTheory.MeasureSpace.volume a d :=
      intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one S hS.smoothMetric ⟨hS.scalarCont⟩
        T a d had eta heta (fun s hs ↦ hclock s (hsub hs))
    have hgammaActLeft :
        lRegularizedAction S T gamma 0 c = lRegularizedAction S T alpha 0 c := by
      apply lRegularizedAction_congr
      intro s hs
      have hs' : s ∈ _root_.Set.Ioo (0 : ℝ) c := by
        simpa only [_root_.Set.uIoo_of_le hc.le] using hs
      exact hgammaLeft ⟨hs'.1.le, hs'.2.le⟩
    have hgammaActRight :
        lRegularizedAction S T gamma c b = lRegularizedAction S T beta c b := by
      apply lRegularizedAction_congr
      intro s hs
      have hs' : s ∈ _root_.Set.Ioo c b := by
        simpa only [_root_.Set.uIoo_of_le hcb.le] using hs
      exact hgammaRight ⟨hs'.1.le, hs'.2.le⟩
    have hprefix : lRegularizedAction S T alpha 0 c = lRegularizedAction S T beta 0 c := by
      calc
        lRegularizedAction S T alpha 0 c = lCost S T x (lExp S T x W sigma) sigma :=
          min_ray_action_eq_cost S T x hsigma hW
        _ = lCost S T x (lExp S T x Z sigma) sigma := by rw [hend]
        _ = lRegularizedAction S T beta 0 c :=
          (min_ray_action_eq_cost S T x hsigma hZsmall).symm
    have haction : lRegularizedAction S T gamma 0 b = lRegularizedAction S T beta 0 b := by
      rw [← lRegularizedAction_add S T gamma 0 c b
        (hint hc.le hgammaLeftC1 hleft) (hint hcb.le hgammaRightC1 hright),
        hgammaActLeft, hgammaActRight, hprefix]
      exact lRegularizedAction_add S T beta 0 c b
        (hint hc.le (hbeta.mono hleft) hleft) (hint hcb.le hbetaTail hright)
    have hbetaCost : lRegularizedAction S T beta 0 b =
        lRegularizedCostC1 S T 0 b x (beta b) := by
      calc
        lRegularizedAction S T beta 0 b = lCost S T x (lExp S T x Z tau) tau :=
          min_ray_action_eq_cost S T x htau hZ
        _ = lRegularizedCostC1 S T 0 b x (beta b) :=
          lCost_eq_regularity (I := I) S T x (lExp S T x Z tau) tau htau.le
    have hmin : ∀ delta : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
        delta 0 = gamma 0 → delta b = gamma b →
        lRegularizedAction S T gamma 0 b ≤ lRegularizedAction S T delta 0 b := by
      intro delta hdelta hd0 hdb
      rw [haction, hbetaCost]
      apply lRegularizedCostC1_le_bdd S T 0 b x (beta b) hcosts delta hdelta
      · exact hd0.trans ((hgammaLeft ⟨le_rfl, hc.le⟩).trans
          (lRegularizedCurve_zero S T x W))
      · exact hdb.trans (hgammaRight ⟨hcb.le, le_rfl⟩)
    obtain ⟨eta, m, t, p, v, hetaLeft, hetaRight, htmono, ht0, htb,
        _hnodeIndex, hsrc, hrep⟩ :=
      exists_chartH1_join (I := I) 0 c b hc hcb gamma gamma
        hgammaLeftC1 hgammaRightC1 rfl
    have heta : _root_.Set.EqOn eta gamma (_root_.Set.Icc (0 : ℝ) b) := by
      intro s hs
      rcases le_total s c with hsc | hcs
      · exact hetaLeft ⟨hs.1, hsc⟩
      · exact hetaRight ⟨hcs, hs.2⟩
    have htmem (i : Fin (m + 1)) : t i ∈ _root_.Set.Icc (0 : ℝ) b :=
      ⟨by simpa only [ht0] using htmono (Fin.zero_le i),
        by simpa only [htb] using htmono (Fin.le_last i)⟩
    have hseg (i : Fin m) {s : ℝ}
        (hs : s ∈ _root_.Set.Icc (t i.castSucc) (t i.succ)) :
        s ∈ _root_.Set.Icc (0 : ℝ) b :=
      ⟨(htmem i.castSucc).1.trans hs.1, hs.2.trans (htmem i.succ).2⟩
    have hsrcGamma : ∀ i, _root_.Set.MapsTo gamma (_root_.Set.Icc (t i.castSucc) (t i.succ))
        (chartAt H (p i)).source := by
      intro i s hs
      rw [← heta (hseg i hs)]
      exact hsrc i hs
    have hrepGamma : ∀ i, _root_.Set.EqOn (v i).toFun
        (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
        (_root_.Set.Icc (0 : ℝ) (partitionIntervalLength t i)) := by
      intro i r hr
      have hshift : t i.castSucc + r ∈ _root_.Set.Icc (0 : ℝ) b := by
        apply hseg i
        simp only [partitionIntervalLength] at hr
        constructor <;> linarith [hr.1, hr.2]
      exact (hrep i hr).trans (congrArg (extChartAt I (p i)) (heta hshift))
    have hgammaC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc (0 : ℝ) b) :=
      lMinCurve_c1 S hS T 0 b hb t htmono ht0 htb p gamma hgamma v
        hsrcGamma hrepGamma hclock hmin
    have hgammaDiff : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma c :=
      (hgammaC1.contMDiffAt (Icc_mem_nhds hc hcb)).mdifferentiableAt (by norm_num)
    have hcSelf : c ∈ _root_.Set.uIcc (0 : ℝ) c := by
      simpa only [_root_.Set.uIcc_of_le hc.le] using
        (show c ∈ _root_.Set.Icc (0 : ℝ) c from ⟨hc.le, le_rfl⟩)
    have halphaDiff : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha c :=
      ((lRegularizedCurve_isLRegularizedCurveOn S hS T x W hc hcW).2.2 c hcSelf).2.1
    have hbetaDiff : MDifferentiableAt 𝓘(ℝ, ℝ) I beta c :=
      ((lRegularizedCurve_isLRegularizedCurveOn S hS T x Z hc hcZ).2.2 c hcSelf).2.1
    have hvelLeft : lVelocity (I := I) alpha c = lVelocity (I := I) gamma c :=
      velocity_eq_of_interval_agreement hc ⟨hc.le, le_rfl⟩
        halphaDiff hgammaDiff (fun s hs ↦ (hgammaLeft hs).symm)
    have hvelRight : lVelocity (I := I) gamma c = lVelocity (I := I) beta c :=
      velocity_eq_of_interval_agreement hcb ⟨le_rfl, hcb.le⟩
        hgammaDiff hbetaDiff hgammaRight
    exact lRegularizedCurve_initialVector_eq_of_endpoint_eq_of_velocity_eq S hS T x hcW hcZ hnode (hvelLeft.trans hvelRight)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lMinVec_unique_lt_of_bdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lMinVec_unique_lt_of_bdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lMinVec_unique_lt_of_bdd ``Submission.DifferentialGeometry.PDE.RicciFlow.lMinVec_unique_lt_of_bdd

theorem lMinVec_unique_lt_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z W : TangentSpace I x} {sigma tau : ℝ}
    (hZ : (Z, tau) ∈ lMinDomain S T x)
    (hsigma : 0 < sigma) (hlt : sigma < tau)
    (hW : (W, sigma) ∈ lMinDomain S T x)
    (hend : lExp S T x W sigma = lExp S T x Z sigma)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - tau) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K) :
    W = Z := by
  let _ : NeZero (Module.finrank ℝ E) := inferInstance
  have htau : 0 < tau := hsigma.trans hlt
  have hZpos := ((mem_lMinDomain S T x Z tau).mp hZ).1
  have hreg : _root_.Set.Icc (T - tau) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ tau := by linarith only [ht.1]
    have h := lExpPosDom_regularity S T x Z hZpos
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
    have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using h
  apply lMinVec_unique_lt_of_bdd S hS T x hZ hlt hW hend
  exact lRegularizedCosts_bdd_rm S hS K T 0 (Real.sqrt tau)
    le_rfl (Real.sqrt_nonneg tau)
    (by simpa only [Real.sq_sqrt htau.le] using hreg)
    (by simpa only [Real.sq_sqrt htau.le] using hRm) x (lExp S T x Z tau)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lMinVec_unique_lt_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lMinVec_unique_lt_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lMinVec_unique_lt_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lMinVec_unique_lt_of_rm

end DifferentialGeometry.PDE.RicciFlow

end
