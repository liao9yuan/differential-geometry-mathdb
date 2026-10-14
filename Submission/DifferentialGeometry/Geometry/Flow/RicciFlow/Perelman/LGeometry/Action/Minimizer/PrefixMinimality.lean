import Submission.DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.TwoPieceSplicing
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Integrability
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.RegularizedC1Attainment

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Filter _root_.Function _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {D : RealTimeInterval}

section Prefix

variable {M : Type u} [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M]

omit [CompactSpace M] in
theorem lRegularized_prefix_min
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a c b : Real) (hac : a < c) (hcb : c < b)
    (gamma : Real → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (_root_.Set.Icc a b))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T delta a b) :
    ∀ delta : Real → M,
      ContMDiffOn (modelWithCornersSelf Real Real) I 1 delta (_root_.Set.Icc a c) →
      delta a = gamma a → delta c = gamma c →
      lRegularizedAction S T gamma a c ≤ lRegularizedAction S T delta a c := by
  intro delta hdelta hda hdc
  have hgammaTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (_root_.Set.Icc c b) := hgamma.mono (by
    intro s hs
    exact ⟨hac.le.trans hs.1, hs.2⟩)
  obtain ⟨eta, m, t, p, u, hetaDelta, hetaGamma, htmono, ht0, htlast,
      _hc, hsrc, hrep⟩ :=
    exists_chartH1_join (I := I) a c b hac hcb delta gamma
      hdelta hgammaTail hdc
  obtain ⟨alpha, _w, halpha, halphaa, halphab, _hsrcAlpha, _hrepAlpha,
      _hw, _huniform, haction⟩ :=
    lAction_c1_dense (I := I) S hMet hSc T a b t htmono ht0 htlast p eta u
      hsrc hrep hreg
  have hetaA : eta a = gamma a :=
    (hetaDelta ⟨le_rfl, hac.le⟩).trans hda
  have hetaB : eta b = gamma b := hetaGamma ⟨hcb.le, le_rfl⟩
  have hwhole : lRegularizedAction S T gamma a b ≤ lRegularizedAction S T eta a b := by
    apply ge_of_tendsto haction
    exact Eventually.of_forall fun n ↦
      hmin (alpha n) (halpha n) ((halphaa n).trans hetaA)
        ((halphab n).trans hetaB)
  have hregAC : ∀ s ∈ _root_.Set.Icc a c, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hs.1, hs.2.trans hcb.le⟩
  have hregCB : ∀ s ∈ _root_.Set.Icc c b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hac.le.trans hs.1, hs.2⟩
  have hgammaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (_root_.Set.Icc a c) := hgamma.mono (by
    intro s hs
    exact ⟨hs.1, hs.2.trans hcb.le⟩)
  have hetaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
      (_root_.Set.Icc a c) := hdelta.congr fun s hs ↦ hetaDelta hs
  have hetaTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
      (_root_.Set.Icc c b) := hgammaTail.congr fun s hs ↦ hetaGamma hs
  have hgammaIntAC :=
    intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hMet hSc T a c hac.le gamma hgammaHead hregAC
  have hgammaIntCB :=
    intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hMet hSc T c b hcb.le gamma hgammaTail hregCB
  have hetaIntAC :=
    intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hMet hSc T a c hac.le eta hetaHead hregAC
  have hetaIntCB :=
    intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hMet hSc T c b hcb.le eta hetaTail hregCB
  have hgammaAdd :=
    lRegularizedAction_add (I := I) S T gamma a c b hgammaIntAC hgammaIntCB
  have hetaAdd := lRegularizedAction_add (I := I) S T eta a c b hetaIntAC hetaIntCB
  have hetaAC : lRegularizedAction S T eta a c = lRegularizedAction S T delta a c := by
    apply lRegularizedAction_congr (I := I) S T
    intro s hs
    have hs' : s ∈ _root_.Set.Ioo a c := by
      simpa only [_root_.Set.uIoo_of_le hac.le] using hs
    exact hetaDelta ⟨hs'.1.le, hs'.2.le⟩
  have hetaCB : lRegularizedAction S T eta c b = lRegularizedAction S T gamma c b := by
    apply lRegularizedAction_congr (I := I) S T
    intro s hs
    have hs' : s ∈ _root_.Set.Ioo c b := by
      simpa only [_root_.Set.uIoo_of_le hcb.le] using hs
    exact hetaGamma ⟨hs'.1.le, hs'.2.le⟩
  rw [← hgammaAdd, ← hetaAdd, hetaAC, hetaCB] at hwhole
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularized_prefix_min then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularized_prefix_min"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularized_prefix_min ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularized_prefix_min

end Prefix

section Compact

variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

theorem lRegularizedCostC1_eq_on
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t0 t1 a b : Real) (hab : a < b)
    (htime : _root_.Set.Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ _root_.Set.Icc t0 t1)
    (x y : M) (gamma : Real → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (_root_.Set.Icc a b))
    (hga : gamma a = x) (hgb : gamma b = y)
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = x → delta b = y →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T delta a b) :
    lRegularizedAction S T gamma a b = lRegularizedCostC1 S T a b x y := by
  let c : Real := (a + b) / 2
  have hac : a < c := by
    simp only [c]
    linarith
  have hcb : c < b := by
    simp only [c]
    linarith
  have hgammaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (_root_.Set.Icc a c) := hgamma.mono (by
    intro s hs
    exact ⟨hs.1, hs.2.trans hcb.le⟩)
  have hgammaTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (_root_.Set.Icc c b) := hgamma.mono (by
    intro s hs
    exact ⟨hac.le.trans hs.1, hs.2⟩)
  obtain ⟨eta, m, t, p, u, hetaHead, hetaTail, htmono, ht0, htlast,
      _hc, hsrc, hrep⟩ :=
    exists_chartH1_join (I := I) a c b hac hcb gamma gamma
      hgammaHead hgammaTail rfl
  have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
    hS.smoothMetric
  have hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  obtain ⟨alpha, _w, halpha, halphaa, halphab, _hsrcAlpha, _hrepAlpha,
      _hw, _huniform, haction⟩ :=
    lAction_c1_dense (I := I) S hMet hSc T a b t htmono ht0 htlast p eta u
      hsrc hrep hreg
  have hetaA : eta a = x := (hetaHead ⟨le_rfl, hac.le⟩).trans hga
  have hetaB : eta b = y := (hetaTail ⟨hcb.le, le_rfl⟩).trans hgb
  have hetaEq : lRegularizedAction S T eta a b = lRegularizedAction S T gamma a b := by
    apply lRegularizedAction_congr (I := I) S T
    intro s hs
    have hs' : s ∈ _root_.Set.Ioo a b := by
      simpa only [_root_.Set.uIoo_of_le hab.le] using hs
    by_cases hsc : s ≤ c
    · exact hetaHead ⟨hs'.1.le, hsc⟩
    · exact hetaTail ⟨(lt_of_not_ge hsc).le, hs'.2.le⟩
  have hcostGamma : lRegularizedCostC1 S T a b x y ≤ lRegularizedAction S T gamma a b := by
    rw [← hetaEq]
    apply ge_of_tendsto haction
    exact Eventually.of_forall fun n ↦
      lRegularizedCostC1_le (I := I) S hS T t0 t1 a b hab.le htime hback x y
        (alpha n) (halpha n) ((halphaa n).trans hetaA)
        ((halphab n).trans hetaB) hreg
  have hcosts : {r : Real | ∃ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta ∧
        delta a = x ∧ delta b = y ∧ lRegularizedAction S T delta a b = r}.Nonempty := by
    refine ⟨lRegularizedAction S T (alpha 0) a b, alpha 0, halpha 0,
      (halphaa 0).trans hetaA, (halphab 0).trans hetaB, rfl⟩
  have hgammaCost : lRegularizedAction S T gamma a b ≤ lRegularizedCostC1 S T a b x y := by
    change lRegularizedAction S T gamma a b ≤ _root_.InfSet.sInf {r : Real | ∃ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta ∧
        delta a = x ∧ delta b = y ∧ lRegularizedAction S T delta a b = r}
    apply le_csInf hcosts
    intro r hr
    obtain ⟨delta, hdelta, hda, hdb, rfl⟩ := hr
    exact hmin delta hdelta hda hdb
  exact le_antisymm hgammaCost hcostGamma

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCostC1_eq_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCostC1_eq_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCostC1_eq_on ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCostC1_eq_on

end Compact

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {D : RealTimeInterval}

theorem lRegularizedAction_minimal_on_subinterval_of_absolutelyContinuousOnInterval
    (S : SolutionOn (I := I) (M := M) D) (T a c d b : ℝ)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (gamma : ℝ → M) (hgamma : Manifold.absolutelyContinuousOnInterval I gamma a b)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T gamma) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hmin : ∀ eta : ℝ → M, Manifold.absolutelyContinuousOnInterval I eta a b →
      IntervalIntegrable (lRegularizedLagrangian S T eta) _root_.MeasureTheory.MeasureSpace.volume a b →
      eta a = gamma a → eta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T eta a b) :
    ∀ delta : ℝ → M, Manifold.absolutelyContinuousOnInterval I delta c d →
      IntervalIntegrable (lRegularizedLagrangian S T delta) _root_.MeasureTheory.MeasureSpace.volume c d →
      delta c = gamma c → delta d = gamma d →
      lRegularizedAction S T gamma c d ≤ lRegularizedAction S T delta c d := by
  classical
  intro delta hdelta hdeltaInt hdeltaC hdeltaD
  have hab := hac.trans (hcd.trans hdb)
  have hgammaAC (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      Manifold.absolutelyContinuousOnInterval I gamma s t :=
    Manifold.absolutelyContinuousOnInterval_mono hgamma (by
      simpa only [_root_.Set.uIcc_of_le hst, _root_.Set.uIcc_of_le hab] using _root_.Set.Icc_subset_Icc has htb)
  have hgammaInt (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      IntervalIntegrable (lRegularizedLagrangian S T gamma) _root_.MeasureTheory.MeasureSpace.volume s t :=
    hint.mono_set (by
      simpa only [_root_.Set.uIcc_of_le hst, _root_.Set.uIcc_of_le hab] using _root_.Set.Icc_subset_Icc has htb)
  let beta : ℝ → M := (_root_.Set.Iic c).piecewise gamma delta
  have hbetaLeft (r : ℝ) (hr : r ≤ c) : beta r = gamma r := if_pos hr
  have hbetaRight (r : ℝ) (hr : c ≤ r) : beta r = delta r := by
    rcases hr.eq_or_lt with hr | hr
    · subst r
      exact (hbetaLeft c le_rfl).trans hdeltaC.symm
    · exact if_neg (not_le.mpr hr)
  have hbeta : Manifold.absolutelyContinuousOnInterval I beta a d :=
    Manifold.absolutelyContinuousOnInterval_piecewise_Iic
      (hgammaAC a c le_rfl hac (hcd.trans hdb)) hdelta hac hcd hdeltaC.symm
  let eta : ℝ → M := (_root_.Set.Iic d).piecewise beta gamma
  have heta : Manifold.absolutelyContinuousOnInterval I eta a b :=
    Manifold.absolutelyContinuousOnInterval_piecewise_Iic hbeta
      (hgammaAC d b (hac.trans hcd) hdb le_rfl) (hac.trans hcd) hdb
      ((hbetaRight d hcd).trans hdeltaD)
  have hleft : _root_.Set.EqOn eta gamma (_root_.Set.Icc a c) := by
    intro r hr
    exact (if_pos (hr.2.trans hcd)).trans (hbetaLeft r hr.2)
  have hmiddle : _root_.Set.EqOn eta delta (_root_.Set.Icc c d) := by
    intro r hr
    exact (if_pos hr.2).trans (hbetaRight r hr.1)
  have hright : _root_.Set.EqOn eta gamma (_root_.Set.Icc d b) := by
    intro r hr
    rcases hr.1.eq_or_lt with heq | hlt
    · subst r
      exact (hmiddle ⟨hcd, le_rfl⟩).trans hdeltaD
    · exact if_neg (not_le.mpr hlt)
  have hlag (alpha beta : ℝ → M) (s t : ℝ) (hst : s ≤ t)
      (heq : _root_.Set.EqOn alpha beta (_root_.Set.Icc s t)) :
      EqOn (lRegularizedLagrangian S T alpha) (lRegularizedLagrangian S T beta) (_root_.Set.uIoo s t) := by
    intro r hr
    rw [_root_.Set.uIoo_of_le hst] at hr
    have hn : alpha =ᶠ[𝓝 r] beta := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
      exact heq (_root_.Set.Ioo_subset_Icc_self hx)
    have hv := hn.self_of_nhds
    have hder := hn.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
    unfold lRegularizedLagrangian lVelocity
    rw [hv, hder]
  have hlagLeft := hlag eta gamma a c hac hleft
  have hlagMiddle := hlag eta delta c d hcd hmiddle
  have hlagRight := hlag eta gamma d b hdb hright
  have hgammaIntLeft := hgammaInt a c le_rfl hac (hcd.trans hdb)
  have hgammaIntMiddle := hgammaInt c d hac hcd hdb
  have hgammaIntRight := hgammaInt d b (hac.trans hcd) hdb le_rfl
  have hetaIntLeft := hgammaIntLeft.congr_uIoo hlagLeft.symm
  have hetaIntMiddle := hdeltaInt.congr_uIoo hlagMiddle.symm
  have hetaIntRight := hgammaIntRight.congr_uIoo hlagRight.symm
  have hwhole := hmin eta heta ((hetaIntLeft.trans hetaIntMiddle).trans hetaIntRight)
    (hleft ⟨le_rfl, hac⟩) (hright ⟨hdb, le_rfl⟩)
  have hactLeft : lRegularizedAction S T eta a c = lRegularizedAction S T gamma a c :=
    intervalIntegral.integral_congr_uIoo hlagLeft
  have hactMiddle : lRegularizedAction S T eta c d = lRegularizedAction S T delta c d :=
    intervalIntegral.integral_congr_uIoo hlagMiddle
  have hactRight : lRegularizedAction S T eta d b = lRegularizedAction S T gamma d b :=
    intervalIntegral.integral_congr_uIoo hlagRight
  rw [← lRegularizedAction_add S T gamma a d b (hgammaIntLeft.trans hgammaIntMiddle) hgammaIntRight,
    ← lRegularizedAction_add S T gamma a c d hgammaIntLeft hgammaIntMiddle,
    ← lRegularizedAction_add S T eta a d b (hetaIntLeft.trans hetaIntMiddle) hetaIntRight,
    ← lRegularizedAction_add S T eta a c d hetaIntLeft hetaIntMiddle,
    hactLeft, hactMiddle, hactRight] at hwhole
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimal_on_subinterval_of_absolutelyContinuousOnInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimal_on_subinterval_of_absolutelyContinuousOnInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimal_on_subinterval_of_absolutelyContinuousOnInterval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimal_on_subinterval_of_absolutelyContinuousOnInterval

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
