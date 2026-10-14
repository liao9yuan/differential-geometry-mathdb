import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InjExhaustionComplete
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeMonotonicity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.SmallReducedComplete
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.LocalCostBranch
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
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
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] in
private theorem original_min_rm_bound
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4
          (S.base.rm04 t y) ≤ K)
    {Z : TangentSpace I x} {sigma : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x) :
    ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K := by
  have hsigma : 0 < sigma := lMinDomain_pos S T x Z sigma hmin
  have hdom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).mp hmin).1
  apply hRm sigma hsigma
  intro t ht
  have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
  have hback : T - t ≤ sigma := by linarith only [ht.1]
  have hsqrt : Real.sqrt (T - t) ∈ _root_.Set.Icc (0 : ℝ) (Real.sqrt sigma) :=
    ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
  have hclock := lExpPosDom_regularity S T x Z hdom hsqrt
  have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
    rw [Real.sq_sqrt hnonneg]
    ring
  simpa only [heq] using hclock

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.original_min_rm_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.original_min_rm_bound target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] in
private theorem original_inj_min_nonconj
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4
          (S.base.rm04 t y) ≤ K)
    (tau : ℝ) (htau : 0 < tau) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    (Z, tau) ∈ lMinDomain S T x ∧ ¬ IsLConjugate S T x Z tau := by
  obtain ⟨sigma, hlt, hmin⟩ := hZ
  obtain ⟨K, hK⟩ := original_min_rm_bound S T x hRm hmin
  exact ⟨lMinDomain_down_of_rm S hS K T x Z hmin htau hlt.le hK,
    lMinVec_nconj_lt_of_rm S hS K T x hmin hlt hK⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.original_inj_min_nonconj
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.original_inj_min_nonconj target :: scope.openDecls } }

theorem lRedJac_mul_src_contOn_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4
          (S.base.rm04 t y) ≤ K)
    (tau : ℝ) (htau : 0 < tau) :
    ContinuousOn
      (fun Z : E ↦ lReducedJacobian S T x Z tau * lSourceDensity S T x)
      (lInjDomain S T x tau) := by
  let U : Set E := lInjDomain S T x tau
  obtain ⟨Φ, hsource, _himage, hmap⟩ :=
    exists_lExpPartial_of_rm S hS T hg x hRm tau htau
  let Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
    { toPartialEquiv := Φ.toPartialEquiv
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num) }
  have hΨsource : Ψ.source = U := hsource
  have hΨmap : _root_.Set.EqOn Ψ (fun Z : E ↦ lExp S T x Z tau) Ψ.source := by
    intro Z hZ
    apply hmap
    change Z ∈ U
    rw [← hΨsource]
    exact hZ
  have hmin (Z : E) (hZ : Z ∈ U) :
      (Z, tau) ∈ lMinDomain S T x ∧ ¬ IsLConjugate S T x Z tau :=
    original_inj_min_nonconj S hS T x hRm tau htau hZ
  have hdom (Z : E) (hZ : Z ∈ U) :
      (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).mp (hmin Z hZ).1).1
  have hden : ContinuousOn (fun Z : E ↦ lExpDensity S T x Z tau) U := by
    have hpd : ContinuousOn
        (paramDensity (I := I) (S.base.metric (T - tau)) Ψ) U := by
      simpa only [hΨsource] using
        paramDensity_contOn (I := I) (S.base.metric (T - tau)) Ψ
    apply hpd.congr
    intro Z hZ
    exact (paramDensity_eq_lExpDensity_of_eqOn S T x tau Ψ hΨmap Z
      (by simpa only [hΨsource] using hZ)).symm
  have hact : ContinuousOn
      (fun Z : E ↦ lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau)) U := by
    intro Z hZ
    have hreg : Real.sqrt tau ∈ lRegularizedDomain S T x Z :=
      ((mem_lExpPosDom S T x Z tau).mp (hdom Z hZ)).2.2
    have hjoint := continuousAt_lRegularizedAction_lRegularizedCurve
      (I := I) S hS T x (Real.sqrt_pos.mpr htau) hreg
    change ContinuousWithinAt
      ((fun p : E × ℝ ↦
        lRegularizedAction S T (lRegularizedCurve S T x p.1) 0 p.2) ∘
          fun W : E ↦ (W, Real.sqrt tau)) U Z
    exact (ContinuousAt.comp (f := fun W : E ↦ (W, Real.sqrt tau))
      hjoint (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  have hl : ContinuousOn
      (fun Z : E ↦ redLength S T x (lExp S T x Z tau) tau) U := by
    apply (hact.div_const (2 * Real.sqrt tau)).congr
    intro Z hZ
    have hcost := ((mem_lMinDomain S T x Z tau).mp (hmin Z hZ).1).2
    have hlen : lLength S T (fun r : ℝ ↦ lExp S T x Z r) 0 tau =
        lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) := by
      change lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 tau = _
      exact lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T (lRegularizedCurve S T x Z) tau htau.le
    change lCost S T x (lExp S T x Z tau) tau / (2 * Real.sqrt tau) = _
    exact congrArg (fun q : ℝ ↦ q / (2 * Real.sqrt tau))
      (hcost.symm.trans hlen)
  have hcore : ContinuousOn
      (fun Z : E ↦
        -redLength S T x (lExp S T x Z tau) tau -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) U :=
    (hl.neg.sub continuousOn_const).sub continuousOn_const
  have hred : ContinuousOn
      (fun Z : E ↦ redDensity S T x (lExp S T x Z tau) tau) U := by
    change ContinuousOn
      (Real.exp ∘ fun Z : E ↦
        -redLength S T x (lExp S T x Z tau) tau -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) U
    exact Real.continuous_exp.comp_continuousOn hcore
  exact (hden.mul hred).congr fun Z hZ ↦
    lRedJac_mul_src_of_nonconj S T x Z tau (hdom Z hZ) (hmin Z hZ).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRedJac_mul_src_contOn_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRedJac_mul_src_contOn_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRedJac_mul_src_contOn_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.lRedJac_mul_src_contOn_of_rm

variable [ConnectedSpace M]

theorem redVolume_zero_lim_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4
          (S.base.rm04 t y) ≤ K)
    (hT : T ∈ D.regular) :
    _root_.Filter.Tendsto (fun tau : ℝ ↦ DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by
  classical
  let F : ℝ → E → ℝ≥0∞ := fun tau Z ↦
    (lInjDomain S T x tau).indicator
      (fun W ↦ ENNReal.ofReal
        (lReducedJacobian S T x W tau * lSourceDensity S T x)) Z
  let G : E → ℝ≥0∞ := fun Z ↦ ENNReal.ofReal (lSourceGaussian S T x Z)
  obtain ⟨a, b, hTab, hreg⟩ := D.exists_Icc_regular hT
  have hsmall : ∀ᶠ tau in 𝓝[>] (0 : ℝ), tau < T - a := by
    have hTa : 0 < T - a := sub_pos.mpr hTab.1
    exact (tendsto_order.1
      (tendsto_id.mono_left nhdsWithin_le_nhds)).2 (T - a) hTa
  have hslab : ∀ᶠ tau in 𝓝[>] (0 : ℝ), _root_.Set.Icc (T - tau) T ⊆ D.regular := by
    filter_upwards [hsmall] with tau htau
    exact (_root_.Set.Icc_subset_Icc (by linarith only [htau]) hTab.2.le).trans hreg
  have hmeas : ∀ᶠ tau in 𝓝[>] (0 : ℝ), Measurable (F tau) := by
    filter_upwards [self_mem_nhdsWithin] with tau htau
    have hU := (lInj_isOpen_of_rm S hS T hg x hRm tau).measurableSet
    have hcont := lRedJac_mul_src_contOn_of_rm S hS T hg x hRm tau htau
    change Measurable ((lInjDomain S T x tau).piecewise
      (ENNReal.ofReal ∘ fun Z ↦ lReducedJacobian S T x Z tau * lSourceDensity S T x) 0)
    exact ContinuousOn.measurable_piecewise
      (ENNReal.continuous_ofReal.comp_continuousOn hcont)
      continuous_zero.continuousOn hU
  have hbound : ∀ᶠ tau in 𝓝[>] (0 : ℝ),
      ∀ᵐ Z ∂modelHaar (E := E), F tau Z ≤ G Z := by
    filter_upwards [self_mem_nhdsWithin] with tau htau
    apply _root_.MeasureTheory.ae_of_all
    intro Z
    by_cases hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau
    · simp only [F, G, Set.indicator_of_mem hZ]
      exact lRedJac_src_le_of_rm S hS T x hRm tau htau hZ
    · simp only [F, Set.indicator_of_notMem hZ, zero_le]
  have hfin : ∫⁻ Z : E, G Z ∂modelHaar (E := E) ≠ (⊤ : ℝ≥0∞) := by
    rw [show (∫⁻ Z : E, G Z ∂modelHaar (E := E)) = 1 by
      simpa only [G] using lSourceGaussian_mass S T x]
    simp
  have hlim : ∀ᵐ Z ∂modelHaar (E := E),
      _root_.Filter.Tendsto (fun tau : ℝ ↦ F tau Z)
        (𝓝[>] (0 : ℝ)) (𝓝 (G Z)) := by
    apply _root_.MeasureTheory.ae_of_all
    intro Z
    have hZev := lInj_eventually_of_rm S hS T hg x hRm Z hT
    obtain ⟨rho, hZrho⟩ := hZev.exists
    obtain ⟨sigma, _hrhosigma, hminSigma⟩ := hZrho
    obtain ⟨K, hK⟩ := original_min_rm_bound S T x hRm hminSigma
    have hraw := (lRedJac_tau_lim_of_rm S hS K T x Z hminSigma hK).mul_const
      (lSourceDensity S T x)
    have hof := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hraw
    have hFeq : (fun tau : ℝ ↦ F tau Z) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun tau ↦ ENNReal.ofReal
          (lReducedJacobian S T x Z tau * lSourceDensity S T x)) := by
      filter_upwards [hZev] with tau hZ
      change (lInjDomain S T x tau).indicator
          (fun W ↦ ENNReal.ofReal
            (lReducedJacobian S T x W tau * lSourceDensity S T x)) Z = _
      exact Set.indicator_of_mem hZ _
    simpa only [G, lSourceGaussian_eq_metric_norm, Function.comp_apply, mul_assoc,
      mul_comm, mul_left_comm] using hof.congr' hFeq.symm
  have hDCT : _root_.Filter.Tendsto (fun tau : ℝ ↦ ∫⁻ Z : E, F tau Z ∂modelHaar (E := E))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫⁻ Z : E, G Z ∂modelHaar (E := E))) :=
    _root_.MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence G hmeas hbound hfin hlim
  have hmass : (∫⁻ Z : E, G Z ∂modelHaar (E := E)) = 1 :=
    by simpa only [G] using lSourceGaussian_mass S T x
  rw [hmass] at hDCT
  apply hDCT.congr'
  filter_upwards [self_mem_nhdsWithin, hslab] with tau htau hslab_tau
  rw [redVolume_lint_of_rm S hS T hg x hRm tau htau hslab_tau]
  exact _root_.MeasureTheory.lintegral_indicator (lInj_isOpen_of_rm S hS T hg x hRm tau).measurableSet _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.redVolume_zero_lim_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.redVolume_zero_lim_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.redVolume_zero_lim_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.redVolume_zero_lim_of_rm

end DifferentialGeometry.PDE.RicciFlow

end
