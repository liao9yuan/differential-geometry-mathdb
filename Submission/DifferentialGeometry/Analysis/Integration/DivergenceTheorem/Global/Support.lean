import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Local.Formula
import Submission.DifferentialGeometry.Geometry.Operator.DirectionalDerivative
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Local.IntegrationByParts
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Local.ChartInvariance
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.PartitionOfUnity
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.CompactSupport
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Submission.DifferentialGeometry.Analysis.Integration.Measure.LocalRestriction
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Compactness.LocallyCompact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.ENNReal

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

lemma pouFinset_for_compactSet
    [T2Space M] [SigmaCompactSpace M]
    {K : Set M} (hK : IsCompact K) :
    {α : M | (tsupport ((chartAtlasPOU I M) α) ∩ K).Nonempty}.Finite := by
  have hLF : LocallyFinite (fun α : M => tsupport ((chartAtlasPOU I M) α)) :=
    (chartAtlasPOU I M).locallyFinite.closure
  exact hLF.finite_nonempty_inter_compact hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.pouFinset_for_compactSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.pouFinset_for_compactSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.pouFinset_for_compactSet ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.pouFinset_for_compactSet

private lemma localDivergence_zero_of_eventuallyEq_zero [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {x : M}
    (hx : x ∈ (chartAt H α).source)
    (hev : (X : ∀ x, TangentSpace I x) =ᶠ[𝓝 x] (0 : ∀ x, TangentSpace I x)) :
    localDivergence (I := I) g α X x = 0 := by
  classical
  set y : E := extChartAt I α x with hy_def
  have hxs : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hy_target : y ∈ (extChartAt I α).target := (extChartAt I α).map_source hxs
  have hsymm_y : (extChartAt I α).symm y = x := (extChartAt I α).left_inv hxs
  have htarget_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have hcont_symm_at : ContinuousAt (extChartAt I α).symm y := by
    have hcontOn := continuousOn_extChartAt_symm (I := I) α
    exact hcontOn.continuousAt (htarget_open.mem_nhds hy_target)
  have hev_pre : ∀ i : Fin (Module.finrank ℝ E),
      (fun z : E => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z)
        =ᶠ[𝓝 y] (fun _ : E => (0 : ℝ)) := by
    intro i
    have hpull : (fun z : E => (X : ∀ x, TangentSpace I x) ((extChartAt I α).symm z))
        =ᶠ[𝓝 y]
        (fun z : E => (0 : ∀ x, TangentSpace I x) ((extChartAt I α).symm z)) := by
      have hcomap : Filter.map (extChartAt I α).symm (𝓝 y) ≤ 𝓝 x := by
        have h : Filter.Tendsto (extChartAt I α).symm (𝓝 y) (𝓝 ((extChartAt I α).symm y)) :=
          hcont_symm_at
        rw [hsymm_y] at h
        exact h
      exact hcomap (hev)
    have htarget_nhd : (extChartAt I α).target ∈ 𝓝 y := htarget_open.mem_nhds hy_target
    filter_upwards [hpull, htarget_nhd] with z hz htz
    have hXz : X ((extChartAt I α).symm z) = (0 : TangentSpace I _) := hz
    have hsymm_base : (extChartAt I α).symm z ∈
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      have hsymm_source : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target htz
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsymm_source
      exact hsymm_source
    have hcoeffZero : chartCoeffOnE (I := I) α X i z = 0 := by
      unfold chartCoeffOnE chartCoeff
      rw [hXz]
      have h0 : ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α)
          ⟨(extChartAt I α).symm z, (0 : TangentSpace I _)⟩).2 = 0 :=
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).linear ℝ hsymm_base).map_zero
      rw [h0]
      simp
    rw [hcoeffZero, _root_.MulZeroClass.zero_mul]
  rw [localDivergence_def]
  have hsum_zero : ∀ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
        (fun z => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z) y = 0 := by
    intro i
    unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
    rw [Filter.EventuallyEq.fderiv_eq (hev_pre i)]
    rw [show (fun _ : E => (0 : ℝ)) = Function.const E 0 from rfl, fderiv_const]
    rfl
  rw [show (∑ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
        (fun z => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z)
        (extChartAt I α x)) = 0 from by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [show (extChartAt I α x) = y from rfl]
    exact hsum_zero i]
  rw [zero_div]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_zero_of_eventuallyEq_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.localDivergence_zero_of_eventuallyEq_zero target :: scope.openDecls } }

lemma divergence_g_zero_of_eventuallyEq_zero [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {x : M}
    (hev : (X : ∀ x, TangentSpace I x) =ᶠ[𝓝 x] (0 : ∀ x, TangentSpace I x)) :
    divergenceG (I := I) g X x = 0 := by
  rw [divergence_g_def]
  exact localDivergence_zero_of_eventuallyEq_zero (I := I) g x X (mem_chart_source H x) hev

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_zero_of_eventuallyEq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_zero_of_eventuallyEq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_zero_of_eventuallyEq_zero ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_zero_of_eventuallyEq_zero

lemma support_divergence_g_subset [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Function.support (divergenceG (I := I) g X) ⊆ tsupport X := by
  intro x hx
  by_contra hxnotin
  have h_open : IsOpen (tsupport X)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hev : (X : ∀ x, TangentSpace I x) =ᶠ[𝓝 x] (0 : ∀ x, TangentSpace I x) := by
    filter_upwards [h_open.mem_nhds hxnotin] with y hy
    change X y = (0 : TangentSpace I y)
    by_contra hne
    have hyS : y ∈ Function.support (X : ∀ x, TangentSpace I x) := hne
    exact hy (subset_tsupport _ hyS)
  exact hx (divergence_g_zero_of_eventuallyEq_zero (I := I) g X hev)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.support_divergence_g_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.support_divergence_g_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.support_divergence_g_subset ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.support_divergence_g_subset

lemma tsupport_divergence_g_subset [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    tsupport (divergenceG (I := I) g X) ⊆ tsupport X :=
  closure_minimal (support_divergence_g_subset (I := I) g X) (isClosed_tsupport _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.tsupport_divergence_g_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.tsupport_divergence_g_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.tsupport_divergence_g_subset ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.tsupport_divergence_g_subset

lemma hasCompactSupport_divergence_g [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    {X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯} (hX : HasCompactSupport X) :
    HasCompactSupport (divergenceG (I := I) g X) :=
  hX.mono' (support_divergence_g_subset (I := I) g X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.hasCompactSupport_divergence_g then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.hasCompactSupport_divergence_g"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.hasCompactSupport_divergence_g ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.hasCompactSupport_divergence_g

omit [Module.Finite ℝ E] in
lemma tangentSectionAction_zero_of_X_zero
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : M → ℝ) {x : M} (hx : X x = (0 : TangentSpace I x)) :
    tangentSectionAction (I := I) X f x = 0 := by
  change (mfderiv I 𝓘(ℝ, ℝ) f x) (X x) = 0
  rw [hx, ContinuousLinearMap.map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction_zero_of_X_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction_zero_of_X_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction_zero_of_X_zero ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction_zero_of_X_zero

omit [Module.Finite ℝ E] in
lemma support_tangentSectionAction_subset
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) :
    Function.support (tangentSectionAction (I := I) X f) ⊆
      Function.support (X : ∀ x, TangentSpace I x) := by
  intro x hx
  by_contra hne
  have hX0 : X x = (0 : TangentSpace I x) :=
    Function.notMem_support.mp hne
  exact hx (tangentSectionAction_zero_of_X_zero (I := I) X f hX0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.support_tangentSectionAction_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.support_tangentSectionAction_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.support_tangentSectionAction_subset ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.support_tangentSectionAction_subset

omit [Module.Finite ℝ E] in
lemma tsupport_tangentSectionAction_subset
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) :
    tsupport (tangentSectionAction (I := I) X f) ⊆ tsupport X :=
  closure_minimal
    ((support_tangentSectionAction_subset (I := I) X f).trans
      (subset_tsupport (X : ∀ x, TangentSpace I x))) (isClosed_tsupport _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.tsupport_tangentSectionAction_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.tsupport_tangentSectionAction_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.tsupport_tangentSectionAction_subset ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.tsupport_tangentSectionAction_subset

omit [Module.Finite ℝ E] in
lemma hasCompactSupport_tangentSectionAction
    {X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯} (hX : HasCompactSupport X)
    (f : M → ℝ) :
    HasCompactSupport (tangentSectionAction (I := I) X f) :=
  hX.mono' ((support_tangentSectionAction_subset (I := I) X f).trans
    (subset_tsupport (X : ∀ x, TangentSpace I x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.hasCompactSupport_tangentSectionAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.hasCompactSupport_tangentSectionAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.hasCompactSupport_tangentSectionAction ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.hasCompactSupport_tangentSectionAction

lemma _root_.Submission.DifferentialGeometry.Integral.Measure.integrable_chartLocalMeasure_of_compactSupport_subset_chartSource
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    Integrable f (chartLocalMeasure (I := I) g α) := by
  classical
  have hsupp_compact : IsCompact (tsupport f) := hf_cs
  have hμ_support : chartLocalMeasure (I := I) g α (tsupport f) < ⊤ :=
    chartLocalMeasure_compact_lt_top (I := I) g α hsupp_compact hf_support
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖f x‖ ≤ C := by
    have hCpt := hsupp_compact.image hf_cont.norm
    obtain ⟨C, hCmem⟩ := hCpt.bddAbove
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ tsupport f
    · exact (hCmem ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · have hf_zero : f x = 0 := by
        by_contra hne
        exact hx (subset_tsupport _ hne)
      simp [hf_zero]
  have hbnd : ∀ᵐ x ∂(chartLocalMeasure (I := I) g α),
      ENNReal.ofReal ‖f x‖ ≤
        ENNReal.ofReal C * (tsupport f).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · rw [Set.indicator_of_mem hx, mul_one]
      exact ENNReal.ofReal_le_ofReal (hC x)
    · rw [Set.indicator_of_notMem hx, _root_.MulZeroClass.mul_zero]
      have hf_zero : f x = 0 := by
        by_contra hne
        exact hx (subset_tsupport _ hne)
      rw [hf_zero]; simp
  refine ⟨hf_cont.aestronglyMeasurable, ?_⟩
  rw [_root_.MeasureTheory.hasFiniteIntegral_iff_norm]
  calc ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂(chartLocalMeasure (I := I) g α)
      ≤ ∫⁻ x, ENNReal.ofReal C *
            (tsupport f).indicator (fun _ => (1 : ℝ≥0∞)) x
            ∂(chartLocalMeasure (I := I) g α) := _root_.MeasureTheory.lintegral_mono_ae hbnd
    _ = ENNReal.ofReal C * chartLocalMeasure (I := I) g α (tsupport f) := by
          rw [_root_.MeasureTheory.lintegral_const_mul _ ((measurable_const).indicator
            (isClosed_tsupport _).measurableSet)]
          rw [_root_.MeasureTheory.lintegral_indicator (isClosed_tsupport _).measurableSet]
          rw [_root_.MeasureTheory.setLIntegral_const, one_mul]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrable_chartLocalMeasure_of_compactSupport_subset_chartSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrable_chartLocalMeasure_of_compactSupport_subset_chartSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrable_chartLocalMeasure_of_compactSupport_subset_chartSource ``Submission.DifferentialGeometry.Integral.Measure.integrable_chartLocalMeasure_of_compactSupport_subset_chartSource

private lemma withDensity_pou_restrict_eq_zero_of_disjoint
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {α : M} {K : Set M} (hK_meas : MeasurableSet K)
    (hα_disj : tsupport ((chartAtlasPOU I M) α : M → ℝ) ∩ K = ∅) :
    ((chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x))).restrict K = 0 := by
  classical
  ext A hA
  rw [Measure.restrict_apply hA, Measure.coe_zero, Pi.zero_apply]
  rw [MeasureTheory.withDensity_apply _ (hA.inter hK_meas)]
  refine _root_.MeasureTheory.setLIntegral_eq_zero (hA.inter hK_meas) ?_
  intro x hx
  obtain ⟨_, hxK⟩ := hx
  have hx_notin : x ∉ tsupport ((chartAtlasPOU I M) α : M → ℝ) := by
    intro hx_in
    have : x ∈ tsupport ((chartAtlasPOU I M) α : M → ℝ) ∩ K := ⟨hx_in, hxK⟩
    rw [hα_disj] at this
    exact (Set.notMem_empty _) this
  have hρα_zero : ((chartAtlasPOU I M) α : M → ℝ) x = 0 := by
    by_contra hne
    exact hx_notin (subset_tsupport _ hne)
  change ENNReal.ofReal (((chartAtlasPOU I M) α : M → ℝ) x) = 0
  rw [hρα_zero]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.withDensity_pou_restrict_eq_zero_of_disjoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.withDensity_pou_restrict_eq_zero_of_disjoint target :: scope.openDecls } }

private lemma riemannianVolumeMeasure_restrict_eq_finset_sum
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {K : Set M} (hK_compact : IsCompact K) :
    (riemannianVolumeMeasure (I := I) (M := M) g).restrict K =
      (∑ α ∈ (pouFinset_for_compactSet (I := I) (M := M) hK_compact).toFinset,
        (chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x))).restrict K := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (_root_.Set.univ : Set M) := chartAtlasPOU I M
  set S : Finset M := (pouFinset_for_compactSet (I := I) (M := M) hK_compact).toFinset with hS_def
  have hSmem : ∀ {α : M}, α ∈ S ↔
      (tsupport ((chartAtlasPOU I M) α) ∩ K).Nonempty := fun {α} =>
    Set.Finite.mem_toFinset _
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  set f : M → MeasureTheory.Measure M := fun α =>
    ((chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x))).restrict K with hf_def
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def]
  rw [MeasureTheory.Measure.restrict_sum _ hK_meas]
  change MeasureTheory.Measure.sum f =
    (∑ α ∈ S, (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x))).restrict K
  rw [show MeasureTheory.Measure.sum f
      = MeasureTheory.Measure.sum (fun i : (S : Set M) => f i)
        + MeasureTheory.Measure.sum (fun i : ↥((S : Set M)ᶜ) => f i) from
    (MeasureTheory.Measure.sum_add_sum_compl (S : Set M) f).symm]
  have hcompl_zero : MeasureTheory.Measure.sum (fun i : ↥((S : Set M)ᶜ) => f i) = 0 := by
    have hzero : ∀ i : ↥((S : Set M)ᶜ), f i = 0 := by
      intro i
      have hi : (i : M) ∉ S := i.2
      have hi_iff := hSmem (α := (i : M))
      rw [hi_iff] at hi
      rw [Set.not_nonempty_iff_eq_empty] at hi
      exact withDensity_pou_restrict_eq_zero_of_disjoint (I := I) (M := M) g hK_meas hi
    ext B hB
    rw [MeasureTheory.Measure.sum_apply _ hB]
    simp [hzero]
  rw [hcompl_zero, add_zero]
  have hSF : MeasureTheory.Measure.sum (fun i : (S : Set M) => f i) = ∑ α ∈ S, f α :=
    MeasureTheory.Measure.sum_coe_finset S f
  rw [hSF]
  refine Finset.induction
    (motive := fun (T : Finset M) =>
      ∑ α ∈ T, f α = (∑ α ∈ T, (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))).restrict K)
    ?_ ?_ S
  · simp only [Finset.sum_empty, hf_def]
    exact (Measure.restrict_zero (s := K)).symm
  · intro α t hα ih
    simp only [Finset.sum_insert hα]
    rw [show f α = ((chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))).restrict K from rfl]
    rw [ih, ← Measure.restrict_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.riemannianVolumeMeasure_restrict_eq_finset_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.riemannianVolumeMeasure_restrict_eq_finset_sum target :: scope.openDecls } }

theorem _root_.Submission.DifferentialGeometry.Integral.Measure.integrable_riemannianVolumeMeasure_and_integral_eq_chartLocalMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ}
    (hf : _root_.MeasureTheory.Integrable f (chartLocalMeasure (I := I) g α))
    (hf_cs : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, f x ∂(chartLocalMeasure (I := I) g α) := by
  have hrestrict :=
    riemannianVolumeMeasure_restrict_eq_chartLocalMeasure_restrict
      (I := I) (M := M) g α hf_cs hf_supp
  have hzero : ∀ x, x ∉ tsupport f → f x = 0 := by
    intro x hx
    by_contra hne
    exact hx (subset_tsupport _ hne)
  have hglobal_on : _root_.MeasureTheory.IntegrableOn f (tsupport f)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    change _root_.MeasureTheory.Integrable f
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict (tsupport f))
    rw [hrestrict]
    exact hf.integrableOn
  refine ⟨hglobal_on.integrable_of_forall_notMem_eq_zero hzero, ?_⟩
  calc
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x in tsupport f, f x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      (_root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x in tsupport f, f x ∂(chartLocalMeasure (I := I) g α) := by
      rw [hrestrict]
    _ = ∫ x, f x ∂(chartLocalMeasure (I := I) g α) :=
      _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrable_riemannianVolumeMeasure_and_integral_eq_chartLocalMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrable_riemannianVolumeMeasure_and_integral_eq_chartLocalMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrable_riemannianVolumeMeasure_and_integral_eq_chartLocalMeasure ``Submission.DifferentialGeometry.Integral.Measure.integrable_riemannianVolumeMeasure_and_integral_eq_chartLocalMeasure

private lemma integral_riemannianVolumeMeasure_of_compactSupport_eq_finset_sum
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {h : M → ℝ} (hh_cont : Continuous h) (hh_cs : HasCompactSupport h) :
    ∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ (pouFinset_for_compactSet (I := I) (M := M) hh_cs).toFinset,
          ∫ x, h x * ((chartAtlasPOU I M) α : M → ℝ) x
            ∂(chartLocalMeasure (I := I) g α) := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (_root_.Set.univ : Set M) := chartAtlasPOU I M
  set K : Set M := tsupport h with hK_def
  have hK_compact : IsCompact K := hh_cs
  have hK_closed : IsClosed K := isClosed_tsupport _
  have hK_meas : MeasurableSet K := hK_closed.measurableSet
  set S : Finset M := (pouFinset_for_compactSet (I := I) (M := M) hK_compact).toFinset
  have : _root_.MeasureTheory.IsLocallyFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  have hLHS : ∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∫ x in K, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine (_root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := riemannianVolumeMeasure
        (I := I) (M := M) g) (s := K) (f := h) ?_).symm
    intro x hx
    by_contra hne
    exact hx (subset_tsupport _ hne)
  rw [hLHS]
  rw [show (∫ x in K, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = ∫ x, h x ∂((riemannianVolumeMeasure (I := I) (M := M) g).restrict K) from rfl]
  rw [riemannianVolumeMeasure_restrict_eq_finset_sum (I := I) (M := M) g hK_compact]
  rw [show ∫ x, h x ∂((∑ α ∈ S, (chartLocalMeasure (I := I) g α).withDensity
            (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y))).restrict K)
      = ∫ x in K, h x ∂(∑ α ∈ S, (chartLocalMeasure (I := I) g α).withDensity
            (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y))) from rfl]
  rw [_root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ∑ α ∈ S,
        (chartLocalMeasure (I := I) g α).withDensity
        (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y)))
        (s := K) (f := h) (fun x hx => ?_)]
  swap
  · by_contra hne
    exact hx (subset_tsupport _ hne)
  rw [show ∫ x, h x ∂(∑ α ∈ S, (chartLocalMeasure (I := I) g α).withDensity
        (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y)))
      = ∑ α ∈ S, ∫ x, h x ∂((chartLocalMeasure (I := I) g α).withDensity
        (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y))) from ?_]
  swap
  · have hh_int : ∀ α ∈ S, _root_.MeasureTheory.Integrable h
        ((chartLocalMeasure (I := I) g α).withDensity
          (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y))) := by
      intro α _
      have hh_int_global : _root_.MeasureTheory.Integrable h (riemannianVolumeMeasure (I := I) (M := M) g) :=
        hh_cont.integrable_of_hasCompactSupport hh_cs
      exact hh_int_global.mono_measure
        (chartLocalMeasure_withDensity_le_riemannianMeasure (I := I) (M := M) g ρ α)
    exact _root_.MeasureTheory.integral_finsetSum_measure hh_int
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have hρ_aem : AEMeasurable (fun x : M => ENNReal.ofReal ((ρ α : M → ℝ) x))
      (chartLocalMeasure (I := I) g α) :=
    (ENNReal.measurable_ofReal.comp ((ρ α).contMDiff.continuous).measurable).aemeasurable
  have hρ_lt_top : ∀ᵐ x ∂(chartLocalMeasure (I := I) g α),
      ENNReal.ofReal ((ρ α : M → ℝ) x) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => by simp)
  rw [integral_withDensity_eq_integral_toReal_smul₀
        (μ := chartLocalMeasure (I := I) g α)
        (f := fun x : M => ENNReal.ofReal ((ρ α : M → ℝ) x)) hρ_aem hρ_lt_top
        (g := h)]
  refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  change (ENNReal.ofReal ((ρ α : M → ℝ) x)).toReal • h x = h x * ((ρ α : M → ℝ) x)
  rw [ENNReal.toReal_ofReal (ρ.nonneg α x), smul_eq_mul, mul_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_riemannianVolumeMeasure_of_compactSupport_eq_finset_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.integral_riemannianVolumeMeasure_of_compactSupport_eq_finset_sum target :: scope.openDecls } }

private lemma integral_riemannianVolumeMeasure_eq_chartLocal_of_compactSupport_in_chart
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α₀ : M)
    {h : M → ℝ} (hh_cont : Continuous h) (hh_cs : HasCompactSupport h)
    (hh_support : tsupport h ⊆ (chartAt H α₀).source) :
    ∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, h x ∂(chartLocalMeasure (I := I) g α₀) := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (_root_.Set.univ : Set M) := chartAtlasPOU I M
  set K : Set M := tsupport h
  set S : Finset M := (pouFinset_for_compactSet (I := I) (M := M) (hh_cs : IsCompact K)).toFinset
  have hSmem : ∀ {α : M}, α ∈ S ↔ (tsupport ((chartAtlasPOU I M) α) ∩ K).Nonempty :=
    fun {α} => Set.Finite.mem_toFinset _
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) :=
    chartAtlasPOU_isSubordinate I M
  rw [integral_riemannianVolumeMeasure_of_compactSupport_eq_finset_sum (I := I) (M := M) g
      hh_cont hh_cs]
  have h_step_b : ∀ α ∈ S,
      ∫ x, h x * ((ρ α : M → ℝ)) x ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, h x * ((ρ α : M → ℝ)) x ∂(chartLocalMeasure (I := I) g α₀) := by
    intro α _
    refine chartLocalMeasure_integral_eq_of_support_in_overlap (I := I) g α α₀
      (fun x => h x * (ρ α : M → ℝ) x) ?_
    intro x hx
    by_cases hxα : x ∈ (chartAt H α).source
    · have hxα₀ : x ∉ (chartAt H α₀).source := fun h' => hx ⟨hxα, h'⟩
      have hxK : x ∉ K := fun h' => hxα₀ (hh_support h')
      have hh_zero : h x = 0 := by
        by_contra hne
        exact hxK (subset_tsupport _ hne)
      rw [hh_zero, _root_.MulZeroClass.zero_mul]
    · have hxnotin : x ∉ tsupport (ρ α : M → ℝ) := fun h' => hxα (hρsub α h')
      have hρα_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne
        exact hxnotin (subset_tsupport _ hne)
      rw [hρα_zero, _root_.MulZeroClass.mul_zero]
  rw [Finset.sum_congr rfl h_step_b]
  have hint_each : ∀ α ∈ S, _root_.MeasureTheory.Integrable (fun x : M => h x * (ρ α : M → ℝ) x)
      (chartLocalMeasure (I := I) g α₀) := by
    intro α _
    have hcont : Continuous (fun x : M => h x * (ρ α : M → ℝ) x) :=
      hh_cont.mul (ρ α).contMDiff.continuous
    have hsupp_sub : tsupport (fun x : M => h x * (ρ α : M → ℝ) x) ⊆ tsupport h := by
      refine closure_minimal ?_ (isClosed_tsupport _)
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hne
      have hh_zero : h x = 0 := by
        by_contra hne'
        exact hne (subset_tsupport _ hne')
      exact hx (by rw [hh_zero, _root_.MulZeroClass.zero_mul])
    have hcs_each : HasCompactSupport (fun x : M => h x * (ρ α : M → ℝ) x) :=
      hh_cs.mono' (subset_trans (subset_tsupport _) hsupp_sub)
    refine integrable_chartLocalMeasure_of_compactSupport_subset_chartSource (I := I) g α₀
      hcont hcs_each (hsupp_sub.trans hh_support)
  rw [show (∑ α ∈ S, ∫ x, h x * (ρ α : M → ℝ) x ∂(chartLocalMeasure (I := I) g α₀))
      = ∫ x, ∑ α ∈ S, h x * (ρ α : M → ℝ) x ∂(chartLocalMeasure (I := I) g α₀) from
        (_root_.MeasureTheory.integral_finsetSum (μ := chartLocalMeasure (I := I) g α₀) S hint_each).symm]
  refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  change (∑ α ∈ S, h x * (ρ α : M → ℝ) x) = h x
  rw [← Finset.mul_sum]
  by_cases hxK : x ∈ K
  · have hsum_one : ∑ α ∈ S, (ρ α : M → ℝ) x = 1 := by
      have hfins_S : ρ.finsupport x ⊆ S := by
        intro α hα
        rw [hSmem]
        rw [ρ.mem_finsupport] at hα
        exact ⟨x, subset_tsupport _ hα, hxK⟩
      exact ρ.sum_finsupport' x (Set.mem_univ x) hfins_S
    rw [hsum_one, mul_one]
  · have hh_zero : h x = 0 := by
      by_contra hne
      exact hxK (subset_tsupport _ hne)
    rw [hh_zero, _root_.MulZeroClass.zero_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_riemannianVolumeMeasure_eq_chartLocal_of_compactSupport_in_chart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.integral_riemannianVolumeMeasure_eq_chartLocal_of_compactSupport_in_chart target :: scope.openDecls } }

private lemma exists_smooth_cutoff_compactSupport_one_nhds
    [T2Space M] [SigmaCompactSpace M]
    {K : Set M} (hK_compact : IsCompact K) :
    ∃ χ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      (∀ᶠ y in 𝓝ˢ K, χ y = 1) ∧ (∀ y, χ y ∈ _root_.Set.Icc (0 : ℝ) 1) := by
  classical
  have : LocallyCompactSpace M := locallyCompactSpace_of_chartedSpace E H I M
  obtain ⟨L, hL_compact, hKL, _hLuniv⟩ :=
    exists_compact_between hK_compact isOpen_univ (Set.subset_univ K)
  have : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  have : NormalSpace M := NormalSpace.of_regularSpace_lindelofSpace
  obtain ⟨f, hf_one, hf_zero, hf_range⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := I) (M := M)
      (n := (⊤ : ℕ∞))
      hK_compact.isClosed hKL
  refine ⟨f, f.contMDiff.of_le (mod_cast le_top), ?_, hf_one, hf_range⟩
  refine HasCompactSupport.of_support_subset_isCompact hL_compact ?_
  intro y hy
  by_contra hyL
  exact hy (hf_zero y hyL)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.exists_smooth_cutoff_compactSupport_one_nhds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.exists_smooth_cutoff_compactSupport_one_nhds target :: scope.openDecls } }

theorem integral_divergence_eq_zero_of_hasCompactSupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) :
    ∫ x, divergenceG (I := I) g X x ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (_root_.Set.univ : Set M) := chartAtlasPOU I M
  set K : Set M := tsupport X
  have hK_compact : IsCompact K := hX
  set S : Finset M := (pouFinset_for_compactSet (I := I) (M := M) hK_compact).toFinset with hS_def
  have hSmem : ∀ {α : M}, α ∈ S ↔ (tsupport ((chartAtlasPOU I M) α) ∩ K).Nonempty :=
    fun {α} => Set.Finite.mem_toFinset _
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) :=
    chartAtlasPOU_isSubordinate I M
  have hdiv_smooth : ContMDiff I 𝓘(ℝ) ∞ (divergenceG (I := I) g X) :=
    divergence_g_contMDiff (I := I) g X
  have hdiv_cont : Continuous (divergenceG (I := I) g X) := hdiv_smooth.continuous
  have hdiv_cs : HasCompactSupport (divergenceG (I := I) g X) :=
    hasCompactSupport_divergence_g (I := I) g hX
  have hdiv_support : tsupport (divergenceG (I := I) g X) ⊆ K :=
    tsupport_divergence_g_subset (I := I) g X
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_one_nhds, hχ_range⟩ :=
    exists_smooth_cutoff_compactSupport_one_nhds (I := I) (M := M) hK_compact
  have h_step_a : ∫ x, divergenceG (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ S, ∫ x, divergenceG (I := I) g X x * (ρ α : M → ℝ) x
          ∂(chartLocalMeasure (I := I) g α) := by
    have hSdiv : (pouFinset_for_compactSet (I := I) (M := M) hdiv_cs).toFinset ⊆ S := by
      intro α hα
      rw [Set.Finite.mem_toFinset _] at hα
      rw [hSmem]
      rcases hα with ⟨x, hxρα, hx⟩
      exact ⟨x, hxρα, hdiv_support hx⟩
    rw [integral_riemannianVolumeMeasure_of_compactSupport_eq_finset_sum (I := I) (M := M) g
        hdiv_cont hdiv_cs]
    apply Finset.sum_subset hSdiv
    intro α _ hα_notin
    rw [Set.Finite.mem_toFinset _] at hα_notin
    simp only [Set.mem_ofPred_eq] at hα_notin
    rw [Set.not_nonempty_iff_eq_empty] at hα_notin
    have h_zero : ∀ x : M, divergenceG (I := I) g X x * (ρ α : M → ℝ) x = 0 := by
      intro x
      by_cases hxρ : x ∈ tsupport ((chartAtlasPOU I M) α : M → ℝ)
      · have hxnotin : x ∉ tsupport (divergenceG (I := I) g X) := by
          intro h
          have : x ∈ tsupport ((chartAtlasPOU I M) α : M → ℝ) ∩
              tsupport (divergenceG (I := I) g X) := ⟨hxρ, h⟩
          rw [hα_notin] at this
          exact (Set.notMem_empty _) this
        have hdiv_zero : divergenceG (I := I) g X x = 0 := by
          by_contra hne
          exact hxnotin (subset_tsupport _ hne)
        rw [hdiv_zero, _root_.MulZeroClass.zero_mul]
      · have hρα_zero : (ρ α : M → ℝ) x = 0 := by
          by_contra hne
          exact hxρ (subset_tsupport _ hne)
        rw [hρα_zero, _root_.MulZeroClass.mul_zero]
    rw [show (fun x : M => divergenceG (I := I) g X x * (ρ α : M → ℝ) x) =
        (fun _ : M => (0 : ℝ)) from funext h_zero]
    exact _root_.MeasureTheory.integral_zero ..
  rw [h_step_a]
  have hχ_one_K : ∀ x ∈ K, χ x = 1 := by
    intro x hxK
    rcases (Filter.eventually_iff_exists_mem.mp hχ_one_nhds) with ⟨U, hU_nhds, hU_eq⟩
    have hU_open : K ⊆ interior U := by
      rwa [← subset_interior_iff_mem_nhdsSet] at hU_nhds
    exact hU_eq x (interior_subset (hU_open hxK))
  have hχ_one_support : ∀ x ∈ tsupport (divergenceG (I := I) g X), χ x = 1 :=
    fun x hx => hχ_one_K x (hdiv_support hx)
  have hdiv_mul_chi_eq : ∀ x : M,
      divergenceG (I := I) g X x * χ x = divergenceG (I := I) g X x := by
    intro x
    by_cases hxsupp : x ∈ tsupport (divergenceG (I := I) g X)
    · rw [hχ_one_support x hxsupp, mul_one]
    · have hdiv_zero : divergenceG (I := I) g X x = 0 := by
        by_contra hne
        exact hxsupp (subset_tsupport _ hne)
      rw [hdiv_zero, _root_.MulZeroClass.zero_mul]
  have h_step_b : ∀ α ∈ S,
      ∫ x, divergenceG (I := I) g X x * (ρ α : M → ℝ) x ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, divergenceG (I := I) g X x *
            (χ x * (ρ α : M → ℝ) x) ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have hχx : divergenceG (I := I) g X x * χ x = divergenceG (I := I) g X x :=
      hdiv_mul_chi_eq x
    calc divergenceG (I := I) g X x * (ρ α : M → ℝ) x
        = (divergenceG (I := I) g X x * χ x) * (ρ α : M → ℝ) x := by rw [hχx]
      _ = divergenceG (I := I) g X x * (χ x * (ρ α : M → ℝ) x) := by ring
  rw [Finset.sum_congr rfl h_step_b]
  have h_step_c : ∀ α ∈ S,
      ∫ x, divergenceG (I := I) g X x * (χ x * (ρ α : M → ℝ) x)
        ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, localDivergence (I := I) g α X x *
            (χ x * (ρ α : M → ℝ) x) ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    by_cases hxα : x ∈ (chartAt H α).source
    · simp only [voss_weyl_divergence_formula (I := I) g α X hxα]
    · have hxnotin : x ∉ tsupport (ρ α : M → ℝ) := fun h => hxα (hρsub α h)
      have hρα_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne
        exact hxnotin (subset_tsupport _ hne)
      change divergenceG (I := I) g X x * (χ x * (ρ α : M → ℝ) x) =
        localDivergence (I := I) g α X x * (χ x * (ρ α : M → ℝ) x)
      rw [hρα_zero, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero]
  rw [Finset.sum_congr rfl h_step_c]
  set φ : M → M → ℝ := fun α x => χ x * (ρ α : M → ℝ) x with hφ_def
  have hφ_smooth : ∀ α : M, ContMDiff I 𝓘(ℝ) ∞ (φ α) := fun α =>
    hχ_smooth.mul (ρ α).contMDiff
  have hφ_cs : ∀ α : M, HasCompactSupport (φ α) := fun α => hχ_cs.mul_right
  have hφ_support : ∀ α : M, tsupport (φ α) ⊆ (chartAt H α).source := fun α => by
    have h1 : tsupport (φ α) ⊆ tsupport (ρ α : M → ℝ) := by
      refine closure_minimal ?_ (isClosed_tsupport _)
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hne
      have hρ_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne'
        exact hne (subset_tsupport _ hne')
      exact hx (by change χ x * (ρ α : M → ℝ) x = 0; rw [hρ_zero, _root_.MulZeroClass.mul_zero])
    exact h1.trans (hρsub α)
  have h_step_d : ∀ α ∈ S,
      ∫ x, localDivergence (I := I) g α X x * (φ α x)
          ∂(chartLocalMeasure (I := I) g α) =
        -∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    exact chart_local_ibp (I := I) g α X (hφ_smooth α) (hφ_cs α) (hφ_support α)
  rw [Finset.sum_congr rfl h_step_d]
  rw [show (∑ α ∈ S, -∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α))
      = -(∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α)) from by
    rw [← Finset.sum_neg_distrib]]
  have hAct_smooth : ∀ α : M,
      ContMDiff I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X (φ α)) := fun α =>
    tangentSectionAction_contMDiff (I := I) X (hφ_smooth α)
  have hAct_cont : ∀ α : M,
      Continuous (tangentSectionAction (I := I) X (φ α)) := fun α =>
    (hAct_smooth α).continuous
  have hAct_support : ∀ α : M,
      tsupport (tangentSectionAction (I := I) X (φ α)) ⊆ (chartAt H α).source := by
    intro α
    refine subset_trans ?_ (hφ_support α)
    refine closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hne
    have h_open : IsOpen (tsupport (φ α))ᶜ := (isClosed_tsupport _).isOpen_compl
    have hev : (φ α) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hne] with y hy
      by_contra hne'
      exact hy (subset_tsupport _ hne')
    have hmfderiv_zero : mfderiv I 𝓘(ℝ) (φ α) x = 0 := by
      rw [Filter.EventuallyEq.mfderiv_eq hev]
      rw [mfderiv_const]
      rfl
    have hAct_zero : tangentSectionAction (I := I) X (φ α) x = 0 := by
      change mfderiv I 𝓘(ℝ) (φ α) x (X x) = 0
      rw [hmfderiv_zero]
      rfl
    exact hx hAct_zero
  have hAct_cs : ∀ α : M, HasCompactSupport (tangentSectionAction (I := I) X (φ α)) := by
    intro α
    have h1 : Function.support (tangentSectionAction (I := I) X (φ α)) ⊆ tsupport (φ α) := by
      intro x hx
      by_contra hne
      have h_open : IsOpen (tsupport (φ α))ᶜ := (isClosed_tsupport _).isOpen_compl
      have hev : (φ α) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hne] with y hy
        by_contra hne'
        exact hy (subset_tsupport _ hne')
      have hmfderiv_zero : mfderiv I 𝓘(ℝ) (φ α) x = 0 := by
        rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_const]
        rfl
      have hAct_zero : tangentSectionAction (I := I) X (φ α) x = 0 := by
        change mfderiv I 𝓘(ℝ) (φ α) x (X x) = 0
        rw [hmfderiv_zero]
        rfl
      exact hx hAct_zero
    exact (hφ_cs α).mono' h1
  have h_step_e : ∀ α ∈ S,
      ∫ x, tangentSectionAction (I := I) X (φ α) x ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, tangentSectionAction (I := I) X (φ α) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro α _
    exact (integral_riemannianVolumeMeasure_eq_chartLocal_of_compactSupport_in_chart
      (I := I) g α (hAct_cont α) (hAct_cs α) (hAct_support α)).symm
  rw [Finset.sum_congr rfl h_step_e]
  have : _root_.MeasureTheory.IsLocallyFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  have hAct_int : ∀ α ∈ S, _root_.MeasureTheory.Integrable
      (fun x : M => tangentSectionAction (I := I) X (φ α) x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := fun α _ =>
    (hAct_cont α).integrable_of_hasCompactSupport (hAct_cs α)
  rw [show (∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = ∫ x, ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from
        (_root_.MeasureTheory.integral_finsetSum (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          S hAct_int).symm]
  have h_pt : ∀ x : M,
      ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x = 0 := by
    intro x
    by_cases hXx : X x = (0 : TangentSpace I x)
    · refine Finset.sum_eq_zero (fun α _ => ?_)
      exact tangentSectionAction_zero_of_X_zero (I := I) X (φ α) hXx
    · have hxsupp : x ∈ Function.support (X : ∀ x, TangentSpace I x) := hXx
      have hxK : x ∈ K := subset_tsupport _ hxsupp
      rcases (Filter.eventually_iff_exists_mem.mp hχ_one_nhds) with ⟨U, hU_nhds, hU_eq⟩
      have hU_int : K ⊆ interior U := by
        rwa [← subset_interior_iff_mem_nhdsSet] at hU_nhds
      have hxU : x ∈ interior U := hU_int hxK
      have hU_x_nhd : U ∈ 𝓝 x := mem_nhds_iff.mpr
        ⟨interior U, interior_subset, isOpen_interior, hxU⟩
      have hev_φα : ∀ α : M, (φ α) =ᶠ[𝓝 x] (fun y => (ρ α : M → ℝ) y) := by
        intro α
        filter_upwards [hU_x_nhd] with y hyU
        change χ y * (ρ α : M → ℝ) y = (ρ α : M → ℝ) y
        rw [hU_eq y hyU, one_mul]
      have hmfderiv_φα : ∀ α : M,
          mfderiv I 𝓘(ℝ) (φ α) x = mfderiv I 𝓘(ℝ) ((ρ α : M → ℝ)) x := by
        intro α
        exact Filter.EventuallyEq.mfderiv_eq (hev_φα α)
      have hact_eq : ∀ α : M,
          tangentSectionAction (I := I) X (φ α) x =
            tangentSectionAction (I := I) X ((ρ α : M → ℝ)) x := by
        intro α
        unfold tangentSectionAction
        rw [hmfderiv_φα α]
        rfl
      rw [show (∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x)
          = ∑ α ∈ S, tangentSectionAction (I := I) X ((ρ α : M → ℝ)) x from
            Finset.sum_congr rfl (fun α _ => hact_eq α)]
      have hMDiff_each : ∀ α ∈ S,
          MDifferentiableAt I 𝓘(ℝ) ((ρ α : M → ℝ)) x :=
        fun α _ => (ρ α).contMDiff.mdifferentiable (by simp) x
      have hcomm := tangentSectionAction_finset_sum (I := I) X S
        (fun α => ((ρ α : M → ℝ))) x hMDiff_each
      rw [← hcomm]
      have h_finset_eq_one : (fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y) =ᶠ[𝓝 x]
          (fun _ : M => (1 : ℝ)) := by
        filter_upwards [ρ.eventually_finsupport_subset x] with y hy
        have hfins_S : ρ.finsupport y ⊆ S := by
          intro α hα
          rw [hSmem]
          rw [ρ.mem_finsupport] at hα
          have hα_x : α ∈ ρ.fintsupport x := hy ((ρ.mem_finsupport y).mpr hα)
          have hx_tsupp : x ∈ tsupport (ρ α : M → ℝ) :=
            (ρ.mem_fintsupport_iff x α).mp hα_x
          exact ⟨x, hx_tsupp, hxK⟩
        exact ρ.sum_finsupport' y (Set.mem_univ y) hfins_S
      unfold tangentSectionAction
      have h_fun_eq : (∑ α ∈ S, (ρ α : M → ℝ)) = fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y := by
        funext y
        rw [Finset.sum_apply]
      rw [h_fun_eq]
      rw [Filter.EventuallyEq.mfderiv_eq h_finset_eq_one]
      rw [mfderiv_const]
      rfl
  rw [show (fun x : M => ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x)
      = (fun _ : M => (0 : ℝ)) from funext h_pt]
  rw [_root_.MeasureTheory.integral_zero, neg_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_hasCompactSupport ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_hasCompactSupport

end DivergenceTheorem
end Integral
end DifferentialGeometry
