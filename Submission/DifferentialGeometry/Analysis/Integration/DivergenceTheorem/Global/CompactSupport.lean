import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Local.Formula
import Submission.DifferentialGeometry.Geometry.Operator.DirectionalDerivative
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Local.IntegrationByParts
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Local.ChartInvariance
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.PartitionOfUnity
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Support

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
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

lemma chartLocalMeasure_integral_eq_of_support_in_overlap
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M)
    (f : M → ℝ)
    (hsupp : ∀ x, x ∉ (chartAt H x₀).source ∩ (chartAt H x₁).source → f x = 0) :
    ∫ x, f x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫ x, f x ∂(chartLocalMeasure (I := I) g x₁) := by
  set U : Set M := (chartAt H x₀).source ∩ (chartAt H x₁).source with hU_def
  have h₀ : ∫ x, f x ∂(chartLocalMeasure (I := I) g x₀)
      = ∫ x in U, f x ∂(chartLocalMeasure (I := I) g x₀) :=
    (_root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  have h₁ : ∫ x, f x ∂(chartLocalMeasure (I := I) g x₁)
      = ∫ x in U, f x ∂(chartLocalMeasure (I := I) g x₁) :=
    (_root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  rw [h₀, h₁]
  change ∫ x, f x ∂((chartLocalMeasure (I := I) g x₀).restrict U)
      = ∫ x, f x ∂((chartLocalMeasure (I := I) g x₁).restrict U)
  rw [chartLocalMeasure_restrict_overlap_eq (I := I) g x₀ x₁]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.chartLocalMeasure_integral_eq_of_support_in_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.chartLocalMeasure_integral_eq_of_support_in_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.chartLocalMeasure_integral_eq_of_support_in_overlap ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.chartLocalMeasure_integral_eq_of_support_in_overlap

private lemma integrable_of_compactSupport_subset_chartSource
    [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    Integrable f (chartLocalMeasure (I := I) g α) := by
  classical
  have hsupp_compact : IsCompact (tsupport f) :=
    .of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _)
  have hμ_support : chartLocalMeasure (I := I) g α (tsupport f) < ⊤ :=
    chartLocalMeasure_compact_lt_top (I := I) g α hsupp_compact hf_support
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖f x‖ ≤ C := by
    have hCpt := (isCompact_univ (X := M)).image hf_cont.norm
    obtain ⟨C, hCmem⟩ := hCpt.bddAbove
    exact ⟨C, fun x => hCmem ⟨x, Set.mem_univ _, rfl⟩⟩
  have hbnd : ∀ᵐ x ∂(chartLocalMeasure (I := I) g α),
      ENNReal.ofReal ‖f x‖ ≤
        ENNReal.ofReal C * (tsupport f).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · rw [Set.indicator_of_mem hx, mul_one]
      exact ENNReal.ofReal_le_ofReal (hC x)
    · rw [Set.indicator_of_notMem hx, _root_.MulZeroClass.mul_zero]
      have hfx_zero : f x = 0 := by
        by_contra hne
        exact hx (subset_tsupport _ hne)
      rw [hfx_zero]; simp
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
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integrable_of_compactSupport_subset_chartSource
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.integrable_of_compactSupport_subset_chartSource target :: scope.openDecls } }

lemma integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α₀ : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_support : tsupport f ⊆ (chartAt H α₀).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, f x ∂(chartLocalMeasure (I := I) g α₀) := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (_root_.Set.univ : Set M) := chartAtlasPOU I M with hρ_def
  set S : Finset M := chartAtlasPOUFinset (I := I) (M := M) with hS_def
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) :=
    chartAtlasPOU_isSubordinate I M
  have h_step1 : ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ S, ∫ x, f x * ρ α x ∂(chartLocalMeasure (I := I) g α) := by
    have hKey :=
      chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
        (I := I) (M := M) (g_fam := fun _ : ℝ => g) (t := 0)
        (h := f) hf_cont
    simp only [riemannianMeasureFamily_def] at hKey
    exact hKey.symm
  rw [h_step1]
  have h_step2 : ∀ α ∈ S,
      ∫ x, f x * ρ α x ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, f x * ρ α x ∂(chartLocalMeasure (I := I) g α₀) := by
    intro α _
    refine chartLocalMeasure_integral_eq_of_support_in_overlap (I := I) g α α₀
      (fun x => f x * ρ α x) ?_
    intro x hx
    by_cases hxα : x ∈ (chartAt H α).source
    · have hxα₀ : x ∉ (chartAt H α₀).source := fun hxα₀' => hx ⟨hxα, hxα₀'⟩
      have hxnotin : x ∉ tsupport f := fun h => hxα₀ (hf_support h)
      have hfx_zero : f x = 0 := by
        by_contra hne
        exact hxnotin (subset_tsupport _ hne)
      rw [hfx_zero, _root_.MulZeroClass.zero_mul]
    · have hxnotin : x ∉ tsupport (ρ α : M → ℝ) := fun h => hxα (hρsub α h)
      have hρα_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne
        exact hxnotin (subset_tsupport _ hne)
      rw [hρα_zero, _root_.MulZeroClass.mul_zero]
  rw [Finset.sum_congr rfl h_step2]
  have h_each_int : ∀ α ∈ S, _root_.MeasureTheory.Integrable (fun x : M => f x * ρ α x)
      (chartLocalMeasure (I := I) g α₀) := by
    intro α _
    have hcont : Continuous (fun x : M => f x * ρ α x) :=
      hf_cont.mul (ρ α).contMDiff.continuous
    have hsupp_sub : tsupport (fun x : M => f x * ρ α x) ⊆ tsupport f := by
      refine closure_minimal ?_ (isClosed_tsupport _)
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hne
      have hfx : f x = 0 := by
        by_contra hne'
        exact hne (subset_tsupport _ hne')
      exact hx (by rw [hfx, _root_.MulZeroClass.zero_mul])
    exact integrable_of_compactSupport_subset_chartSource (I := I) g α₀
      hcont (hsupp_sub.trans hf_support)
  rw [show (∑ α ∈ S, ∫ x, f x * ρ α x ∂(chartLocalMeasure (I := I) g α₀))
      = ∫ x, ∑ α ∈ S, f x * ρ α x ∂(chartLocalMeasure (I := I) g α₀) from
        (_root_.MeasureTheory.integral_finsetSum (μ := chartLocalMeasure (I := I) g α₀) S h_each_int).symm]
  refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only
  rw [← Finset.mul_sum]
  have hsum_one : ∑ α ∈ S, ρ α x = 1 := by
    have hfins : ρ.finsupport x ⊆ S := by
      intro α hα
      rw [chartAtlasPOU_finset_mem]
      rw [ρ.mem_finsupport, Function.mem_support] at hα
      exact ⟨x, hα⟩
    exact ρ.sum_finsupport' x (_root_.Set.mem_univ x) hfins
  rw [hsum_one, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart

theorem integral_divergence_eq_zero_of_compact
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, divergenceG (I := I) g X x ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (_root_.Set.univ : Set M) := chartAtlasPOU I M with hρ_def
  set S : Finset M := chartAtlasPOUFinset (I := I) (M := M) with hS_def
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) :=
    chartAtlasPOU_isSubordinate I M
  have hdiv_smooth : ContMDiff I 𝓘(ℝ) ∞ (divergenceG (I := I) g X) :=
    divergence_g_contMDiff (I := I) g X
  have hdiv_cont : Continuous (divergenceG (I := I) g X) := hdiv_smooth.continuous
  have hρα_compactSupport : ∀ α : M, HasCompactSupport (ρ α : M → ℝ) := fun α =>
    HasCompactSupport.of_compactSpace _
  have h_step_a : ∫ x, divergenceG (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ S, ∫ x, divergenceG (I := I) g X x * ρ α x
          ∂(chartLocalMeasure (I := I) g α) := by
    have hKey :=
      chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
        (I := I) (M := M) (g_fam := fun _ : ℝ => g) (t := 0)
        (h := divergenceG (I := I) g X) hdiv_cont
    simp only [riemannianMeasureFamily_def] at hKey
    exact hKey.symm
  rw [h_step_a]
  have h_step_b : ∀ α ∈ S,
      ∫ x, divergenceG (I := I) g X x * ρ α x ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, localDivergence (I := I) g α X x * ρ α x
          ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    by_cases hxα : x ∈ (chartAt H α).source
    · simp only [voss_weyl_divergence_formula (I := I) g α X hxα]
    · have hxnotin : x ∉ tsupport (ρ α : M → ℝ) := fun h => hxα (hρsub α h)
      have hρα_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne
        exact hxnotin (subset_tsupport _ hne)
      simp only [hρα_zero, _root_.MulZeroClass.mul_zero]
  rw [Finset.sum_congr rfl h_step_b]
  have h_step_c : ∀ α ∈ S,
      ∫ x, localDivergence (I := I) g α X x * ρ α x
          ∂(chartLocalMeasure (I := I) g α) =
        -∫ x, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
            ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    exact chart_local_ibp (I := I) g α X (ρ α).contMDiff (hρα_compactSupport α) (hρsub α)
  rw [Finset.sum_congr rfl h_step_c]
  rw [show (∑ α ∈ S, -∫ x, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
            ∂(chartLocalMeasure (I := I) g α))
      = -(∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
            ∂(chartLocalMeasure (I := I) g α)) from by
    rw [← Finset.sum_neg_distrib]]
  have hAct_smooth : ∀ α : M,
      ContMDiff I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X (ρ α : M → ℝ)) := fun α =>
    tangentSectionAction_contMDiff (I := I) X (ρ α).contMDiff
  have hAct_cont : ∀ α : M,
      Continuous (tangentSectionAction (I := I) X (ρ α : M → ℝ)) := fun α =>
    (hAct_smooth α).continuous
  have hAct_support : ∀ α : M,
      tsupport (tangentSectionAction (I := I) X (ρ α : M → ℝ)) ⊆ (chartAt H α).source := by
    intro α
    refine subset_trans ?_ (hρsub α)
    refine closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hne
    have h_open : IsOpen (tsupport (ρ α : M → ℝ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have hev : (ρ α : M → ℝ) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hne] with z hz
      by_contra hne'
      exact hz (subset_tsupport _ hne')
    have hmfderiv_zero : mfderiv I 𝓘(ℝ) (ρ α : M → ℝ) x = 0 := by
      rw [Filter.EventuallyEq.mfderiv_eq hev]
      rw [mfderiv_const]; rfl
    have hAct_zero : tangentSectionAction (I := I) X (ρ α : M → ℝ) x = 0 := by
      change mfderiv I 𝓘(ℝ) (ρ α : M → ℝ) x (X x) = 0
      rw [hmfderiv_zero]; rfl
    exact hx hAct_zero
  have h_step_d : ∀ α ∈ S,
      ∫ x, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
          ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro α _
    exact (integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart
      (I := I) g α (hAct_cont α) (hAct_support α)).symm
  rw [Finset.sum_congr rfl h_step_d]
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have h_each_int : ∀ α ∈ S, _root_.MeasureTheory.Integrable
      (fun x : M => tangentSectionAction (I := I) X (ρ α : M → ℝ) x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro α _
    obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖tangentSectionAction (I := I) X (ρ α : M → ℝ) x‖ ≤ C := by
      have hCpt := (isCompact_univ (X := M)).image (hAct_cont α).norm
      obtain ⟨C, hCmem⟩ := hCpt.bddAbove
      exact ⟨C, fun x => hCmem ⟨x, Set.mem_univ _, rfl⟩⟩
    exact (_root_.MeasureTheory.integrable_const C).mono' (hAct_cont α).aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  rw [show (∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      = ∫ x, ∑ α ∈ S, tangentSectionAction (I := I) X (ρ α : M → ℝ) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from
        (_root_.MeasureTheory.integral_finsetSum (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          S h_each_int).symm]
  have h_pt : ∀ x : M,
      ∑ α ∈ S, tangentSectionAction (I := I) X (ρ α : M → ℝ) x = 0 := by
    intro x
    have hMDiff_each : ∀ α ∈ S, MDifferentiableAt I 𝓘(ℝ) ((ρ α : M → ℝ)) x :=
      fun α _ => (ρ α).contMDiff.mdifferentiable (by simp) x
    have hcomm := tangentSectionAction_finset_sum (I := I) X S
      (fun α => ((ρ α : M → ℝ))) x hMDiff_each
    rw [← hcomm]
    have h_finset_eq_one : (fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y) =ᶠ[𝓝 x]
        (fun _ : M => (1 : ℝ)) := by
      filter_upwards [ρ.eventually_finsupport_subset x] with y hy
      have hyfins_sub_S : ρ.finsupport y ⊆ S := by
        intro α hα
        rw [chartAtlasPOU_finset_mem]
        rw [ρ.mem_finsupport, Function.mem_support] at hα
        exact ⟨y, hα⟩
      exact ρ.sum_finsupport' y (_root_.Set.mem_univ y) hyfins_sub_S
    unfold tangentSectionAction
    have h_fun_eq : (∑ α ∈ S, (ρ α : M → ℝ)) = fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y := by
      funext y
      rw [Finset.sum_apply]
    rw [h_fun_eq]
    rw [Filter.EventuallyEq.mfderiv_eq h_finset_eq_one, mfderiv_const]
    rfl
  rw [show (fun x : M => ∑ α ∈ S, tangentSectionAction (I := I) X (ρ α : M → ℝ) x)
      = (fun _ : M => (0 : ℝ)) from funext h_pt]
  rw [_root_.MeasureTheory.integral_zero, neg_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_compact ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_compact

end DivergenceTheorem
end Integral
end DifferentialGeometry
