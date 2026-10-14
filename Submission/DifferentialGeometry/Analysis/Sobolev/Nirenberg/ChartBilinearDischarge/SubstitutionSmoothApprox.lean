import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SubstitutionNonSmoothChartBilinear
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.SmoothRegularity
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Basic
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace SubstitutionDischargeSmoothApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTranslatedCutoffDiffQuot
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))


omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
theorem exists_chart_target_cutoff
    [I.Boundaryless]
    {α : M}
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {h : ℝ}
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ χ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧
      (∀ x ∈ Metric.cthickening |h| K_0, χ x = 1) ∧
      tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α := by
  classical
  have h_cthick_compact : IsCompact (Metric.cthickening |h| K_0) := by
    have h_bdd : Bornology.IsBounded (Metric.cthickening |h| K_0) :=
      hK_0_compact.isBounded.cthickening
    have h_closed : IsClosed (Metric.cthickening |h| K_0) :=
      Metric.isClosed_cthickening
    exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨h_closed, h_bdd⟩
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, χ, hδ_pos, _hδΩ, hχ_smooth, hχ_compact, hχ_range, hχ_one,
    hχ_support⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) h_cthick_compact h_open h_thick
  refine ⟨χ, hχ_smooth, hχ_compact, ?_, ?_, ?_, hχ_support⟩
  · intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    have h_in_Icc : χ x ∈ Set.Icc (0 : ℝ) 1 := hχ_range hx_range
    exact h_in_Icc.1
  · intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    have h_in_Icc : χ x ∈ Set.Icc (0 : ℝ) 1 := hχ_range hx_range
    exact h_in_Icc.2
  · intro x hx
    apply hχ_one
    exact Metric.self_subset_cthickening _ hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.exists_chart_target_cutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.exists_chart_target_cutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.exists_chart_target_cutoff ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.exists_chart_target_cutoff

omit [NeZero (Module.finrank ℝ E)] in
lemma cutoff_uChart_memLp_two_univ
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_support_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (fun x => χ x * D.uChart x) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  have hχ_abs_cont : Continuous (fun x => |χ x|) := hχ_cont.abs
  obtain ⟨M_χ, hM_χ_nn, hM_χ_bd⟩ : ∃ M_χ : ℝ, 0 ≤ M_χ ∧ ∀ x, |χ x| ≤ M_χ := by
    by_cases hSupport_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, hxMax_in, hxMax_max⟩ :=
        hχ_cs.exists_isMaxOn hSupport_empty hχ_abs_cont.continuousOn
      refine ⟨|χ xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact hxMax_max hx
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
        exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact absurd ⟨x, hx⟩ hSupport_empty
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
  have h_support_compact : IsCompact (tsupport χ) := hχ_cs
  have h_support_meas : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  have hu_l2_support : _root_.MeasureTheory.MemLp D.uChart 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.u_chart_memLp_weighted h_support_compact h_support_meas hχ_support_in
  have h_u_aesm_restrict : _root_.MeasureTheory.AEStronglyMeasurable D.uChart
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hu_l2_support.aestronglyMeasurable
  have h_pt_le : ∀ᵐ x ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)),
      ‖χ x * D.uChart x‖ ≤ ‖M_χ * D.uChart x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hM_χ_nn]
    exact mul_le_mul_of_nonneg_right (hM_χ_bd x) (abs_nonneg _)
  have h_prod_aesm_restrict : _root_.MeasureTheory.AEStronglyMeasurable (fun x => χ x * D.uChart x)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hχ_cont.aestronglyMeasurable.restrict.mul h_u_aesm_restrict
  have h_restrict_lp : _root_.MeasureTheory.MemLp (fun x => χ x * D.uChart x) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    MemLp.mono (hu_l2_support.const_mul M_χ) h_prod_aesm_restrict h_pt_le
  have h_indicator_eq : (tsupport χ).indicator (fun x => χ x * D.uChart x) =
      (fun x => χ x * D.uChart x) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hχx, _root_.MulZeroClass.zero_mul]
  have h_indicator_lp :
      _root_.MeasureTheory.MemLp ((tsupport χ).indicator (fun x => χ x * D.uChart x)) 2
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    (MeasureTheory.memLp_indicator_iff_restrict h_support_meas).mpr h_restrict_lp
  rw [h_indicator_eq] at h_indicator_lp
  exact h_indicator_lp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_memLp_two_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_memLp_two_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_memLp_two_univ ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_memLp_two_univ

omit [NeZero (Module.finrank ℝ E)] in
lemma cutoff_uChart_partial_memLp_two_univ
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_support_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (i : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.MemLp (fun x =>
        (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
        χ x * D.weakPartial i x) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  have hχ_partial_cont : Continuous
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1)) :=
    (hχ_smooth.continuous_fderiv h_top_ne_zero).clm_apply continuous_const
  have h_support_compact : IsCompact (tsupport χ) := hχ_cs
  have h_support_meas : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  have hχ_abs_cont : Continuous (fun x => |χ x|) := hχ_cont.abs
  obtain ⟨M_χ, hM_χ_nn, hM_χ_bd⟩ : ∃ M_χ : ℝ, 0 ≤ M_χ ∧ ∀ x, |χ x| ≤ M_χ := by
    by_cases hSupport_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        hχ_cs.exists_isMaxOn hSupport_empty hχ_abs_cont.continuousOn
      refine ⟨|χ xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact hxMax_max hx
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
        exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact absurd ⟨x, hx⟩ hSupport_empty
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
  have h_partial_χ_support : HasCompactSupport
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1)) :=
    hχ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have h_partial_χ_support_subset : tsupport
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1)) ⊆ tsupport χ :=
    tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)
  obtain ⟨M_dχ, hM_dχ_nn, hM_dχ_bd⟩ : ∃ M_dχ : ℝ, 0 ≤ M_dχ ∧
      ∀ x, |(fderiv ℝ χ x) (EuclideanSpace.single i 1)| ≤ M_dχ := by
    by_cases hSupport_empty :
        (tsupport (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1))).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        h_partial_χ_support.exists_isMaxOn hSupport_empty
          (hχ_partial_cont.abs.continuousOn)
      refine ⟨|(fderiv ℝ χ xMax) (EuclideanSpace.single i 1)|,
        abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport
          (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1))
      · exact hxMax_max hx
      · have hdχx :
            (fun y : EuclN => (fderiv ℝ χ y) (EuclideanSpace.single i 1)) x = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y : EuclN => (fderiv ℝ χ y) (EuclideanSpace.single i 1))
            hx
        rw [show (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0 from hdχx,
          abs_zero]
        exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport
          (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1))
      · exact absurd ⟨x, hx⟩ hSupport_empty
      · have hdχx :
            (fun y : EuclN => (fderiv ℝ χ y) (EuclideanSpace.single i 1)) x = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y : EuclN => (fderiv ℝ χ y) (EuclideanSpace.single i 1))
            hx
        rw [show (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0 from hdχx,
          abs_zero]
  have hu_l2_support : _root_.MeasureTheory.MemLp D.uChart 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.u_chart_memLp_weighted h_support_compact h_support_meas hχ_support_in
  have hwp_l2_support : _root_.MeasureTheory.MemLp (D.weakPartial i) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    D.weak_partial_locally_memLp i (tsupport χ) h_support_compact hχ_support_in
  have h_dχ_aesm_restrict : _root_.MeasureTheory.AEStronglyMeasurable
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1))
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hχ_partial_cont.aestronglyMeasurable.restrict
  have h_χ_aesm_restrict : _root_.MeasureTheory.AEStronglyMeasurable χ
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hχ_cont.aestronglyMeasurable.restrict
  have h_term1_aesm_restrict : _root_.MeasureTheory.AEStronglyMeasurable
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    h_dχ_aesm_restrict.mul hu_l2_support.aestronglyMeasurable
  have h_term2_aesm_restrict : _root_.MeasureTheory.AEStronglyMeasurable
      (fun x => χ x * D.weakPartial i x)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    h_χ_aesm_restrict.mul hwp_l2_support.aestronglyMeasurable
  have h_pt_le_1 : ∀ᵐ x ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)),
      ‖(fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x‖ ≤
        ‖M_dχ * D.uChart x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hM_dχ_nn]
    exact mul_le_mul_of_nonneg_right (hM_dχ_bd x) (abs_nonneg _)
  have h_term1_lp : _root_.MeasureTheory.MemLp
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    MemLp.mono (hu_l2_support.const_mul M_dχ) h_term1_aesm_restrict h_pt_le_1
  have h_pt_le_2 : ∀ᵐ x ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)),
      ‖χ x * D.weakPartial i x‖ ≤ ‖M_χ * D.weakPartial i x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hM_χ_nn]
    exact mul_le_mul_of_nonneg_right (hM_χ_bd x) (abs_nonneg _)
  have h_term2_lp : _root_.MeasureTheory.MemLp
      (fun x => χ x * D.weakPartial i x) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    MemLp.mono (hwp_l2_support.const_mul M_χ) h_term2_aesm_restrict h_pt_le_2
  have h_sum_lp : _root_.MeasureTheory.MemLp (fun x =>
      (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
      χ x * D.weakPartial i x) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    h_term1_lp.add h_term2_lp
  have h_indicator_eq : (tsupport χ).indicator
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
        χ x * D.weakPartial i x) =
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
        χ x * D.weakPartial i x) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hx_notin :
          x ∉ tsupport (fun y : EuclN =>
            (fderiv ℝ χ y) (EuclideanSpace.single i 1)) :=
        fun h => hx (h_partial_χ_support_subset h)
      have hdχx :
          (fun y : EuclN => (fderiv ℝ χ y) (EuclideanSpace.single i 1)) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun y : EuclN => (fderiv ℝ χ y) (EuclideanSpace.single i 1))
          hx_notin
      rw [hχx,
        show (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0 from hdχx,
        _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.zero_mul, add_zero]
  have h_indicator_lp :
      _root_.MeasureTheory.MemLp ((tsupport χ).indicator (fun x =>
          (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
          χ x * D.weakPartial i x)) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    (MeasureTheory.memLp_indicator_iff_restrict h_support_meas).mpr h_sum_lp
  rw [h_indicator_eq] at h_indicator_lp
  exact h_indicator_lp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_partial_memLp_two_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_partial_memLp_two_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_partial_memLp_two_univ ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_partial_memLp_two_univ

omit [NeZero (Module.finrank ℝ E)] in
lemma cutoff_uChart_hasWeakPartialDeriv_univ
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_support_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
        χ x * D.weakPartial i x)
      (fun x => χ x * D.uChart x) Set.univ := by
  classical
  intro ψ hψ_smooth hψ_support _hψ_sub
  set ei : EuclN := EuclideanSpace.single i (1 : ℝ) with hei_def
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_chart_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    h_chart_open.measurableSet
  have hχψ_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * ψ x) :=
    hχ_smooth.mul hψ_smooth
  have hχψ_cs : HasCompactSupport (fun x => χ x * ψ x) :=
    hχ_cs.mul_right
  have hχψ_support_in_χ : tsupport (fun x => χ x * ψ x) ⊆ tsupport χ :=
    tsupport_smul_subset_left χ ψ
  have hχψ_support : tsupport (fun x => χ x * ψ x) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    hχψ_support_in_χ.trans hχ_support_in
  have h_ibp_chart :=
    D.weak_partial_isWeakPartial i (fun y => χ y * ψ y)
      hχψ_smooth hχψ_cs hχψ_support
  have hχ_diff : Differentiable ℝ χ := hχ_smooth.differentiable (by simp)
  have hψ_diff : Differentiable ℝ ψ := hψ_smooth.differentiable (by simp)
  have h_fderiv_prod : ∀ x : EuclN,
      (fderiv ℝ (fun y => χ y * ψ y) x) ei =
        χ x * (fderiv ℝ ψ x) ei + ψ x * (fderiv ℝ χ x) ei := by
    intro x
    rw [fderiv_fun_mul (hχ_diff.differentiableAt) (hψ_diff.differentiableAt)]
    simp [add_apply, smul_apply,
      smul_eq_mul]
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  have hψ_cont : Continuous ψ := hψ_smooth.continuous
  have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  have h_dχ_cont : Continuous (fun y : EuclN => (fderiv ℝ χ y) ei) :=
    (hχ_smooth.continuous_fderiv h_top_ne_zero).clm_apply continuous_const
  have h_dψ_cont : Continuous (fun y : EuclN => (fderiv ℝ ψ y) ei) :=
    (hψ_smooth.continuous_fderiv h_top_ne_zero).clm_apply continuous_const
  set G : EuclN → ℝ := fun x =>
    (fderiv ℝ χ x) ei * D.uChart x + χ x * D.weakPartial i x with hG_def
  have h_LHS_eq :
      ∫ x in (Set.univ : Set EuclN), χ x * D.uChart x * (fderiv ℝ ψ x) ei =
      ∫ x in chartTargetEuclid (I := I) (M := M) α,
        χ x * D.uChart x * (fderiv ℝ ψ x) ei := by
    rw [_root_.MeasureTheory.setIntegral_univ]
    refine (_root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := chartTargetEuclid (I := I) (M := M) α)
      (f := fun x => χ x * D.uChart x * (fderiv ℝ ψ x) ei)
      (fun x hx => ?_)).symm
    have hx_notin_χ : x ∉ tsupport χ := fun h => hx (hχ_support_in h)
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx_notin_χ
    change χ x * D.uChart x * (fderiv ℝ ψ x) ei = 0
    simp [hχx]
  have h_RHS_eq :
      ∫ x in (Set.univ : Set EuclN), G x * ψ x =
      ∫ x in chartTargetEuclid (I := I) (M := M) α, G x * ψ x := by
    rw [_root_.MeasureTheory.setIntegral_univ]
    refine (_root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := chartTargetEuclid (I := I) (M := M) α)
      (f := fun x => G x * ψ x) (fun x hx => ?_)).symm
    have hx_notin_χ : x ∉ tsupport χ := fun h => hx (hχ_support_in h)
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx_notin_χ
    have h_partial_χ_support_subset :
        tsupport (fun y : EuclN => (fderiv ℝ χ y) ei) ⊆ tsupport χ := by
      rw [hei_def]
      exact tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)
    have hx_notin_dχ : x ∉ tsupport (fun y : EuclN => (fderiv ℝ χ y) ei) :=
      fun h => hx_notin_χ (h_partial_χ_support_subset h)
    have hdχx :
        (fun y : EuclN => (fderiv ℝ χ y) ei) x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : EuclN => (fderiv ℝ χ y) ei) hx_notin_dχ
    have hdχx' : (fderiv ℝ χ x) ei = 0 := hdχx
    simp [hG_def, hχx, hdχx']
  change ∫ x in (Set.univ : Set EuclN), χ x * D.uChart x * (fderiv ℝ ψ x) ei =
      -∫ x in (Set.univ : Set EuclN), G x * ψ x
  rw [h_LHS_eq, h_RHS_eq]
  have h_support_compact : IsCompact (tsupport χ) := hχ_cs
  have h_support_meas : MeasurableSet (tsupport χ) :=
    (isClosed_tsupport χ).measurableSet
  have hu_l2_support : _root_.MeasureTheory.MemLp D.uChart 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.u_chart_memLp_weighted h_support_compact h_support_meas hχ_support_in
  have hwp_l2_support : _root_.MeasureTheory.MemLp (D.weakPartial i) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    D.weak_partial_locally_memLp i (tsupport χ) h_support_compact hχ_support_in
  have h_finite_meas_fact :
      Fact ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) (tsupport χ) < (⊤ : ℝ≥0∞)) :=
    Fact.mk h_support_compact.measure_lt_top
  have h_restrict_finite : _root_.MeasureTheory.IsFiniteMeasure
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    Restrict.isFiniteMeasure (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)
  have hu_l1_support : _root_.MeasureTheory.Integrable D.uChart
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hu_l2_support.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hwp_l1_support : _root_.MeasureTheory.Integrable (D.weakPartial i)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hwp_l2_support.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_χ_aesm_support : _root_.MeasureTheory.AEStronglyMeasurable χ
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hχ_cont.aestronglyMeasurable.restrict
  have hψ_aesm_support : _root_.MeasureTheory.AEStronglyMeasurable ψ
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hψ_cont.aestronglyMeasurable.restrict
  have h_dχ_aesm_support : _root_.MeasureTheory.AEStronglyMeasurable (fun x : EuclN => (fderiv ℝ χ x) ei)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    h_dχ_cont.aestronglyMeasurable.restrict
  have h_dψ_aesm_support : _root_.MeasureTheory.AEStronglyMeasurable (fun x : EuclN => (fderiv ℝ ψ x) ei)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    h_dψ_cont.aestronglyMeasurable.restrict
  obtain ⟨M_χ, hM_χ_nn, hM_χ_bd⟩ : ∃ M_χ : ℝ, 0 ≤ M_χ ∧ ∀ x, |χ x| ≤ M_χ := by
    by_cases hSupport_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        h_support_compact.exists_isMaxOn hSupport_empty hχ_cont.abs.continuousOn
      refine ⟨|χ xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact hxMax_max hx
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]; exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact absurd ⟨x, hx⟩ hSupport_empty
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
  obtain ⟨M_ψ, hM_ψ_nn, hM_ψ_bd⟩ : ∃ M_ψ : ℝ, 0 ≤ M_ψ ∧
      ∀ x ∈ tsupport χ, |ψ x| ≤ M_ψ := by
    by_cases hSupport_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, hxMax_in, hxMax_max⟩ :=
        h_support_compact.exists_isMaxOn hSupport_empty hψ_cont.abs.continuousOn
      refine ⟨|ψ xMax|, abs_nonneg _, ?_⟩
      intro x hx
      exact hxMax_max hx
    · refine ⟨0, le_refl _, ?_⟩
      intro x hx
      exact absurd ⟨x, hx⟩ hSupport_empty
  obtain ⟨M_dψ, hM_dψ_nn, hM_dψ_bd⟩ : ∃ M_dψ : ℝ, 0 ≤ M_dψ ∧
      ∀ x ∈ tsupport χ, |(fderiv ℝ ψ x) ei| ≤ M_dψ := by
    by_cases hSupport_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, hxMax_in, hxMax_max⟩ :=
        h_support_compact.exists_isMaxOn hSupport_empty h_dψ_cont.abs.continuousOn
      refine ⟨|(fderiv ℝ ψ xMax) ei|, abs_nonneg _, ?_⟩
      intro x hx
      exact hxMax_max hx
    · refine ⟨0, le_refl _, ?_⟩
      intro x hx
      exact absurd ⟨x, hx⟩ hSupport_empty
  obtain ⟨M_dχ, hM_dχ_nn, hM_dχ_bd⟩ : ∃ M_dχ : ℝ, 0 ≤ M_dχ ∧
      ∀ x ∈ tsupport χ, |(fderiv ℝ χ x) ei| ≤ M_dχ := by
    by_cases hSupport_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, hxMax_in, hxMax_max⟩ :=
        h_support_compact.exists_isMaxOn hSupport_empty h_dχ_cont.abs.continuousOn
      refine ⟨|(fderiv ℝ χ xMax) ei|, abs_nonneg _, ?_⟩
      intro x hx
      exact hxMax_max hx
    · refine ⟨0, le_refl _, ?_⟩
      intro x hx
      exact absurd ⟨x, hx⟩ hSupport_empty
  have h_χ_dψ_bdd : ∀ᵐ x ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)),
      ‖χ x * (fderiv ℝ ψ x) ei‖ ≤ M_χ * M_dψ := by
    rw [_root_.MeasureTheory.ae_restrict_iff' h_support_meas]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hM_χ_bd x) (hM_dψ_bd x hx) (abs_nonneg _) hM_χ_nn
  have h_ψ_dχ_bdd : ∀ᵐ x ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)),
      ‖ψ x * (fderiv ℝ χ x) ei‖ ≤ M_ψ * M_dχ := by
    rw [_root_.MeasureTheory.ae_restrict_iff' h_support_meas]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hM_ψ_bd x hx) (hM_dχ_bd x hx) (abs_nonneg _) hM_ψ_nn
  have h_χ_ψ_bdd : ∀ᵐ x ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)),
      ‖χ x * ψ x‖ ≤ M_χ * M_ψ := by
    rw [_root_.MeasureTheory.ae_restrict_iff' h_support_meas]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hM_χ_bd x) (hM_ψ_bd x hx) (abs_nonneg _) hM_χ_nn
  have h_χ_dψ_aesm : _root_.MeasureTheory.AEStronglyMeasurable
      (fun x : EuclN => χ x * (fderiv ℝ ψ x) ei)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    h_χ_aesm_support.mul h_dψ_aesm_support
  have h_term1_int : _root_.MeasureTheory.Integrable
      (fun x => D.uChart x * (χ x * (fderiv ℝ ψ x) ei))
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hu_l1_support.mul_bdd h_χ_dψ_aesm h_χ_dψ_bdd
  have h_χ_ψ_aesm : _root_.MeasureTheory.AEStronglyMeasurable
      (fun x : EuclN => χ x * ψ x)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    h_χ_aesm_support.mul hψ_aesm_support
  have h_term2_int : _root_.MeasureTheory.Integrable
      (fun x => D.weakPartial i x * (χ x * ψ x))
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hwp_l1_support.mul_bdd h_χ_ψ_aesm h_χ_ψ_bdd
  have h_ψ_dχ_aesm : _root_.MeasureTheory.AEStronglyMeasurable
      (fun x : EuclN => ψ x * (fderiv ℝ χ x) ei)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hψ_aesm_support.mul h_dχ_aesm_support
  have h_term3_int : _root_.MeasureTheory.Integrable
      (fun x => D.uChart x * (ψ x * (fderiv ℝ χ x) ei))
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hu_l1_support.mul_bdd h_ψ_dχ_aesm h_ψ_dχ_bdd
  have h_integrand_LHS_zero_outside :
      ∀ x, x ∉ tsupport χ → χ x * D.uChart x * (fderiv ℝ ψ x) ei = 0 := by
    intro x hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hχx, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.zero_mul]
  have h_integrand_term1_zero_outside :
      ∀ x, x ∉ tsupport χ → D.uChart x * (χ x * (fderiv ℝ ψ x) ei) = 0 := by
    intro x hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hχx, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.mul_zero]
  have h_integrand_term3_zero_outside :
      ∀ x, x ∉ tsupport χ → D.uChart x * (ψ x * (fderiv ℝ χ x) ei) = 0 := by
    intro x hx
    have h_partial_χ_support_subset :
        tsupport (fun y : EuclN => (fderiv ℝ χ y) ei) ⊆ tsupport χ := by
      rw [hei_def]
      exact tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)
    have hx_notin_dχ : x ∉ tsupport (fun y : EuclN => (fderiv ℝ χ y) ei) :=
      fun h => hx (h_partial_χ_support_subset h)
    have hdχx :
        (fun y : EuclN => (fderiv ℝ χ y) ei) x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : EuclN => (fderiv ℝ χ y) ei) hx_notin_dχ
    have hdχx' : (fderiv ℝ χ x) ei = 0 := hdχx
    rw [hdχx', _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero]
  have h_integrand_term2_zero_outside :
      ∀ x, x ∉ tsupport χ → D.weakPartial i x * (χ x * ψ x) = 0 := by
    intro x hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hχx, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.mul_zero]
  have h_integrand_RHS_zero_outside :
      ∀ x, x ∉ tsupport χ → G x * ψ x = 0 := by
    intro x hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h_partial_χ_support_subset :
        tsupport (fun y : EuclN => (fderiv ℝ χ y) ei) ⊆ tsupport χ := by
      rw [hei_def]
      exact tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)
    have hx_notin_dχ : x ∉ tsupport (fun y : EuclN => (fderiv ℝ χ y) ei) :=
      fun h => hx (h_partial_χ_support_subset h)
    have hdχx :
        (fun y : EuclN => (fderiv ℝ χ y) ei) x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : EuclN => (fderiv ℝ χ y) ei) hx_notin_dχ
    have hdχx' : (fderiv ℝ χ x) ei = 0 := hdχx
    rw [hG_def]
    simp [hχx, hdχx']
  have h_LHS_chart_to_support :
      ∫ x in chartTargetEuclid (I := I) (M := M) α,
        χ x * D.uChart x * (fderiv ℝ ψ x) ei =
      ∫ x in tsupport χ, χ x * D.uChart x * (fderiv ℝ ψ x) ei :=
    _root_.MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      h_chart_open.measurableSet hχ_support_in
      (fun x hx => h_integrand_LHS_zero_outside x hx.2)
  have h_RHS_chart_to_support :
      ∫ x in chartTargetEuclid (I := I) (M := M) α, G x * ψ x =
      ∫ x in tsupport χ, G x * ψ x :=
    _root_.MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      h_chart_open.measurableSet hχ_support_in
      (fun x hx => h_integrand_RHS_zero_outside x hx.2)
  have h_term1_chart_to_support :
      ∫ x in chartTargetEuclid (I := I) (M := M) α,
        D.uChart x * (χ x * (fderiv ℝ ψ x) ei) =
      ∫ x in tsupport χ, D.uChart x * (χ x * (fderiv ℝ ψ x) ei) :=
    _root_.MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      h_chart_open.measurableSet hχ_support_in
      (fun x hx => h_integrand_term1_zero_outside x hx.2)
  have h_term3_chart_to_support :
      ∫ x in chartTargetEuclid (I := I) (M := M) α,
        D.uChart x * (ψ x * (fderiv ℝ χ x) ei) =
      ∫ x in tsupport χ, D.uChart x * (ψ x * (fderiv ℝ χ x) ei) :=
    _root_.MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      h_chart_open.measurableSet hχ_support_in
      (fun x hx => h_integrand_term3_zero_outside x hx.2)
  have h_term2_chart_to_support :
      ∫ x in chartTargetEuclid (I := I) (M := M) α,
        D.weakPartial i x * (χ x * ψ x) =
      ∫ x in tsupport χ, D.weakPartial i x * (χ x * ψ x) :=
    _root_.MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      h_chart_open.measurableSet hχ_support_in
      (fun x hx => h_integrand_term2_zero_outside x hx.2)
  have h_ibp_chart_LHS_split :
      ∫ x in tsupport χ,
        D.uChart x * (fderiv ℝ (fun y => χ y * ψ y) x) ei =
      (∫ x in tsupport χ, D.uChart x * (χ x * (fderiv ℝ ψ x) ei)) +
      ∫ x in tsupport χ, D.uChart x * (ψ x * (fderiv ℝ χ x) ei) := by
    rw [← MeasureTheory.integral_add h_term1_int h_term3_int]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    have h_pt := h_fderiv_prod x
    calc D.uChart x * (fderiv ℝ (fun y => χ y * ψ y) x) ei
        = D.uChart x * (χ x * (fderiv ℝ ψ x) ei + ψ x * (fderiv ℝ χ x) ei) := by
          rw [h_pt]
      _ = D.uChart x * (χ x * (fderiv ℝ ψ x) ei) +
          D.uChart x * (ψ x * (fderiv ℝ χ x) ei) := by ring
  have h_ibp_chart_LHS_chart_to_support :
      ∫ x in chartTargetEuclid (I := I) (M := M) α,
        D.uChart x * (fderiv ℝ (fun y => χ y * ψ y) x) ei =
      ∫ x in tsupport χ,
        D.uChart x * (fderiv ℝ (fun y => χ y * ψ y) x) ei := by
    refine _root_.MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      h_chart_open.measurableSet hχ_support_in (fun x hx => ?_)
    have hx_notin_χψ : x ∉ tsupport (fun y => χ y * ψ y) :=
      fun h => hx.2 (hχψ_support_in_χ h)
    have hχψ_partial_support :
        tsupport (fun y : EuclN => (fderiv ℝ (fun z => χ z * ψ z) y) ei) ⊆
          tsupport χ :=
      (tsupport_fderiv_apply_subset ℝ ei).trans hχψ_support_in_χ
    have hx_notin :
        x ∉ tsupport (fun y : EuclN => (fderiv ℝ (fun z => χ z * ψ z) y) ei) :=
      fun h => hx.2 (hχψ_partial_support h)
    have hdχψx :
        (fun y : EuclN => (fderiv ℝ (fun z => χ z * ψ z) y) ei) x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : EuclN => (fderiv ℝ (fun z => χ z * ψ z) y) ei) hx_notin
    have hdχψx' : (fderiv ℝ (fun z => χ z * ψ z) x) ei = 0 := hdχψx
    rw [hdχψx', _root_.MulZeroClass.mul_zero]
  rw [h_ibp_chart_LHS_chart_to_support, h_term2_chart_to_support] at h_ibp_chart
  rw [h_ibp_chart_LHS_split] at h_ibp_chart
  rw [h_LHS_chart_to_support, h_RHS_chart_to_support]
  have h_LHS_pt :
      ∫ x in tsupport χ, χ x * D.uChart x * (fderiv ℝ ψ x) ei =
      ∫ x in tsupport χ, D.uChart x * (χ x * (fderiv ℝ ψ x) ei) := by
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x; ring
  have h_RHS_split :
      ∫ x in tsupport χ, G x * ψ x =
      (∫ x in tsupport χ, D.uChart x * (ψ x * (fderiv ℝ χ x) ei)) +
      ∫ x in tsupport χ, D.weakPartial i x * (χ x * ψ x) := by
    rw [← MeasureTheory.integral_add h_term3_int h_term2_int]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [hG_def]; ring
  rw [h_LHS_pt, h_RHS_split]
  linarith [h_ibp_chart]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_hasWeakPartialDeriv_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_hasWeakPartialDeriv_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_hasWeakPartialDeriv_univ ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_hasWeakPartialDeriv_univ

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_weak_partials_cutoff_uChart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_support_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ G : Fin (Module.finrank ℝ E) → EuclN → ℝ,
      (∀ i, _root_.MeasureTheory.MemLp (G i) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) ∧
      (∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i (G i)
        (fun x => χ x * D.uChart x) Set.univ) ∧
      MemLp (fun x => χ x * D.uChart x) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  refine ⟨fun i x =>
    (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
    χ x * D.weakPartial i x, ?_, ?_, ?_⟩
  · intro i
    exact cutoff_uChart_partial_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_support_in i
  · intro i
    exact cutoff_uChart_hasWeakPartialDeriv_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_support_in i
  · exact cutoff_uChart_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_support_in

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.exists_weak_partials_cutoff_uChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.exists_weak_partials_cutoff_uChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.exists_weak_partials_cutoff_uChart ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.exists_weak_partials_cutoff_uChart

private noncomputable def cutoff_uChart_witness
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_support_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    DeGiorgi.MemW1pWitness (d := Module.finrank ℝ E) (ENNReal.ofReal 2)
      (fun x => χ x * D.uChart x) Set.univ where
  memLp := by
    have h_lp := cutoff_uChart_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_support_in
    rw [Measure.restrict_univ]
    have h_two_eq : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
    rw [h_two_eq]
    exact h_lp
  weakGrad := fun x =>
    WithLp.toLp 2 fun i =>
      (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
      χ x * D.weakPartial i x
  weakGrad_component_memLp := by
    intro i
    have h_lp := cutoff_uChart_partial_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_support_in i
    rw [Measure.restrict_univ]
    have h_eq :
        (fun x =>
          (WithLp.toLp 2 fun j =>
            (fderiv ℝ χ x) (EuclideanSpace.single j 1) * D.uChart x +
            χ x * D.weakPartial j x) i) =
        (fun x =>
          (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
          χ x * D.weakPartial i x) := by
      funext x
      simp
    rw [h_eq]
    have h_two_eq : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
    rw [h_two_eq]
    exact h_lp
  isWeakGrad := by
    intro i
    have h_eq :
        (fun x =>
          (WithLp.toLp 2 fun j =>
            (fderiv ℝ χ x) (EuclideanSpace.single j 1) * D.uChart x +
            χ x * D.weakPartial j x) i) =
        (fun x =>
          (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
          χ x * D.weakPartial i x) := by
      funext x
      simp
    rw [h_eq]
    exact cutoff_uChart_hasWeakPartialDeriv_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_support_in i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_witness
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.cutoff_uChart_witness target :: scope.openDecls } }

theorem exists_smooth_uChart_approx
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_support_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ uSeq : ℕ → EuclN → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (uSeq n)) ∧
      (∀ n, HasCompactSupport (uSeq n)) ∧
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm
        (fun x => uSeq n x - χ x * D.uChart x) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
        _root_.Filter.atTop (𝓝 0) ∧
      ∀ i : Fin (Module.finrank ℝ E),
        _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm
          (fun x => (fderiv ℝ (uSeq n) x) (EuclideanSpace.single i 1) -
            ((fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
             χ x * D.weakPartial i x)) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
          atTop (𝓝 0) := by
  classical
  let hw :=
    cutoff_uChart_witness (I := I) (M := M) D hχ_smooth hχ_cs hχ_support_in
  have h_χu_cs : HasCompactSupport (fun x => χ x * D.uChart x) := by
    refine HasCompactSupport.intro' (K := tsupport χ)
      hχ_cs (isClosed_tsupport χ) ?_
    intro x hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hχx, _root_.MulZeroClass.zero_mul]
  have hp : (1 : ℝ) < 2 := by norm_num
  obtain ⟨uSeq, hu_smooth, hu_cs, _hu_support_thicken, hu_tendsto, hu_grad_tendsto⟩ :=
    DeGiorgi.exists_smooth_compactSupport_W1p_approx_univ
      (d := Module.finrank ℝ E) hp hw h_χu_cs
  refine ⟨uSeq, hu_smooth, hu_cs, ?_, ?_⟩
  · have h_two_eq : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
    have h_eq_tendsto :
        (fun n => _root_.MeasureTheory.eLpNorm (fun x => uSeq n x - χ x * D.uChart x) 2
          (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (fun n => _root_.MeasureTheory.eLpNorm (fun x => uSeq n x - χ x * D.uChart x)
          (ENNReal.ofReal 2) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by
      funext n
      rw [h_two_eq]
    rw [h_eq_tendsto]
    exact hu_tendsto
  · intro i
    have h_two_eq : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
    have h_eq_tendsto :
        (fun n => _root_.MeasureTheory.eLpNorm
          (fun x => (fderiv ℝ (uSeq n) x) (EuclideanSpace.single i 1) -
            ((fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
             χ x * D.weakPartial i x)) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (fun n => _root_.MeasureTheory.eLpNorm
          (fun x => (fderiv ℝ (uSeq n) x) (EuclideanSpace.single i 1) -
            hw.weakGrad x i) (ENNReal.ofReal 2) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by
      funext n
      have h_grad_pt : ∀ x : EuclN, hw.weakGrad x i =
          (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
          χ x * D.weakPartial i x := by
        intro x
        change (WithLp.toLp 2 fun j =>
            (fderiv ℝ χ x) (EuclideanSpace.single j 1) * D.uChart x +
            χ x * D.weakPartial j x) i = _
        simp
      have h_lhs_eq :
          (fun x => (fderiv ℝ (uSeq n) x) (EuclideanSpace.single i 1) -
            ((fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
             χ x * D.weakPartial i x)) =
          (fun x => (fderiv ℝ (uSeq n) x) (EuclideanSpace.single i 1) -
            hw.weakGrad x i) := by
        funext x
        rw [h_grad_pt x]
      conv_lhs => rw [h_lhs_eq]
      congr 1
      exact h_two_eq.symm
    rw [h_eq_tendsto]
    exact hu_grad_tendsto i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.exists_smooth_uChart_approx then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.exists_smooth_uChart_approx"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.exists_smooth_uChart_approx ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.exists_smooth_uChart_approx

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem nirenbergTestFunction_smooth_seq
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    {uSeq : ℕ → EuclN → ℝ}
    (hu_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (uSeq n))
    :
    ∀ n, ContDiff ℝ (⊤ : ℕ∞)
      (nirenbergTestFunction (d := Module.finrank ℝ E) k h η (uSeq n)) ∧
        HasCompactSupport
          (nirenbergTestFunction (d := Module.finrank ℝ E) k h η
            (uSeq n)) := by
  classical
  intro n
  refine ⟨?_, ?_⟩
  · exact contDiff_nirenbergTestFunction (d := Module.finrank ℝ E)
      hη (hu_seq_smooth n) k hh
  · exact hasCompactSupport_nirenbergTestFunction
      (d := Module.finrank ℝ E) hη_support k h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.nirenbergTestFunction_smooth_seq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.nirenbergTestFunction_smooth_seq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.nirenbergTestFunction_smooth_seq ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.nirenbergTestFunction_smooth_seq

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_translate_eq_local (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (F : EuclN → ℝ) :
    _root_.MeasureTheory.eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  set τ : EuclN ≃ₜ EuclN :=
    Homeomorph.addRight (h • EuclideanSpace.single k 1) with hτ_def
  have hMP : _root_.MeasureTheory.MeasurePreserving τ _root_.MeasureTheory.MeasureSpace.volume volume := by
    rw [show (τ : EuclN → EuclN) = fun x => x + h • EuclideanSpace.single k 1
      from rfl]
    exact _root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume _
  have hτ_emb : MeasurableEmbedding τ := τ.measurableEmbedding
  have h_eq :
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F = F ∘ (τ : EuclN → EuclN) := rfl
  rw [h_eq]
  rw [show _root_.MeasureTheory.eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      _root_.MeasureTheory.eLpNorm F 2 (Measure.map τ _root_.MeasureTheory.MeasureSpace.volume) from by rw [hMP.map_eq]]
  exact (hτ_emb.eLpNorm_map_measure (g := F) (p := 2)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.eLpNorm_translate_eq_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.eLpNorm_translate_eq_local target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_diffQuot_le_local
    (k : Fin (Module.finrank ℝ E)) {h : ℝ} (hh : h ≠ 0) {F : EuclN → ℝ}
    (hF_aesm : _root_.MeasureTheory.AEStronglyMeasurable F (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) :
    _root_.MeasureTheory.eLpNorm (DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * _root_.MeasureTheory.eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  have h_dq_eq : DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h F =
      fun x => h⁻¹ * (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F x - F x) := by
    funext x
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh F x]
    change (F (x + h • EuclideanSpace.single k 1) - F x) / h =
      h⁻¹ * (F (x + h • EuclideanSpace.single k 1) - F x)
    field_simp
  rw [h_dq_eq]
  have h_eq_pi : (fun x => h⁻¹ * (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F x - F x)) =
      h⁻¹ • (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F - F) := by
    funext x
    simp [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [h_eq_pi]
  rw [_root_.MeasureTheory.eLpNorm_const_smul h⁻¹]
  have hτF_aesm : _root_.MeasureTheory.AEStronglyMeasurable
      (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    have hMP : _root_.MeasureTheory.MeasurePreserving
        (fun x : EuclN => x + h • EuclideanSpace.single k 1) _root_.MeasureTheory.MeasureSpace.volume volume :=
      _root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume _
    exact hF_aesm.comp_measurePreserving hMP
  have h_minkowski :
      _root_.MeasureTheory.eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F - F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
        _root_.MeasureTheory.eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) +
          eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    _root_.MeasureTheory.eLpNorm_sub_le hτF_aesm hF_aesm (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [eLpNorm_translate_eq_local k h F] at h_minkowski
  have h_step : _root_.MeasureTheory.eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h F - F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      2 * _root_.MeasureTheory.eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    rw [two_mul]; exact h_minkowski
  have h_inv_abs : |h⁻¹| = |h|⁻¹ := abs_inv _
  have habs_h_pos : 0 < |h| := abs_pos.mpr hh
  have h_ofReal_inv :
      ENNReal.ofReal |h⁻¹| = (ENNReal.ofReal |h|)⁻¹ := by
    rw [h_inv_abs]
    exact ENNReal.ofReal_inv_of_pos habs_h_pos
  have h_enorm_abs : (‖(h⁻¹ : ℝ)‖ₑ : ℝ≥0∞) = ENNReal.ofReal |h⁻¹| := by
    rw [Real.enorm_eq_ofReal_abs]
  rw [h_enorm_abs, h_ofReal_inv]
  calc (ENNReal.ofReal |h|)⁻¹ *
        _root_.MeasureTheory.eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h F - F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)
      ≤ (ENNReal.ofReal |h|)⁻¹ *
          (2 * _root_.MeasureTheory.eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by gcongr
    _ = 2 / ENNReal.ofReal |h| * _root_.MeasureTheory.eLpNorm F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
        rw [← mul_assoc]
        congr 1
        rw [ENNReal.div_eq_inv_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.eLpNorm_diffQuot_le_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.eLpNorm_diffQuot_le_local target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma nirenbergTestFunction_sub
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) (η u₁ u₂ : EuclN → ℝ) :
    (nirenbergTestFunction (d := Module.finrank ℝ E) k h η u₁) -
        (nirenbergTestFunction (d := Module.finrank ℝ E) k h η u₂) =
      nirenbergTestFunction (d := Module.finrank ℝ E) k h η (u₁ - u₂) := by
  unfold nirenbergTestFunction
  have h_inner_sub :
      (fun y => (η y)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (u₁ - u₂) y) =
      (fun y => (η y)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u₁ y) -
      (fun y => (η y)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u₂ y) := by
    funext y
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_sub
      (d := Module.finrank ℝ E) k h]
    simp [Pi.sub_apply]
    ring
  rw [h_inner_sub]
  rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_sub
    (d := Module.finrank ℝ E) k (-h)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.nirenbergTestFunction_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.nirenbergTestFunction_sub target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem nirenbergTestFunction_seq_tendsto_eLpNorm
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_support_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_cs : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    {K_0 : Set EuclN}
    (hχ_one : ∀ x ∈ Metric.cthickening |h| K_0, χ x = 1)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    {uSeq : ℕ → EuclN → ℝ}
    (hu_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (uSeq n))
    (hu_seq_cs : ∀ n, HasCompactSupport (uSeq n))
    (hu_seq_l2_tendsto : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm
      (fun x => uSeq n x - χ x * D.uChart x) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) _root_.Filter.atTop (𝓝 0)) :
    _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm
      (fun x => nirenbergTestFunction (d := Module.finrank ℝ E) k h η (uSeq n) x -
        nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart x) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (Metric.cthickening |h| K_0))) _root_.Filter.atTop (𝓝 0) := by
  classical
  have h_test_eq : nirenbergTestFunction (d := Module.finrank ℝ E) k h η
      (fun x => χ x * D.uChart x) =
      nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart := by
    funext x
    by_cases hh0 : h = 0
    · subst hh0
      simp [nirenbergTestFunction]
    have h_test_eq_pointwise : ∀ v : EuclN → ℝ,
        nirenbergTestFunction (d := Module.finrank ℝ E) k h η v x =
        ((η (x + (-h) • EuclideanSpace.single k 1))^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h v
            (x + (-h) • EuclideanSpace.single k 1) -
          (η x)^2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h v x) / (-h) := by
      intro v
      exact nirenbergTestFunction_apply (d := Module.finrank ℝ E) k h η v x hh0
    rw [h_test_eq_pointwise (fun x => χ x * D.uChart x),
      h_test_eq_pointwise D.uChart]
    have h_diff_apply : ∀ v y,
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h v y =
          (v (y + h • EuclideanSpace.single k 1) - v y) / h := fun v y =>
      DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh0 v y
    rw [h_diff_apply, h_diff_apply, h_diff_apply, h_diff_apply]
    by_cases hxK0 : x ∈ Metric.cthickening |h| K_0
    · have h_prod_eq : ∀ z, (η z)^2 * (((χ (z + h • EuclideanSpace.single k 1)) *
            D.uChart (z + h • EuclideanSpace.single k 1) - χ z * D.uChart z) / h) =
          (η z)^2 * (((D.uChart (z + h • EuclideanSpace.single k 1)) -
            D.uChart z) / h) := by
        intro z
        by_cases hηz : η z = 0
        · rw [show (η z)^2 = 0 from by rw [hηz]; ring, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.zero_mul]
        have hz_in_support : z ∈ tsupport η := subset_tsupport η hηz
        have hz_in_K0 : z ∈ K_0 := hη_support_in_K_0 hz_in_support
        have hz_in_cthick : z ∈ Metric.cthickening |h| K_0 :=
          Metric.self_subset_cthickening _ hz_in_K0
        have hz_shift_in_cthick : z + h • EuclideanSpace.single k 1 ∈
            Metric.cthickening |h| K_0 := by
          refine Metric.mem_cthickening_of_dist_le _ z |h| K_0 hz_in_K0 ?_
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
          simp [Real.norm_eq_abs]
        have hχz : χ z = 1 := hχ_one z hz_in_cthick
        have hχz_shift : χ (z + h • EuclideanSpace.single k 1) = 1 :=
          hχ_one _ hz_shift_in_cthick
        rw [hχz, hχz_shift, one_mul, one_mul]
      rw [h_prod_eq x, h_prod_eq (x + (-h) • EuclideanSpace.single k 1)]
    · have hηx_zero : η x = 0 := by
        by_contra hηx
        have hx_in_support : x ∈ tsupport η := subset_tsupport η hηx
        have hx_in_K0 : x ∈ K_0 := hη_support_in_K_0 hx_in_support
        exact hxK0 (Metric.self_subset_cthickening _ hx_in_K0)
      have hηx_shift_zero : η (x + (-h) • EuclideanSpace.single k 1) = 0 := by
        by_contra hηxs
        have hxs_in_support : x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
          subset_tsupport η hηxs
        have hxs_in_K0 : x + (-h) • EuclideanSpace.single k 1 ∈ K_0 :=
          hη_support_in_K_0 hxs_in_support
        have hx_in_cthick : x ∈ Metric.cthickening |h| K_0 := by
          refine Metric.mem_cthickening_of_dist_le _
            (x + (-h) • EuclideanSpace.single k 1) |h| K_0 hxs_in_K0 ?_
          rw [dist_eq_norm]
          have h_calc : x - (x + (-h) • EuclideanSpace.single k 1) =
              h • EuclideanSpace.single k 1 := by
            rw [sub_add_eq_sub_sub, sub_self, zero_sub, ← neg_smul, neg_neg]
          rw [h_calc, norm_smul]
          simp [Real.norm_eq_abs]
        exact hxK0 hx_in_cthick
      rw [show (η x)^2 = 0 from by rw [hηx_zero]; ring,
        show (η (x + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
          rw [hηx_shift_zero]; ring]
      simp
  have h_diff_eq : ∀ n,
      (fun x => nirenbergTestFunction (d := Module.finrank ℝ E) k h η (uSeq n) x -
        nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart x) =
      nirenbergTestFunction (d := Module.finrank ℝ E) k h η
        (uSeq n - fun x => χ x * D.uChart x) := by
    intro n
    rw [← h_test_eq]
    exact nirenbergTestFunction_sub k h η (uSeq n)
      (fun x => χ x * D.uChart x)
  have hη_cont : Continuous η := hη_smooth.continuous
  have hη_abs_cont : Continuous (fun x => |η x|) := hη_cont.abs
  obtain ⟨M_η, hM_η_nn, hM_η_bd⟩ : ∃ M_η : ℝ, 0 ≤ M_η ∧ ∀ x, |η x| ≤ M_η := by
    by_cases hSupport_empty : (tsupport η).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        hη_cs.exists_isMaxOn hSupport_empty hη_abs_cont.continuousOn
      refine ⟨|η xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport η
      · exact hxMax_max hx
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hηx, abs_zero]; exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport η
      · exact absurd ⟨x, hx⟩ hSupport_empty
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hηx, abs_zero]
  have h_univ_tendsto :
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm
        (fun x => nirenbergTestFunction (d := Module.finrank ℝ E) k h η (uSeq n) x -
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart x) 2
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) _root_.Filter.atTop (𝓝 0) := by
    have h_eLp_eq : ∀ n,
        _root_.MeasureTheory.eLpNorm (fun x =>
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η (uSeq n) x -
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart x) 2
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        eLpNorm (nirenbergTestFunction (d := Module.finrank ℝ E) k h η
          (uSeq n - fun x => χ x * D.uChart x)) 2
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      intro n
      rw [h_diff_eq n]
    have h_χu_lp : _root_.MeasureTheory.MemLp (fun x => χ x * D.uChart x) 2
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
      cutoff_uChart_memLp_two_univ (I := I) (M := M) D
        hχ_smooth hχ_cs hχ_support_in
    have h_aesm_diff : ∀ n,
        _root_.MeasureTheory.AEStronglyMeasurable (uSeq n - fun x => χ x * D.uChart x)
          (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      intro n
      have h_uSeq_aesm : _root_.MeasureTheory.AEStronglyMeasurable (uSeq n)
          (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
        (hu_seq_smooth n).continuous.aestronglyMeasurable
      exact h_uSeq_aesm.sub h_χu_lp.aestronglyMeasurable
    have h_diff_lp : ∀ n,
        _root_.MeasureTheory.MemLp (uSeq n - fun x => χ x * D.uChart x) 2
          (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      intro n
      have h_uSeq_lp : _root_.MeasureTheory.MemLp (uSeq n) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
        (hu_seq_smooth n).continuous.memLp_of_hasCompactSupport (hu_seq_cs n)
      exact h_uSeq_lp.sub h_χu_lp
    have h_bound : ∀ n,
        eLpNorm (nirenbergTestFunction (d := Module.finrank ℝ E) k h η
          (uSeq n - fun x => χ x * D.uChart x)) 2
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
        (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
          ((2 / ENNReal.ofReal |h|) *
            _root_.MeasureTheory.eLpNorm (uSeq n - fun x => χ x * D.uChart x) 2
              (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by
      intro n
      have h_test_bound :=
        eLpNorm_nirenbergTestFunction_le (d := Module.finrank ℝ E)
          k hh hη_cont (h_aesm_diff n) hM_η_nn hM_η_bd
      have h_dq_bound :=
        eLpNorm_diffQuot_le_local k hh (h_aesm_diff n)
      have h_step1 :
          eLpNorm (nirenbergTestFunction (d := Module.finrank ℝ E) k h η
            (uSeq n - fun x => χ x * D.uChart x)) 2
            (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
          (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            _root_.MeasureTheory.eLpNorm (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (uSeq n - fun x => χ x * D.uChart x)) 2
            (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := h_test_bound
      have h_step2 :
          (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            _root_.MeasureTheory.eLpNorm (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (uSeq n - fun x => χ x * D.uChart x)) 2
            (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
          (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            ((2 / ENNReal.ofReal |h|) *
              _root_.MeasureTheory.eLpNorm (uSeq n - fun x => χ x * D.uChart x) 2
                (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by gcongr
      exact h_step1.trans h_step2
    have h_diff_eLp_eq : ∀ n,
        _root_.MeasureTheory.eLpNorm (fun x => uSeq n x - χ x * D.uChart x) 2
          (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        _root_.MeasureTheory.eLpNorm (uSeq n - fun x => χ x * D.uChart x) 2
          (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      intro n; rfl
    have hu_seq_l2_tendsto' :
        _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (uSeq n - fun x => χ x * D.uChart x) 2
          (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) _root_.Filter.atTop (𝓝 0) := by
      have h_eq : (fun n => _root_.MeasureTheory.eLpNorm (uSeq n - fun x => χ x * D.uChart x) 2
            (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
          (fun n => _root_.MeasureTheory.eLpNorm (fun x => uSeq n x - χ x * D.uChart x) 2
            (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by
        funext n; rfl
      rw [h_eq]
      exact hu_seq_l2_tendsto
    have h_const_tendsto :
        _root_.Filter.Tendsto (fun n =>
          (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            ((2 / ENNReal.ofReal |h|) *
              _root_.MeasureTheory.eLpNorm (uSeq n - fun x => χ x * D.uChart x) 2
                (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) _root_.Filter.atTop (𝓝 0) := by
      have hh_abs_pos : 0 < |h| := abs_pos.mpr hh
      have h_const_ne_top : (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
          (2 / ENNReal.ofReal |h|) ≠ ⊤ := by
        refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_
        · exact ENNReal.div_ne_top ENNReal.ofNat_ne_top
            (ENNReal.ofReal_pos.mpr hh_abs_pos).ne'
        · exact ENNReal.ofReal_ne_top
        · exact ENNReal.div_ne_top ENNReal.ofNat_ne_top
            (ENNReal.ofReal_pos.mpr hh_abs_pos).ne'
      have h_eq_assoc : ∀ n,
          (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            ((2 / ENNReal.ofReal |h|) *
              _root_.MeasureTheory.eLpNorm (uSeq n - fun x => χ x * D.uChart x) 2
                (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
          ((2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            (2 / ENNReal.ofReal |h|)) *
            _root_.MeasureTheory.eLpNorm (uSeq n - fun x => χ x * D.uChart x) 2
              (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
        intro n; ring
      simp only [h_eq_assoc]
      have h := ENNReal.Tendsto.const_mul (a :=
          (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            (2 / ENNReal.ofReal |h|)) hu_seq_l2_tendsto' (Or.inr h_const_ne_top)
      simpa using h
    rw [show (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η (uSeq n) x -
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart x) 2
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) = _ from funext h_eLp_eq]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_const_tendsto
      ?_ ?_
    · refine Filter.Eventually.of_forall (fun n => ?_)
      exact zero_le
    · exact Filter.Eventually.of_forall h_bound
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_univ_tendsto
    ?_ ?_
  · refine Filter.Eventually.of_forall (fun n => ?_)
    exact zero_le
  · refine Filter.Eventually.of_forall (fun n => ?_)
    exact MeasureTheory.eLpNorm_mono_measure
      (fun x =>
        nirenbergTestFunction (d := Module.finrank ℝ E) k h η (uSeq n) x -
        nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart x)
      Measure.restrict_le_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.nirenbergTestFunction_seq_tendsto_eLpNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.nirenbergTestFunction_seq_tendsto_eLpNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.nirenbergTestFunction_seq_tendsto_eLpNorm ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox.nirenbergTestFunction_seq_tendsto_eLpNorm

end SubstitutionDischargeSmoothApprox
end Sobolev
end Analysis
end DifferentialGeometry
