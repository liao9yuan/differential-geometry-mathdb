import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.ChartBilinearVariationalIdentity
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SubstitutionNonSmooth
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.WeakDerivativeBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTranslatedCutoffDiffQuot
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitutionNonSmooth
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
theorem integral_sq_diffQuot_uChart_le
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {η : EuclN → ℝ} (hη_support : HasCompactSupport η)
    {Ω' : Set EuclN}
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hΩ'_compact_closure : IsCompact (closure Ω'))
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω') :
    ∀ (k : Fin (Module.finrank ℝ E)),
    ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart x)^2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
        ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E),
          ((D.weakPartial l) x) ^ 2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have hη_tsupp_compact : IsCompact (tsupport η) := hη_support
  have h_cthickR0_compact : IsCompact (Metric.cthickening R₀ (tsupport η)) :=
    hη_tsupp_compact.cthickening
  have h_cthickR0_in_Ω' : Metric.cthickening R₀ (tsupport η) ⊆ Ω' := by
    have h := hh_support_in_Ω' (h := R₀) (by rw [abs_of_pos hR₀_pos])
    rw [abs_of_pos hR₀_pos] at h
    exact h
  have h_cthickR0_in_chart :
      Metric.cthickening R₀ (tsupport η) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
    h_cthickR0_in_Ω'.trans (subset_closure.trans hΩ'_chart)
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, hδ_pos, hδ_in_chart⟩ :=
    h_cthickR0_compact.exists_cthickening_subset_open h_chart_open
      h_cthickR0_in_chart
  set r : ℝ := R₀ + δ / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_le : r ≤ R₀ + δ := by rw [hr_def]; linarith
  have h_cthick_r_compact : IsCompact (Metric.cthickening r (tsupport η)) :=
    hη_tsupp_compact.cthickening
  have h_cthick_r_in_chart :
      Metric.cthickening r (tsupport η) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
    intro x hx
    have hx' : x ∈ Metric.cthickening (R₀ + δ) (tsupport η) :=
      Metric.cthickening_mono hr_le _ hx
    have h_eq : Metric.cthickening (R₀ + δ) (tsupport η) =
        Metric.cthickening δ (Metric.cthickening R₀ (tsupport η)) := by
      have hδ_le : (0 : ℝ) ≤ δ := hδ_pos.le
      have hR0_le : (0 : ℝ) ≤ R₀ := hR₀_pos.le
      rw [show (R₀ + δ) = (δ + R₀) from by ring,
        ← cthickening_cthickening hδ_le hR0_le]
    rw [h_eq] at hx'
    exact hδ_in_chart hx'
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_one_nhds, hχ_tsupp, hχ_range⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact
      (K := Metric.cthickening r (tsupport η))
      (U := chartTargetEuclid (I := I) (M := M) α)
      h_cthick_r_compact h_chart_open h_cthick_r_in_chart
  have hχ_one : ∀ x ∈ Metric.cthickening r (tsupport η), χ x = 1 := fun _ hx =>
    hχ_one_nhds.self_of_nhdsSet hx
  have hχ_nn : ∀ x : EuclN, 0 ≤ χ x ∧ χ x ≤ 1 := by
    intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    exact ⟨(hχ_range hx_range).1, (hχ_range hx_range).2⟩
  set u_g : EuclN → ℝ := fun x => χ x * D.uChart x with hu_g_def
  set G : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun i x =>
    (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
    χ x * D.weakPartial i x with hG_def
  have hu_g_l2 : _root_.MeasureTheory.MemLp u_g 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    cutoff_uChart_memLp_two_univ (I := I) (M := M) D hχ_smooth hχ_cs hχ_tsupp
  have hG_l2 : ∀ i, _root_.MeasureTheory.MemLp (G i) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := fun i =>
    cutoff_uChart_partial_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp i
  have hG_isWP : ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (G i) u_g Set.univ := fun i =>
    cutoff_uChart_hasWeakPartialDeriv_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp i
  intro k h hh hh_le
  have hh_abs_pos : 0 < |h| := abs_pos.mpr hh
  have hh_abs_le : |h| ≤ R₀ := hh_le
  set Ω'_fk : Set EuclN := Metric.cthickening |h| (tsupport η) with hΩ'_fk_def
  set Ω''_fk : Set EuclN := tsupport η with hΩ''_fk_def
  have hΩ'_fk_meas : MeasurableSet Ω'_fk := by
    rw [hΩ'_fk_def]; exact (Metric.isClosed_cthickening).measurableSet
  have hΩ''_fk_meas : MeasurableSet Ω''_fk := by
    rw [hΩ''_fk_def]; exact (isClosed_tsupport η).measurableSet
  have h_closure_eq : closure Ω''_fk = tsupport η := by
    rw [hΩ''_fk_def]; exact (isClosed_tsupport η).closure_eq
  have hΩ''_compact_closure : IsCompact (closure Ω''_fk) := by
    rw [h_closure_eq]; exact hη_tsupp_compact
  have h_thick : Metric.cthickening |h| (closure Ω''_fk) ⊆ Ω'_fk := by
    rw [h_closure_eq, hΩ'_fk_def]
  have h_FK : ∫ x in Ω''_fk,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      ∫ x in Ω'_fk, (G k x)^2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    exact
      DifferentialGeometry.Analysis.Sobolev.integral_sq_diffQuot_le_integral_sq_weakPartial_meas
        (d := Module.finrank ℝ E)
        hu_g_l2 (hG_l2 k) k (hG_isWP k)
        hΩ'_fk_meas hΩ''_fk_meas
        hΩ''_compact_closure hh_abs_pos h_thick hh (le_refl |h|)
  have hr_ge_R0 : R₀ ≤ r := by rw [hr_def]; linarith
  have h_cthick_h_subset_r :
      Metric.cthickening |h| (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.cthickening_mono (hh_abs_le.trans hr_ge_R0) _
  have h_self_subset_cthick_h :
      tsupport η ⊆ Metric.cthickening |h| (tsupport η) :=
    Metric.self_subset_cthickening _
  have h_diffQuot_eq_on_tsupport : ∀ x ∈ tsupport η,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart x := by
    intro x hx
    have hx_in_r : x ∈ Metric.cthickening r (tsupport η) := by
      exact h_cthick_h_subset_r (h_self_subset_cthick_h hx)
    have hχx : χ x = 1 := hχ_one x hx_in_r
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_r : x + h • EuclideanSpace.single k 1 ∈
        Metric.cthickening r (tsupport η) := h_cthick_h_subset_r h_shift_in_cthick_h
    have hχ_shift : χ (x + h • EuclideanSpace.single k 1) = 1 :=
      hχ_one _ h_shift_in_r
    change
      (if h = 0 then 0 else
        (u_g (x + h • EuclideanSpace.single k 1) - u_g x) / h) =
      (if h = 0 then 0 else
        (D.uChart (x + h • EuclideanSpace.single k 1) - D.uChart x) / h)
    rw [if_neg hh, if_neg hh, hu_g_def]
    simp only [hχ_shift, hχx, one_mul]
  have h_LHS_eq :
      ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart x)^2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    refine _root_.MeasureTheory.setIntegral_congr_fun (isClosed_tsupport η).measurableSet ?_
    intro x hx
    have h_eq := h_diffQuot_eq_on_tsupport x hx
    exact congrArg (· ^ 2) h_eq.symm
  have hh_abs_lt_r : |h| < r := by rw [hr_def]; linarith
  have h_cthick_h_subset_thick_r :
      Metric.cthickening |h| (tsupport η) ⊆ Metric.thickening r (tsupport η) := by
    intro x hx
    have h_inf : Metric.infEDist x (tsupport η) ≤ ENNReal.ofReal |h| :=
      (Metric.mem_cthickening_iff).mp hx
    have h_ofReal_lt : ENNReal.ofReal |h| < ENNReal.ofReal r :=
      ENNReal.ofReal_lt_ofReal_iff hr_pos |>.mpr hh_abs_lt_r
    have h_inf_lt : Metric.infEDist x (tsupport η) < ENNReal.ofReal r :=
      lt_of_le_of_lt h_inf h_ofReal_lt
    exact (Metric.mem_thickening_iff_infEDist_lt).mpr h_inf_lt
  have h_thick_r_open : IsOpen (Metric.thickening r (tsupport η)) :=
    Metric.isOpen_thickening
  have h_thick_r_subset_cthick_r :
      Metric.thickening r (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.thickening_subset_cthickening _ _
  have h_fderiv_zero_on_thick_r : ∀ x ∈ Metric.thickening r (tsupport η),
      (fderiv ℝ χ x) (EuclideanSpace.single k 1) = 0 := by
    intro x hx
    have hχ_eq_one_nhds : (fun y => χ y) =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
      refine Filter.eventually_of_mem (h_thick_r_open.mem_nhds hx) ?_
      intro y hy
      exact hχ_one y (h_thick_r_subset_cthick_r hy)
    have h_fderiv_eq : fderiv ℝ χ x = fderiv ℝ (fun _ : EuclN => (1 : ℝ)) x :=
      Filter.EventuallyEq.fderiv_eq hχ_eq_one_nhds
    rw [h_fderiv_eq]
    simp
  have hG_eq_on_cthick_h : ∀ x ∈ Metric.cthickening |h| (tsupport η),
      G k x = D.weakPartial k x := by
    intro x hx
    have hx_in_r : x ∈ Metric.cthickening r (tsupport η) := h_cthick_h_subset_r hx
    have hx_in_thick_r : x ∈ Metric.thickening r (tsupport η) :=
      h_cthick_h_subset_thick_r hx
    have hχx : χ x = 1 := hχ_one x hx_in_r
    have hdχx : (fderiv ℝ χ x) (EuclideanSpace.single k 1) = 0 :=
      h_fderiv_zero_on_thick_r x hx_in_thick_r
    change (fderiv ℝ χ x) (EuclideanSpace.single k 1) * D.uChart x +
      χ x * D.weakPartial k x = D.weakPartial k x
    rw [hdχx, hχx, _root_.MulZeroClass.zero_mul, one_mul, zero_add]
  have h_FK_RHS_eq :
      ∫ x in Ω'_fk, (G k x)^2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ∫ x in Ω'_fk, (D.weakPartial k x)^2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    refine _root_.MeasureTheory.setIntegral_congr_fun hΩ'_fk_meas ?_
    intro x hx
    have h_eq := hG_eq_on_cthick_h x (by rw [hΩ'_fk_def] at hx; exact hx)
    exact congrArg (· ^ 2) h_eq
  have h_cthick_h_subset_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' :=
    hh_support_in_Ω' hh_le
  have h_closure_Ω'_meas : MeasurableSet (closure Ω') :=
    isClosed_closure.measurableSet
  have h_wp_k_l2_closure_Ω' : _root_.MeasureTheory.MemLp (D.weakPartial k) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω')) :=
    D.weak_partial_locally_memLp k (closure Ω') hΩ'_compact_closure hΩ'_chart
  have h_wp_k_l2_Ω' : _root_.MeasureTheory.MemLp (D.weakPartial k) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω') :=
    h_wp_k_l2_closure_Ω'.mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have h_wp_k_intOn_Ω' : _root_.MeasureTheory.IntegrableOn (fun x => (D.weakPartial k x) ^ 2)
      Ω' (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    h_wp_k_l2_Ω'.integrable_sq
  have h_set_mono :
      ∫ x in Ω'_fk, (D.weakPartial k x)^2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      ∫ x in Ω', (D.weakPartial k x)^2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    refine _root_.MeasureTheory.setIntegral_mono_set h_wp_k_intOn_Ω' ?_ ?_
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _
    · refine Filter.Eventually.of_forall ?_
      intro x hx
      rw [hΩ'_fk_def] at hx
      exact h_cthick_h_subset_Ω' hx
  have h_per_l_intOn : ∀ l, _root_.MeasureTheory.IntegrableOn (fun x => (D.weakPartial l x) ^ 2)
      Ω' (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    intro l
    have h_wp_l_l2_closure_Ω' : _root_.MeasureTheory.MemLp (D.weakPartial l) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω')) :=
      D.weak_partial_locally_memLp l (closure Ω') hΩ'_compact_closure hΩ'_chart
    have h_wp_l_l2_Ω' : _root_.MeasureTheory.MemLp (D.weakPartial l) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω') :=
      h_wp_l_l2_closure_Ω'.mono_measure
        (Measure.restrict_mono subset_closure le_rfl)
    exact h_wp_l_l2_Ω'.integrable_sq
  have h_sum_intOn : _root_.MeasureTheory.IntegrableOn
      (fun x => ∑ l : Fin (Module.finrank ℝ E), (D.weakPartial l x) ^ 2)
      Ω' (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    _root_.MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω')
      (f := fun l x => (D.weakPartial l x) ^ 2)
      (fun l _ => h_per_l_intOn l)
  have h_k_le_sum :
      ∫ x in Ω', (D.weakPartial k x)^2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((D.weakPartial l) x)^2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    refine _root_.MeasureTheory.integral_mono_ae (h_per_l_intOn k) h_sum_intOn ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact Finset.single_le_sum (f := fun l => (D.weakPartial l x) ^ 2)
      (fun l _ => sq_nonneg _) (Finset.mem_univ k)
  calc ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart x)^2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)
      = ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := h_LHS_eq
    _ ≤ ∫ x in Ω'_fk, (G k x)^2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := h_FK
    _ = ∫ x in Ω'_fk, (D.weakPartial k x)^2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := h_FK_RHS_eq
    _ ≤ ∫ x in Ω', (D.weakPartial k x)^2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := h_set_mono
    _ ≤ ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((D.weakPartial l) x)^2
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := h_k_le_sum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.integral_sq_diffQuot_uChart_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.integral_sq_diffQuot_uChart_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.integral_sq_diffQuot_uChart_le ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.integral_sq_diffQuot_uChart_le

end ChartBilinearH1Compl

end Laplacian
end Analysis
end DifferentialGeometry
