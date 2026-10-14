import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.ChartBilinearDischarge.SubstitutionIBP
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.ChartBilinearDischarge.SubstitutionGradTendsto
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.ChartBilinearTrivialCases

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
namespace SubstitutionDischargeAssembly

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
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeGradTendsto
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBP
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionChartBilinearTrivialCases
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))


omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private theorem exists_chart_target_cutoff_strong
    [I.Boundaryless]
    {α : M}
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {R₀ : ℝ} {h : ℝ} (_hh_le : |h| ≤ R₀)
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ (δ : ℝ) (χ : EuclN → ℝ),
      0 < δ ∧
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧
      (∀ x ∈ Metric.cthickening δ (Metric.cthickening |h| K_0), χ x = 1) ∧
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
  refine ⟨δ, χ, hδ_pos, hχ_smooth, hχ_compact, ?_, ?_, hχ_one, hχ_support⟩
  · intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    exact (hχ_range hx_range).1
  · intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    exact (hχ_range hx_range).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.exists_chart_target_cutoff_strong
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.exists_chart_target_cutoff_strong target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma fderiv_chi_zero_on_cthickening
    {δ : ℝ} (hδ : 0 < δ) {χ : EuclN → ℝ} {h : ℝ} {K_0 : Set EuclN}
    (hχ_one : ∀ x ∈ Metric.cthickening δ (Metric.cthickening |h| K_0), χ x = 1)
    {x : EuclN} (hx : x ∈ Metric.cthickening |h| K_0)
    (i : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0 :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.fderiv_cutoff_apply_zero_on_cthickening
    (d := Module.finrank ℝ E) hδ hχ_one hx i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.fderiv_chi_zero_on_cthickening
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.fderiv_chi_zero_on_cthickening target :: scope.openDecls } }


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chi_eq_one_on_cthickening
    {δ : ℝ} (_hδ : 0 < δ) {χ : EuclN → ℝ} {h : ℝ} {K_0 : Set EuclN}
    (hχ_one : ∀ x ∈ Metric.cthickening δ (Metric.cthickening |h| K_0), χ x = 1)
    {x : EuclN} (hx : x ∈ Metric.cthickening |h| K_0) : χ x = 1 := by
  have hx_inner : x ∈ Metric.cthickening δ (Metric.cthickening |h| K_0) :=
    Metric.self_subset_cthickening _ hx
  exact hχ_one x hx_inner

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.chi_eq_one_on_cthickening
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.chi_eq_one_on_cthickening target :: scope.openDecls } }

private noncomputable def vTestPartialSummand
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (η : EuclN → ℝ) (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (j : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun z => (η z)^2 *
    DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart z

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.vTestPartialSummand
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.vTestPartialSummand target :: scope.openDecls } }

private noncomputable def vTestPartialSummandIndicator
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (η : EuclN → ℝ) (k : Fin (Module.finrank ℝ E)) (h : ℝ) (K_0 : Set EuclN)
    (j : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun z => (η z)^2 *
    DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h
      ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) z +
    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.uChart) z

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.vTestPartialSummandIndicator
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.vTestPartialSummandIndicator target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma tF_eq_tFE_on_tsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ}
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E)) {h : ℝ}
    (j : Fin (Module.finrank ℝ E))
    {z : EuclN} (hz : z ∈ tsupport η) :
    vTestPartialSummand (I := I) (M := M) D η k h j z =
      vTestPartialSummandIndicator (I := I) (M := M) D η k h K_0 j z := by
  classical
  have hz_K_0 : z ∈ K_0 := hη_support_in_K_0 hz
  have hz_thick : z ∈ Metric.cthickening |h| K_0 :=
    Metric.self_subset_cthickening _ hz_K_0
  have hz_shift : z + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| K_0 := by
    refine Metric.mem_cthickening_of_dist_le _ z |h| K_0 hz_K_0 ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp [Real.norm_eq_abs]
  have h_dq_wp : DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h (D.weakPartial j) z =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) z := by
    by_cases hh : h = 0
    · subst hh
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    · rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh]
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh]
      rw [Set.indicator_of_mem hz_shift, Set.indicator_of_mem hz_thick]
  have h_dq_u : DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h D.uChart z =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.uChart) z := by
    by_cases hh : h = 0
    · subst hh
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    · rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh]
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh]
      rw [Set.indicator_of_mem hz_shift, Set.indicator_of_mem hz_thick]
  unfold vTestPartialSummand vTestPartialSummandIndicator
  rw [h_dq_wp, h_dq_u]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.tF_eq_tFE_on_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.tF_eq_tFE_on_tsupport target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma tF_eq_zero_outside_tsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {η : EuclN → ℝ} (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (j : Fin (Module.finrank ℝ E))
    {z : EuclN} (hz : z ∉ tsupport η) :
    vTestPartialSummand (I := I) (M := M) D η k h j z = 0 := by
  unfold vTestPartialSummand
  have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
  rw [show (η z)^2 = 0 from by rw [hηz]; ring, _root_.MulZeroClass.zero_mul]
  rw [show 2 * η z = 0 from by rw [hηz]; ring]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.tF_eq_zero_outside_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.tF_eq_zero_outside_tsupport target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma tFE_eq_zero_outside_tsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {η : EuclN → ℝ} {h : ℝ} (k : Fin (Module.finrank ℝ E)) (K_0 : Set EuclN)
    (j : Fin (Module.finrank ℝ E))
    {z : EuclN} (hz : z ∉ tsupport η) :
    vTestPartialSummandIndicator (I := I) (M := M) D η k h K_0 j z = 0 := by
  unfold vTestPartialSummandIndicator
  have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
  rw [show (η z)^2 = 0 from by rw [hηz]; ring, _root_.MulZeroClass.zero_mul]
  rw [show 2 * η z = 0 from by rw [hηz]; ring]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.tFE_eq_zero_outside_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.tFE_eq_zero_outside_tsupport target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma tF_eq_tFE
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ}
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E)) {h : ℝ}
    (j : Fin (Module.finrank ℝ E)) :
    vTestPartialSummand (I := I) (M := M) D η k h j =
      vTestPartialSummandIndicator (I := I) (M := M) D η k h K_0 j := by
  funext z
  by_cases hz : z ∈ tsupport η
  · exact tF_eq_tFE_on_tsupport (I := I) (M := M) D
      hη_support_in_K_0 k j hz
  · rw [tF_eq_zero_outside_tsupport (I := I) (M := M) D k h j hz,
      tFE_eq_zero_outside_tsupport (I := I) (M := M) D k K_0 j hz]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.tF_eq_tFE
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.tF_eq_tFE target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma uChart_indicator_memLp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {h : ℝ}
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    _root_.MeasureTheory.MemLp ((Metric.cthickening |h| K_0).indicator D.uChart) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact
  have h_thick_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
    h_thick_compact.measurableSet
  refine (MeasureTheory.memLp_indicator_iff_restrict h_thick_meas).mpr ?_
  exact memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    D.u_chart_memLp_weighted h_thick_compact h_thick_meas h_thick

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.uChart_indicator_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.uChart_indicator_memLp target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma weakPartial_indicator_memLp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {h : ℝ}
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (j : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.MemLp ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact
  have h_thick_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
    h_thick_compact.measurableSet
  refine (MeasureTheory.memLp_indicator_iff_restrict h_thick_meas).mpr ?_
  exact D.weak_partial_locally_memLp j (Metric.cthickening |h| K_0)
    h_thick_compact h_thick

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.weakPartial_indicator_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.weakPartial_indicator_memLp target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma memLp_diffQuot_of_memLp_local
    {F : EuclN → ℝ} (hF_lp : _root_.MeasureTheory.MemLp F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
    (k : Fin (Module.finrank ℝ E)) {h : ℝ} (hh : h ≠ 0) :
    _root_.MeasureTheory.MemLp (DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have hF_aesm : _root_.MeasureTheory.AEStronglyMeasurable F (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    hF_lp.aestronglyMeasurable
  have hdq_aesm : _root_.MeasureTheory.AEStronglyMeasurable
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h F) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    DifferentialGeometry.Analysis.Sobolev.aestronglyMeasurable_diffQuot
      (d := Module.finrank ℝ E) k h hF_aesm
  refine ⟨hdq_aesm, ?_⟩
  have h_dq_eq : DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h F =
      h⁻¹ • (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F - F) := by
    funext x
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh F x]
    simp [Pi.smul_apply, Pi.sub_apply,
      DifferentialGeometry.Analysis.Sobolev.translate, smul_eq_mul]
    field_simp
  rw [h_dq_eq]
  have hτF_lp : _root_.MeasureTheory.MemLp (DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h F) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    DifferentialGeometry.Analysis.Sobolev.memLp_translate
      (d := Module.finrank ℝ E) k h hF_lp
  have h_diff_lp : _root_.MeasureTheory.MemLp ((DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h F) - F) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := hτF_lp.sub hF_lp
  have h_smul_lp : _root_.MeasureTheory.MemLp (h⁻¹ • ((DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h F) - F)) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := h_diff_lp.const_smul h⁻¹
  exact h_smul_lp.eLpNorm_lt_top

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.memLp_diffQuot_of_memLp_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.memLp_diffQuot_of_memLp_local target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma tFE_memLp_two
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (j : Fin (Module.finrank ℝ E)) :
    MemLp (vTestPartialSummandIndicator (I := I) (M := M) D η k h K_0 j) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have hη_cont : Continuous η := hη.continuous
  have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  obtain ⟨M_η, hM_η_nn, hM_η_bd⟩ : ∃ M_η : ℝ, 0 ≤ M_η ∧ ∀ x, |η x| ≤ M_η := by
    by_cases hSupport_empty : (tsupport η).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        hη_support.exists_isMaxOn hSupport_empty hη_cont.abs.continuousOn
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
  have h_partial_eta_cont : Continuous
      (fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) :=
    (hη.continuous_fderiv h_top_ne_zero).clm_apply continuous_const
  have h_partial_eta_cs : HasCompactSupport
      (fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) :=
    hη_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  obtain ⟨M_dη, hM_dη_nn, hM_dη_bd⟩ :
      ∃ M_dη : ℝ, 0 ≤ M_dη ∧
        ∀ x, |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤ M_dη := by
    by_cases hSupport_empty : (tsupport (fun z : EuclN => (fderiv ℝ η z)
        (EuclideanSpace.single j 1))).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        h_partial_eta_cs.exists_isMaxOn hSupport_empty
          h_partial_eta_cont.abs.continuousOn
      refine ⟨|(fderiv ℝ η xMax) (EuclideanSpace.single j 1)|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport (fun z : EuclN => (fderiv ℝ η z)
          (EuclideanSpace.single j 1))
      · exact hxMax_max hx
      · have hpartialx :
            (fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) x = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) hx
        rw [show (fderiv ℝ η x) (EuclideanSpace.single j 1) = 0 from hpartialx,
          abs_zero]
        exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport (fun z : EuclN => (fderiv ℝ η z)
          (EuclideanSpace.single j 1))
      · exact absurd ⟨x, hx⟩ hSupport_empty
      · have hpartialx :
            (fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) x = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) hx
        rw [show (fderiv ℝ η x) (EuclideanSpace.single j 1) = 0 from hpartialx,
          abs_zero]
  have hu_ext_lp := uChart_indicator_memLp (I := I) (M := M) D
    hK_0_compact h_thick
  have hwp_ext_lp := weakPartial_indicator_memLp (I := I) (M := M) D
    hK_0_compact h_thick j
  have hdq_u_ext_lp : _root_.MeasureTheory.MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.uChart)) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    memLp_diffQuot_of_memLp_local hu_ext_lp k hh
  have hdq_wp_ext_lp : _root_.MeasureTheory.MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weakPartial j))) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    memLp_diffQuot_of_memLp_local hwp_ext_lp k hh
  unfold vTestPartialSummandIndicator
  have ht1_pt_bd : ∀ z, ‖(η z)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) z‖ ≤
      ‖M_η^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) z‖ := by
    intro z
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ M_η^2)]
    have h_eta_sq : |(η z)^2| ≤ M_η^2 := by
      have h_abs : |η z| ≤ M_η := hM_η_bd z
      have h_eq : |(η z)^2| = (η z)^2 := abs_of_nonneg (sq_nonneg _)
      rw [h_eq]
      calc (η z)^2 = (|η z|)^2 := (sq_abs _).symm
        _ ≤ M_η^2 := pow_le_pow_left₀ (abs_nonneg _) h_abs 2
    exact mul_le_mul_of_nonneg_right h_eta_sq (abs_nonneg _)
  have ht1_aesm : _root_.MeasureTheory.AEStronglyMeasurable (fun z => (η z)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) z)
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    (hη_cont.pow 2).aestronglyMeasurable.mul hdq_wp_ext_lp.aestronglyMeasurable
  have ht1_lp : _root_.MeasureTheory.MemLp (fun z => (η z)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) z) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    MemLp.mono (hdq_wp_ext_lp.const_mul (M_η^2)) ht1_aesm
      (Filter.Eventually.of_forall ht1_pt_bd)
  have ht2_pt_bd : ∀ z, ‖2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.uChart) z‖ ≤
      ‖(2 * M_η * M_dη) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z‖ := by
    intro z
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have h_lhs_abs : |(2 : ℝ) * η z *
        (fderiv ℝ η z) (EuclideanSpace.single j 1) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z| =
        (2 * |η z| * |(fderiv ℝ η z) (EuclideanSpace.single j 1)|) *
        |DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h_rhs_abs : |(2 * M_η * M_dη) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z| =
        (2 * M_η * M_dη) *
        |DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * M_η * M_dη)]
    rw [h_lhs_abs, h_rhs_abs]
    have h_factor : 2 * |η z| * |(fderiv ℝ η z) (EuclideanSpace.single j 1)| ≤
        2 * M_η * M_dη := by
      have h1 : |η z| * |(fderiv ℝ η z) (EuclideanSpace.single j 1)| ≤
          M_η * M_dη :=
        mul_le_mul (hM_η_bd z) (hM_dη_bd z) (abs_nonneg _) hM_η_nn
      calc 2 * |η z| * |(fderiv ℝ η z) (EuclideanSpace.single j 1)|
          = 2 * (|η z| * |(fderiv ℝ η z) (EuclideanSpace.single j 1)|) := by ring
        _ ≤ 2 * (M_η * M_dη) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
        _ = 2 * M_η * M_dη := by ring
    exact mul_le_mul_of_nonneg_right h_factor (abs_nonneg _)
  have ht2_aesm : _root_.MeasureTheory.AEStronglyMeasurable (fun z =>
      2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z)
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    (((continuous_const.mul hη_cont).mul h_partial_eta_cont).aestronglyMeasurable).mul
      hdq_u_ext_lp.aestronglyMeasurable
  have ht2_lp : _root_.MeasureTheory.MemLp (fun z =>
      2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    MemLp.mono (hdq_u_ext_lp.const_mul (2 * M_η * M_dη)) ht2_aesm
      (Filter.Eventually.of_forall ht2_pt_bd)
  exact ht1_lp.add ht2_lp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.tFE_memLp_two
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.tFE_memLp_two target :: scope.openDecls } }

private noncomputable def weakPartial_v_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (η : EuclN → ℝ) (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (j : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.diffQuot
    (d := Module.finrank ℝ E) k (-h)
    (vTestPartialSummand (I := I) (M := M) D η k h j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.weakPartial_v_h
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.weakPartial_v_h target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma weakPartial_v_h_memLp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (j : Fin (Module.finrank ℝ E)) :
    MemLp (weakPartial_v_h (I := I) (M := M) D η k h j) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  unfold weakPartial_v_h
  rw [tF_eq_tFE (I := I) (M := M) D hη_support_in_K_0 k j]
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  exact memLp_diffQuot_of_memLp_local
    (tFE_memLp_two (I := I) (M := M) D hK_0_compact hη hη_support k hh h_thick j)
    k hnh

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.weakPartial_v_h_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.weakPartial_v_h_memLp target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma nirenbergTestFunction_uChart_memLp_cthickening
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    MemLp (nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)) := by
  classical
  set F : EuclN → ℝ := fun z =>
    (η z)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart z with hF_def
  set F_ext : EuclN → ℝ := fun z =>
    (η z)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.uChart) z with hF_ext_def
  have hF_eq : F = F_ext := by
    funext z
    by_cases hz : z ∈ tsupport η
    · have hz_K_0 : z ∈ K_0 := hη_support_in_K_0 hz
      have hz_thick : z ∈ Metric.cthickening |h| K_0 :=
        Metric.self_subset_cthickening _ hz_K_0
      have hz_shift : z + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| K_0 := by
        refine Metric.mem_cthickening_of_dist_le _ z |h| K_0 hz_K_0 ?_
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
        simp [Real.norm_eq_abs]
      have h_dq_u : DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.uChart z =
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            ((Metric.cthickening |h| K_0).indicator D.uChart) z := by
        by_cases hh_eq : h = 0
        · subst hh_eq
          simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
        · rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hh_eq]
          rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hh_eq]
          rw [Set.indicator_of_mem hz_shift, Set.indicator_of_mem hz_thick]
      change (η z)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.uChart z =
        (η z)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z
      rw [h_dq_u]
    · have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
      change (η z)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.uChart z =
        (η z)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z
      rw [show (η z)^2 = 0 from by rw [hηz]; ring]
      ring
  have hη_cont : Continuous η := hη.continuous
  obtain ⟨M_η, hM_η_nn, hM_η_bd⟩ : ∃ M_η : ℝ, 0 ≤ M_η ∧ ∀ x, |η x| ≤ M_η := by
    by_cases hSupport_empty : (tsupport η).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        hη_support.exists_isMaxOn hSupport_empty hη_cont.abs.continuousOn
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
  have hu_ext_lp := uChart_indicator_memLp (I := I) (M := M) D
    hK_0_compact h_thick
  have hdq_u_ext_lp : _root_.MeasureTheory.MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.uChart)) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    memLp_diffQuot_of_memLp_local hu_ext_lp k hh
  have hF_ext_pt_bd : ∀ z, ‖F_ext z‖ ≤
      ‖M_η^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z‖ := by
    intro z
    change ‖(η z)^2 * _‖ ≤ ‖M_η^2 * _‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ M_η^2)]
    have h_eta_sq : |(η z)^2| ≤ M_η^2 := by
      have h_abs : |η z| ≤ M_η := hM_η_bd z
      have h_eq : |(η z)^2| = (η z)^2 := abs_of_nonneg (sq_nonneg _)
      rw [h_eq]
      calc (η z)^2 = (|η z|)^2 := (sq_abs _).symm
        _ ≤ M_η^2 := pow_le_pow_left₀ (abs_nonneg _) h_abs 2
    exact mul_le_mul_of_nonneg_right h_eta_sq (abs_nonneg _)
  have hF_ext_aesm : _root_.MeasureTheory.AEStronglyMeasurable F_ext (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    (hη_cont.pow 2).aestronglyMeasurable.mul hdq_u_ext_lp.aestronglyMeasurable
  have hF_ext_lp : _root_.MeasureTheory.MemLp F_ext 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    MemLp.mono (hdq_u_ext_lp.const_mul (M_η^2)) hF_ext_aesm
      (Filter.Eventually.of_forall hF_ext_pt_bd)
  have hF_lp : _root_.MeasureTheory.MemLp F 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    rw [hF_eq]; exact hF_ext_lp
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have h_dq_F_lp : _root_.MeasureTheory.MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) F) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    memLp_diffQuot_of_memLp_local hF_lp k hnh
  have h_restrict_lp : _root_.MeasureTheory.MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) F) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
    h_dq_F_lp.restrict _
  have h_test_eq : nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) F := rfl
  rw [h_test_eq]
  exact h_restrict_lp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.nirenbergTestFunction_uChart_memLp_cthickening
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.nirenbergTestFunction_uChart_memLp_cthickening target :: scope.openDecls } }


omit [NeZero (Module.finrank ℝ E)] in
theorem variational_identity_at_v_h_of_compact_support
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weakPartial i y *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.uChart z) y)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.uChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.fChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  let _ : NeZero (Module.finrank ℝ E) :=
    ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt k.isLt)⟩
  obtain ⟨δ, χ, hδ_pos, hχ_smooth, hχ_cs, hχ_nn, hχ_le_one,
    hχ_one_strong, hχ_support⟩ :=
    exists_chart_target_cutoff_strong (I := I) (M := M) (α := α)
      hK_0_compact hh_le h_thick
  have hχ_one : ∀ x ∈ Metric.cthickening |h| K_0, χ x = 1 := fun x hx =>
    chi_eq_one_on_cthickening hδ_pos hχ_one_strong hx
  have hχ_dx_zero : ∀ x ∈ Metric.cthickening |h| K_0, ∀ i,
      (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0 := fun x hx i =>
    fderiv_chi_zero_on_cthickening hδ_pos hχ_one_strong hx i
  obtain ⟨uSeq, hu_seq_smooth, hu_seq_cs, hu_seq_l2, hu_seq_grad_l2⟩ :=
    exists_smooth_uChart_approx (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_support
  have h_v_seq_l2 :
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
        nirenbergTestFunction (d := Module.finrank ℝ E) k h η (uSeq n) x -
        nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart x) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0) :=
    nirenbergTestFunction_seq_tendsto_eLpNorm (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_support hη hη_support k hh
      hχ_one hη_support_in_K_0 hu_seq_smooth hu_seq_cs hu_seq_l2
  have h_v_seq_grad_l2 : ∀ j : Fin (Module.finrank ℝ E),
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm
        (fun y => (fderiv ℝ
          (nirenbergTestFunction (d := Module.finrank ℝ E) k h η
            (uSeq n)) y) (EuclideanSpace.single j 1) -
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart z) y) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (Metric.cthickening |h| K_0))) _root_.Filter.atTop (𝓝 0) := by
    intro j
    exact nirenbergTestFunction_seq_grad_tendsto_eLpNorm (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_support hη hη_support hK_0_compact hχ_one hχ_dx_zero
      hη_support_in_K_0 k hh hu_seq_smooth hu_seq_cs hu_seq_l2
      hu_seq_grad_l2 j
  set wpv : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun j y =>
    DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k (-h)
      (fun z => (η z)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
        2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart z) y with hwpv_def
  have hv_h_lp : _root_.MeasureTheory.MemLp (nirenbergTestFunction (d := Module.finrank ℝ E)
      k h η D.uChart) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
    nirenbergTestFunction_uChart_memLp_cthickening (I := I) (M := M) D
      hK_0_compact hη hη_support hη_support_in_K_0 k hh hh_le h_thick
  have h_wpv_eq_def : ∀ j : Fin (Module.finrank ℝ E),
      wpv j = weakPartial_v_h (I := I) (M := M) D η k h j := by
    intro j
    rfl
  have hv_h_grad_lp : ∀ j : Fin (Module.finrank ℝ E),
      _root_.MeasureTheory.MemLp (wpv j) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Metric.cthickening |h| K_0)) := by
    intro j
    rw [h_wpv_eq_def j]
    exact (weakPartial_v_h_memLp (I := I) (M := M) D
      hK_0_compact hη hη_support hη_support_in_K_0 k hh h_thick j).restrict _
  have h_v_seq_support : ∀ n : ℕ,
      tsupport (nirenbergTestFunction (d := Module.finrank ℝ E)
        k h η (uSeq n)) ⊆ Metric.cthickening |h| K_0 := fun n =>
    nirenbergTestFunction_tsupport_in_thickening (E := E) k h
      hη_support_in_K_0 (uSeq n)
  exact variational_identity_at_v_h (I := I) (M := M) D
    hK_0_compact hη hη_support k hh h_thick
    wpv hv_h_lp hv_h_grad_lp uSeq hu_seq_smooth h_v_seq_support
    h_v_seq_l2 h_v_seq_grad_l2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.variational_identity_at_v_h_of_compact_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.variational_identity_at_v_h_of_compact_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.variational_identity_at_v_h_of_compact_support ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.variational_identity_at_v_h_of_compact_support


omit [NeZero (Module.finrank ℝ E)] in
theorem variational_identity_v_h_expanded_of_compact_support
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weakPartial i y *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.uChart z) y)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.uChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.fChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
  variational_identity_at_v_h_of_compact_support (I := I) (M := M) D
    hK_0_compact hη hη_support hη_support_in_K_0 k hh hh_le h_thick

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.variational_identity_v_h_expanded_of_compact_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.variational_identity_v_h_expanded_of_compact_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.variational_identity_v_h_expanded_of_compact_support ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.variational_identity_v_h_expanded_of_compact_support

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuot_weightedInvGram_weak_partial_expand
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} (α : M)
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E)) (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (j : Fin (Module.finrank ℝ E)) (y : EuclN) :
    DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
          D.weakPartial i z) y =
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial i) y +
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
        D.weakPartial i y :=
  DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_coeff_apply
    (d := Module.finrank ℝ E) k h
    (fun z => weightedInvGramOnEuclid (I := I) g α i j z) (D.weakPartial i) y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.diffQuot_weightedInvGram_weak_partial_expand
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.diffQuot_weightedInvGram_weak_partial_expand target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eta_sq_factor_zero_outside_tsupport
    {η : EuclN → ℝ} (A : EuclN → ℝ) {z : EuclN} (hz : z ∉ tsupport η) :
    (η z)^2 * A z = 0 := by
  have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
  rw [show (η z)^2 = 0 from by rw [hηz]; ring, _root_.MulZeroClass.zero_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.eta_sq_factor_zero_outside_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.eta_sq_factor_zero_outside_tsupport target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma two_eta_partial_factor_zero_outside_tsupport
    {η : EuclN → ℝ} (j : Fin (Module.finrank ℝ E))
    (B A : EuclN → ℝ) {z : EuclN} (hz : z ∉ tsupport η) :
    2 * B z * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) * A z = 0 := by
  have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
  rw [show (η z) = 0 from hηz]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.two_eta_partial_factor_zero_outside_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.two_eta_partial_factor_zero_outside_tsupport target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma integral_cthickening_eq_integral_K_0
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {h : ℝ}
    {η : EuclN → ℝ} (hη_support_in_K_0 : tsupport η ⊆ K_0)
    {f : EuclN → ℝ}
    (hf_zero_outside_tsupport : ∀ y, y ∉ tsupport η → f y = 0) :
    ∫ y in Metric.cthickening |h| K_0, f y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ∫ y in K_0, f y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact
  have h_thick_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
    h_thick_compact.measurableSet
  have hK_0_meas : MeasurableSet K_0 :=
    hK_0_compact.isClosed.measurableSet
  have hK_0_in_thick : K_0 ⊆ Metric.cthickening |h| K_0 :=
    Metric.self_subset_cthickening _
  have h_zero_outside_K_0 : ∀ y, y ∉ K_0 → f y = 0 := by
    intro y hy_not_K_0
    apply hf_zero_outside_tsupport
    intro hy_in_tsupp
    exact hy_not_K_0 (hη_support_in_K_0 hy_in_tsupp)
  have h_indicator_eq : (Metric.cthickening |h| K_0).indicator f =
      K_0.indicator f := by
    funext y
    by_cases hy_K_0 : y ∈ K_0
    · have hy_thick : y ∈ Metric.cthickening |h| K_0 := hK_0_in_thick hy_K_0
      rw [Set.indicator_of_mem hy_thick, Set.indicator_of_mem hy_K_0]
    · rw [Set.indicator_of_notMem hy_K_0]
      have hfy : f y = 0 := h_zero_outside_K_0 y hy_K_0
      by_cases hy_thick : y ∈ Metric.cthickening |h| K_0
      · rw [Set.indicator_of_mem hy_thick, hfy]
      · rw [Set.indicator_of_notMem hy_thick]
  have h_lhs_eq : ∫ y in Metric.cthickening |h| K_0, f y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ∫ y, (Metric.cthickening |h| K_0).indicator f y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    (MeasureTheory.integral_indicator h_thick_meas).symm
  have h_rhs_eq : ∫ y in K_0, f y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ∫ y, K_0.indicator f y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    (MeasureTheory.integral_indicator hK_0_meas).symm
  rw [h_lhs_eq, h_rhs_eq, h_indicator_eq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.integral_cthickening_eq_integral_K_0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.integral_cthickening_eq_integral_K_0 target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_uniform_bound_continuous_compactSupport
    {f : EuclN → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  classical
  by_cases hSupport_empty : (tsupport f).Nonempty
  · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
      hf_cs.exists_isMaxOn hSupport_empty hf_cont.abs.continuousOn
    refine ⟨|f xMax|, abs_nonneg _, ?_⟩
    intro x
    by_cases hx : x ∈ tsupport f
    · exact hxMax_max hx
    · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hfx, abs_zero]; exact abs_nonneg _
  · refine ⟨0, le_refl _, ?_⟩
    intro x
    by_cases hx : x ∈ tsupport f
    · exact absurd ⟨x, hx⟩ hSupport_empty
    · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hfx, abs_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.exists_uniform_bound_continuous_compactSupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.exists_uniform_bound_continuous_compactSupport target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_uniform_bound_on_compact
    {f : EuclN → ℝ} {K : Set EuclN} (hf_cont : ContinuousOn f K)
    (hK_compact : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |f x| ≤ M := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, le_refl _, ?_⟩
    intro x hx
    rw [hK_empty] at hx
    exact absurd hx (Set.notMem_empty x)
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_abs_cont : ContinuousOn (fun x => |f x|) K := hf_cont.abs
  obtain ⟨xMax, _hxMax_in, h_max_eq⟩ := hK_compact.exists_isMaxOn hKne h_abs_cont
  refine ⟨|f xMax|, abs_nonneg _, fun x hx => h_max_eq hx⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.exists_uniform_bound_on_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.exists_uniform_bound_on_compact target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma weakPartial_memLp_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (D.weakPartial i) 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) :=
  D.weak_partial_locally_memLp i K_0 hK_0_compact hK_0_in

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.weakPartial_memLp_K_0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.weakPartial_memLp_K_0 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuot_weakPartial_memLp_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    _root_.MeasureTheory.MemLp (DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h (D.weakPartial i)) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := by
  classical
  set wp_i_ext : EuclN → ℝ :=
    (Metric.cthickening |h| K_0).indicator (D.weakPartial i) with hwp_i_ext_def
  have hwp_i_ext_lp : _root_.MeasureTheory.MemLp wp_i_ext 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    weakPartial_indicator_memLp (I := I) (M := M) D hK_0_compact h_thick i
  have hdq_wp_i_ext_lp : _root_.MeasureTheory.MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h wp_i_ext) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    memLp_diffQuot_of_memLp_local hwp_i_ext_lp k hh
  have hdq_wp_i_ext_lp_restrict : _root_.MeasureTheory.MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h wp_i_ext) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) :=
    hdq_wp_i_ext_lp.restrict K_0
  have h_pt_eq : ∀ y ∈ K_0,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial i) y =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h wp_i_ext y := by
    intro y hy_K_0
    have hy_thick : y ∈ Metric.cthickening |h| K_0 :=
      Metric.self_subset_cthickening _ hy_K_0
    have hy_shift : y + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| K_0 := by
      refine Metric.mem_cthickening_of_dist_le _ y |h| K_0 hy_K_0 ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      simp [Real.norm_eq_abs]
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh]
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh]
    change (D.weakPartial i (y + h • EuclideanSpace.single k 1) -
        D.weakPartial i y) / h =
      (wp_i_ext (y + h • EuclideanSpace.single k 1) - wp_i_ext y) / h
    rw [show wp_i_ext (y + h • EuclideanSpace.single k 1) =
        D.weakPartial i (y + h • EuclideanSpace.single k 1) from
        Set.indicator_of_mem hy_shift _,
      show wp_i_ext y = D.weakPartial i y from
        Set.indicator_of_mem hy_thick _]
  have hK_0_meas : MeasurableSet K_0 := hK_0_compact.isClosed.measurableSet
  have h_ae_eq :
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h wp_i_ext =ᵐ[
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0]
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial i) := by
    refine (MeasureTheory.ae_restrict_iff' hK_0_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact (h_pt_eq y hy).symm
  exact MemLp.ae_eq h_ae_eq hdq_wp_i_ext_lp_restrict

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.diffQuot_weakPartial_memLp_K_0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.diffQuot_weakPartial_memLp_K_0 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuot_uChart_memLp_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    _root_.MeasureTheory.MemLp (DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h D.uChart) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := by
  classical
  set u_ext : EuclN → ℝ :=
    (Metric.cthickening |h| K_0).indicator D.uChart with hu_ext_def
  have hu_ext_lp : _root_.MeasureTheory.MemLp u_ext 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    uChart_indicator_memLp (I := I) (M := M) D hK_0_compact h_thick
  have hdq_u_ext_lp : _root_.MeasureTheory.MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_ext) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    memLp_diffQuot_of_memLp_local hu_ext_lp k hh
  have hdq_u_ext_lp_restrict : _root_.MeasureTheory.MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_ext) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) :=
    hdq_u_ext_lp.restrict K_0
  have h_pt_eq : ∀ y ∈ K_0,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart y =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_ext y := by
    intro y hy_K_0
    have hy_thick : y ∈ Metric.cthickening |h| K_0 :=
      Metric.self_subset_cthickening _ hy_K_0
    have hy_shift : y + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| K_0 := by
      refine Metric.mem_cthickening_of_dist_le _ y |h| K_0 hy_K_0 ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      simp [Real.norm_eq_abs]
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh]
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh]
    change (D.uChart (y + h • EuclideanSpace.single k 1) - D.uChart y) / h =
      (u_ext (y + h • EuclideanSpace.single k 1) - u_ext y) / h
    rw [show u_ext (y + h • EuclideanSpace.single k 1) =
        D.uChart (y + h • EuclideanSpace.single k 1) from
        Set.indicator_of_mem hy_shift _,
      show u_ext y = D.uChart y from
        Set.indicator_of_mem hy_thick _]
  have hK_0_meas : MeasurableSet K_0 := hK_0_compact.isClosed.measurableSet
  have h_ae_eq :
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_ext =ᵐ[
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0]
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart := by
    refine (MeasureTheory.ae_restrict_iff' hK_0_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact (h_pt_eq y hy).symm
  exact MemLp.ae_eq h_ae_eq hdq_u_ext_lp_restrict

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.diffQuot_uChart_memLp_K_0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.diffQuot_uChart_memLp_K_0 target :: scope.openDecls } }


omit [NeZero (Module.finrank ℝ E)] in
private lemma translate_weightedInvGramOnEuclid_continuousOn_K_0
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (_hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ContinuousOn (DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h
      (fun y => weightedInvGramOnEuclid (I := I) g α i j y)) K_0 := by
  classical
  have h_w_cont : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have h_translate_cont : Continuous
      (fun y : EuclN => y + h • EuclideanSpace.single k 1) :=
    continuous_id.add continuous_const
  have h_maps : _root_.Set.MapsTo (fun y : EuclN => y + h • EuclideanSpace.single k 1) K_0
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro y hy_K_0
    have h_in_thick : y + h • EuclideanSpace.single k 1 ∈
        Metric.cthickening |h| K_0 := by
      refine Metric.mem_cthickening_of_dist_le _ y |h| K_0 hy_K_0 ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      simp [Real.norm_eq_abs]
    exact h_thick h_in_thick
  exact h_w_cont.comp h_translate_cont.continuousOn h_maps

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.translate_weightedInvGramOnEuclid_continuousOn_K_0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.translate_weightedInvGramOnEuclid_continuousOn_K_0 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuot_weightedInvGramOnEuclid_continuousOn_K_0
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ContinuousOn (DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h
      (fun y => weightedInvGramOnEuclid (I := I) g α i j y)) K_0 := by
  classical
  by_cases hh : h = 0
  · subst hh
    have h_dq_zero : DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0
        (fun y => weightedInvGramOnEuclid (I := I) g α i j y) =
        (fun _ : EuclN => (0 : ℝ)) := by
      funext x
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    rw [h_dq_zero]
    exact continuousOn_const
  have h_dq_eq : DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h
      (fun y => weightedInvGramOnEuclid (I := I) g α i j y) =
      fun y => (weightedInvGramOnEuclid (I := I) g α i j
        (y + h • EuclideanSpace.single k 1) -
        weightedInvGramOnEuclid (I := I) g α i j y) / h := by
    funext y
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh]
  rw [h_dq_eq]
  have h_translate_cont :=
    translate_weightedInvGramOnEuclid_continuousOn_K_0 (I := I) (M := M)
      g α i j (k := k) (h := h) hh_le h_thick
  have h_w_cont : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro y hy
    exact h_thick (Metric.self_subset_cthickening _ hy)
  have h_w_cont_K_0 : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j) K_0 :=
    h_w_cont.mono hK_0_in
  exact (h_translate_cont.sub h_w_cont_K_0).div_const h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.diffQuot_weightedInvGramOnEuclid_continuousOn_K_0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.diffQuot_weightedInvGramOnEuclid_continuousOn_K_0 target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma integrable_bdd_bdd_L2_L2
    {c bdd_factor F1 F2 : EuclN → ℝ}
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (h_c_cont : ContinuousOn c K_0)
    (h_bdd_cont : Continuous bdd_factor)
    (hF1_lp : _root_.MeasureTheory.MemLp F1 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0))
    (hF2_lp : _root_.MeasureTheory.MemLp F2 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0)) :
    _root_.MeasureTheory.Integrable (fun y => c y * bdd_factor y * F1 y * F2 y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := by
  classical
  let _ : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := by
    constructor
    rw [show (1 : ℝ≥0∞)⁻¹ = 1 from inv_one]
    rw [ENNReal.inv_two_add_inv_two]
  have hK_0_meas : MeasurableSet K_0 := hK_0_compact.isClosed.measurableSet
  obtain ⟨M_c, _hM_c_nn, hM_c_bd⟩ :=
    exists_uniform_bound_on_compact h_c_cont hK_0_compact
  obtain ⟨M_b, _hM_b_nn, hM_b_bd⟩ :=
    exists_uniform_bound_on_compact h_bdd_cont.continuousOn hK_0_compact
  have h_F1F2_int : _root_.MeasureTheory.Integrable (fun y => F1 y * F2 y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := by
    have h := MemLp.integrable_mul (μ :=
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0)
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) hF1_lp hF2_lp
    exact h.congr (Filter.Eventually.of_forall fun _ ↦ rfl)
  have h_bdd_aesm : _root_.MeasureTheory.AEStronglyMeasurable bdd_factor
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) :=
    h_bdd_cont.aestronglyMeasurable.mono_measure
      (MeasureTheory.Measure.restrict_le_self)
  have h_c_aesm : _root_.MeasureTheory.AEStronglyMeasurable c
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) :=
    h_c_cont.aestronglyMeasurable_of_isCompact hK_0_compact hK_0_meas
  have h_c_b_aesm : _root_.MeasureTheory.AEStronglyMeasurable (fun y => c y * bdd_factor y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) :=
    h_c_aesm.mul h_bdd_aesm
  have h_c_b_bound : ∀ᵐ y ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0),
      ‖c y * bdd_factor y‖ ≤ M_c * M_b := by
    rw [_root_.MeasureTheory.ae_restrict_iff' hK_0_meas]
    refine Filter.Eventually.of_forall ?_
    intro y hy
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hM_c_bd y hy) (hM_b_bd y (by trivial))
      (abs_nonneg _) (le_trans (abs_nonneg _) (hM_c_bd y hy))
  have h_combine : _root_.MeasureTheory.Integrable (fun y =>
      c y * bdd_factor y * (F1 y * F2 y))
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) :=
    h_F1F2_int.bdd_mul h_c_b_aesm h_c_b_bound
  have h_eq : (fun y => c y * bdd_factor y * F1 y * F2 y) =
      (fun y => c y * bdd_factor y * (F1 y * F2 y)) := by
    funext y; ring
  rw [h_eq]
  exact h_combine

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.integrable_bdd_bdd_L2_L2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.integrable_bdd_bdd_L2_L2 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma translatedCoeff_cutoffSq_diffQuotPartial_diffQuotPartial_integrable_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.Integrable (fun y =>
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial j) y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := by
  have h_τw_cont := translate_weightedInvGramOnEuclid_continuousOn_K_0
    (I := I) (M := M) g α i j (k := k) (h := h) hh_le h_thick
  have hη_sq_cont : Continuous (fun y : EuclN => (η y) ^ 2) :=
    hη.continuous.pow 2
  have hdq_wp_i_lp := diffQuot_weakPartial_memLp_K_0 (I := I) (M := M) D i
    hK_0_compact k hh h_thick
  have hdq_wp_j_lp := diffQuot_weakPartial_memLp_K_0 (I := I) (M := M) D j
    hK_0_compact k hh h_thick
  exact integrable_bdd_bdd_L2_L2 hK_0_compact h_τw_cont hη_sq_cont
    hdq_wp_i_lp hdq_wp_j_lp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.translatedCoeff_cutoffSq_diffQuotPartial_diffQuotPartial_integrable_K_0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.translatedCoeff_cutoffSq_diffQuotPartial_diffQuotPartial_integrable_K_0 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma translatedCoeff_cutoffDeriv_diffQuotPartial_diffQuotUChart_integrable_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.Integrable (fun y =>
      2 *
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := by
  classical
  have h_τw_cont := translate_weightedInvGramOnEuclid_continuousOn_K_0
    (I := I) (M := M) g α i j (k := k) (h := h) hh_le h_thick
  have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  have hη_factor_cont : Continuous (fun y : EuclN =>
      (2 : ℝ) * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    (continuous_const.mul hη.continuous).mul
      ((hη.continuous_fderiv h_top_ne_zero).clm_apply continuous_const)
  have hdq_wp_i_lp := diffQuot_weakPartial_memLp_K_0 (I := I) (M := M) D i
    hK_0_compact k hh h_thick
  have hdq_u_lp := diffQuot_uChart_memLp_K_0 (I := I) (M := M) D
    hK_0_compact k hh h_thick
  have h_int := integrable_bdd_bdd_L2_L2 hK_0_compact h_τw_cont hη_factor_cont
    hdq_wp_i_lp hdq_u_lp
  have h_eq : (fun y =>
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      ((2 : ℝ) * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart y) =
    (fun y =>
      2 *
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart y) := by
    funext y; ring
  rw [← h_eq]
  exact h_int

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.translatedCoeff_cutoffDeriv_diffQuotPartial_diffQuotUChart_integrable_K_0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.translatedCoeff_cutoffDeriv_diffQuotPartial_diffQuotUChart_integrable_K_0 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuotCoeff_cutoffSq_partial_diffQuotPartial_integrable_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.Integrable (fun y =>
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      D.weakPartial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial j) y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := by
  have h_dqw_cont := diffQuot_weightedInvGramOnEuclid_continuousOn_K_0
    (I := I) (M := M) g α i j (k := k) (h := h) hh_le h_thick
  have hη_sq_cont : Continuous (fun y : EuclN => (η y) ^ 2) :=
    hη.continuous.pow 2
  have hwp_i_lp := weakPartial_memLp_K_0 (I := I) (M := M) D i
    hK_0_compact hK_0_in
  have hdq_wp_j_lp := diffQuot_weakPartial_memLp_K_0 (I := I) (M := M) D j
    hK_0_compact k hh h_thick
  exact integrable_bdd_bdd_L2_L2 hK_0_compact h_dqw_cont hη_sq_cont
    hwp_i_lp hdq_wp_j_lp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.diffQuotCoeff_cutoffSq_partial_diffQuotPartial_integrable_K_0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.diffQuotCoeff_cutoffSq_partial_diffQuotPartial_integrable_K_0 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuotCoeff_cutoffDeriv_partial_diffQuotUChart_integrable_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.Integrable (fun y =>
      2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      D.weakPartial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := by
  classical
  have h_dqw_cont := diffQuot_weightedInvGramOnEuclid_continuousOn_K_0
    (I := I) (M := M) g α i j (k := k) (h := h) hh_le h_thick
  have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  have hη_factor_cont : Continuous (fun y : EuclN =>
      (2 : ℝ) * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    (continuous_const.mul hη.continuous).mul
      ((hη.continuous_fderiv h_top_ne_zero).clm_apply continuous_const)
  have hwp_i_lp := weakPartial_memLp_K_0 (I := I) (M := M) D i
    hK_0_compact hK_0_in
  have hdq_u_lp := diffQuot_uChart_memLp_K_0 (I := I) (M := M) D
    hK_0_compact k hh h_thick
  have h_int := integrable_bdd_bdd_L2_L2 hK_0_compact h_dqw_cont hη_factor_cont
    hwp_i_lp hdq_u_lp
  have h_eq : (fun y =>
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      ((2 : ℝ) * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      D.weakPartial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart y) =
    (fun y =>
      2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      D.weakPartial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart y) := by
    funext y; ring
  rw [← h_eq]
  exact h_int

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.diffQuotCoeff_cutoffDeriv_partial_diffQuotUChart_integrable_K_0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.diffQuotCoeff_cutoffDeriv_partial_diffQuotUChart_integrable_K_0 target :: scope.openDecls } }


omit [NeZero (Module.finrank ℝ E)] in
private lemma principal_post_ibp_integral_eq_symbolic
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (_hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                D.weakPartial i z) y *
            ((η y) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
              2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart y))
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      principalTermChartBilinear (I := I) (M := M) D K_0 η k h
        + cross1TermChartBilinear (I := I) (M := M) D K_0 η k h
        + cross2TermChartBilinear (I := I) (M := M) D K_0 η k h
        + cross3TermChartBilinear (I := I) (M := M) D K_0 η k h := by
  classical
  set T1 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j y => DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h
      (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial j) y with hT1_def
  set T2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j y => 2 *
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart y with hT2_def
  set T3 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j y => DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h
      (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      D.weakPartial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial j) y with hT3_def
  set T4 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j y => 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      D.weakPartial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart y with hT4_def
  set LHS_ij : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j y => DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
          D.weakPartial i z) y *
      ((η y) ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart y) with hLHS_def
  have h_pointwise_expand : ∀ i j y,
      LHS_ij i j y = T1 i j y + T2 i j y + T3 i j y + T4 i j y := by
    intro i j y
    change DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
          D.weakPartial i z) y *
      ((η y) ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart y) =
      T1 i j y + T2 i j y + T3 i j y + T4 i j y
    rw [diffQuot_weightedInvGram_weak_partial_expand (I := I) (M := M)
      α D i k h j y]
    change (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial i) y +
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
        D.weakPartial i y) *
      ((η y) ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart y) =
      (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial j) y) +
      (2 *
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart y) +
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      D.weakPartial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial j) y) +
      (2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      D.weakPartial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart y)
    ring
  have h_sum_expand : ∀ y, (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), LHS_ij i j y) =
      (∑ i, ∑ j, T1 i j y) + (∑ i, ∑ j, T2 i j y) +
      (∑ i, ∑ j, T3 i j y) + (∑ i, ∑ j, T4 i j y) := by
    intro y
    have h_per_ij : ∀ i, (∑ j : Fin (Module.finrank ℝ E), LHS_ij i j y) =
        (∑ j, T1 i j y) + (∑ j, T2 i j y) + (∑ j, T3 i j y) + (∑ j, T4 i j y) := by
      intro i
      rw [show (fun (j : Fin (Module.finrank ℝ E)) => LHS_ij i j y) =
          (fun j => T1 i j y + T2 i j y + T3 i j y + T4 i j y) from
          funext (fun j => h_pointwise_expand i j y)]
      simp [Finset.sum_add_distrib]
    rw [show (fun (i : Fin (Module.finrank ℝ E)) =>
        ∑ j : Fin (Module.finrank ℝ E), LHS_ij i j y) =
        (fun i => (∑ j, T1 i j y) + (∑ j, T2 i j y) +
          (∑ j, T3 i j y) + (∑ j, T4 i j y)) from
        funext h_per_ij]
    simp [Finset.sum_add_distrib]
  have h_int_expand :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E), LHS_ij i j y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ∫ y in Metric.cthickening |h| K_0,
          ((∑ i, ∑ j, T1 i j y) + (∑ i, ∑ j, T2 i j y) +
          (∑ i, ∑ j, T3 i j y) + (∑ i, ∑ j, T4 i j y))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    refine _root_.MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    exact h_sum_expand y
  have h_T_zero : ∀ y ∉ tsupport η,
      ((∑ i, ∑ j, T1 i j y) + (∑ i, ∑ j, T2 i j y) +
      (∑ i, ∑ j, T3 i j y) + (∑ i, ∑ j, T4 i j y)) = 0 := by
    intro y hy
    have hηy : η y = 0 := image_eq_zero_of_notMem_tsupport hy
    have h1 : ∀ i j, T1 i j y = 0 := by
      intro i j
      change DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial j) y = 0
      rw [show (η y) ^ 2 = 0 from by rw [hηy]; ring]
      ring
    have h2 : ∀ i j, T2 i j y = 0 := by
      intro i j
      change 2 *
        DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h
          (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
        η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial i) y *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.uChart y = 0
      rw [show η y = 0 from hηy]
      ring
    have h3 : ∀ i j, T3 i j y = 0 := by
      intro i j
      change DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      D.weakPartial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial j) y = 0
      rw [show (η y) ^ 2 = 0 from by rw [hηy]; ring]
      ring
    have h4 : ∀ i j, T4 i j y = 0 := by
      intro i j
      change 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
        η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
        D.weakPartial i y *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.uChart y = 0
      rw [show η y = 0 from hηy]
      ring
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T1 i j y) = 0 from by
        apply Finset.sum_eq_zero; intros i _
        apply Finset.sum_eq_zero; intros j _
        exact h1 i j]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T2 i j y) = 0 from by
        apply Finset.sum_eq_zero; intros i _
        apply Finset.sum_eq_zero; intros j _
        exact h2 i j]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T3 i j y) = 0 from by
        apply Finset.sum_eq_zero; intros i _
        apply Finset.sum_eq_zero; intros j _
        exact h3 i j]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T4 i j y) = 0 from by
        apply Finset.sum_eq_zero; intros i _
        apply Finset.sum_eq_zero; intros j _
        exact h4 i j]
    ring
  have h_thick_to_K_0 :
      ∫ y in Metric.cthickening |h| K_0,
          ((∑ i, ∑ j, T1 i j y) + (∑ i, ∑ j, T2 i j y) +
          (∑ i, ∑ j, T3 i j y) + (∑ i, ∑ j, T4 i j y))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ∫ y in K_0,
          ((∑ i, ∑ j, T1 i j y) + (∑ i, ∑ j, T2 i j y) +
          (∑ i, ∑ j, T3 i j y) + (∑ i, ∑ j, T4 i j y))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    integral_cthickening_eq_integral_K_0 (E := E) hK_0_compact
      hη_support_in_K_0 h_T_zero
  have hT1_ij_int : ∀ i j, _root_.MeasureTheory.Integrable (T1 i j)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := fun i j =>
    translatedCoeff_cutoffSq_diffQuotPartial_diffQuotPartial_integrable_K_0 (I := I) (M := M) D
      hK_0_compact hη k hh hh_le
      h_thick i j
  have hT2_ij_int : ∀ i j, _root_.MeasureTheory.Integrable (T2 i j)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := fun i j =>
    translatedCoeff_cutoffDeriv_diffQuotPartial_diffQuotUChart_integrable_K_0 (I := I) (M := M) D
      hK_0_compact hη k hh hh_le
      h_thick i j
  have hT3_ij_int : ∀ i j, _root_.MeasureTheory.Integrable (T3 i j)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := fun i j =>
    diffQuotCoeff_cutoffSq_partial_diffQuotPartial_integrable_K_0 (I := I) (M := M) D hK_0_compact
      hK_0_in hη k hh hh_le
      h_thick i j
  have hT4_ij_int : ∀ i j, _root_.MeasureTheory.Integrable (T4 i j)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := fun i j =>
    diffQuotCoeff_cutoffDeriv_partial_diffQuotUChart_integrable_K_0 (I := I) (M := M) D hK_0_compact
      hK_0_in hη k hh hh_le
      h_thick i j
  have hT1_sum_int : _root_.MeasureTheory.Integrable (fun y => ∑ i, ∑ j, T1 i j y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := by
    refine _root_.MeasureTheory.integrable_finsetSum _ ?_
    intro i _
    exact _root_.MeasureTheory.integrable_finsetSum _ (fun j _ => hT1_ij_int i j)
  have hT2_sum_int : _root_.MeasureTheory.Integrable (fun y => ∑ i, ∑ j, T2 i j y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := by
    refine _root_.MeasureTheory.integrable_finsetSum _ ?_
    intro i _
    exact _root_.MeasureTheory.integrable_finsetSum _ (fun j _ => hT2_ij_int i j)
  have hT3_sum_int : _root_.MeasureTheory.Integrable (fun y => ∑ i, ∑ j, T3 i j y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := by
    refine _root_.MeasureTheory.integrable_finsetSum _ ?_
    intro i _
    exact _root_.MeasureTheory.integrable_finsetSum _ (fun j _ => hT3_ij_int i j)
  have hT4_sum_int : _root_.MeasureTheory.Integrable (fun y => ∑ i, ∑ j, T4 i j y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) := by
    refine _root_.MeasureTheory.integrable_finsetSum _ ?_
    intro i _
    exact _root_.MeasureTheory.integrable_finsetSum _ (fun j _ => hT4_ij_int i j)
  have h_split :
      ∫ y in K_0,
          ((∑ i, ∑ j, T1 i j y) + (∑ i, ∑ j, T2 i j y) +
          (∑ i, ∑ j, T3 i j y) + (∑ i, ∑ j, T4 i j y))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ∫ y in K_0, (∑ i, ∑ j, T1 i j y) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) +
      ∫ y in K_0, (∑ i, ∑ j, T2 i j y) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) +
      ∫ y in K_0, (∑ i, ∑ j, T3 i j y) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) +
      ∫ y in K_0, (∑ i, ∑ j, T4 i j y) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    have hT12_int : _root_.MeasureTheory.Integrable (fun y => (∑ i, ∑ j, T1 i j y) +
        (∑ i, ∑ j, T2 i j y)) ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) :=
      hT1_sum_int.add hT2_sum_int
    have hT123_int : _root_.MeasureTheory.Integrable (fun y => (∑ i, ∑ j, T1 i j y) +
        (∑ i, ∑ j, T2 i j y) + (∑ i, ∑ j, T3 i j y))
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0) :=
      hT12_int.add hT3_sum_int
    rw [_root_.MeasureTheory.integral_add hT123_int hT4_sum_int]
    rw [_root_.MeasureTheory.integral_add hT12_int hT3_sum_int]
    rw [_root_.MeasureTheory.integral_add hT1_sum_int hT2_sum_int]
  have h_principalTerm : ∫ y in K_0, (∑ i, ∑ j, T1 i j y)
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      principalTermChartBilinear (I := I) (M := M) D K_0 η k h := by
    rfl
  have h_cross1 : ∫ y in K_0, (∑ i, ∑ j, T2 i j y)
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      cross1TermChartBilinear (I := I) (M := M) D K_0 η k h := by
    rw [show (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), T2 i j y) =
        (fun y => ∑ i : Fin (Module.finrank ℝ E),
          (fun y' => ∑ j : Fin (Module.finrank ℝ E), T2 i j y') y) from rfl]
    rw [_root_.MeasureTheory.integral_finsetSum _ (fun i _ =>
      _root_.MeasureTheory.integrable_finsetSum _ (fun j _ => hT2_ij_int i j))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [show (fun y' : EuclN => ∑ j : Fin (Module.finrank ℝ E), T2 i j y') =
        (fun y' => ∑ j : Fin (Module.finrank ℝ E), (fun y'' => T2 i j y'') y')
        from rfl]
    rw [_root_.MeasureTheory.integral_finsetSum _ (fun j _ => hT2_ij_int i j)]
  have h_cross2 : ∫ y in K_0, (∑ i, ∑ j, T3 i j y)
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      cross2TermChartBilinear (I := I) (M := M) D K_0 η k h := by
    rw [show (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), T3 i j y) =
        (fun y => ∑ i : Fin (Module.finrank ℝ E),
          (fun y' => ∑ j : Fin (Module.finrank ℝ E), T3 i j y') y) from rfl]
    rw [_root_.MeasureTheory.integral_finsetSum _ (fun i _ =>
      _root_.MeasureTheory.integrable_finsetSum _ (fun j _ => hT3_ij_int i j))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [show (fun y' : EuclN => ∑ j : Fin (Module.finrank ℝ E), T3 i j y') =
        (fun y' => ∑ j : Fin (Module.finrank ℝ E), (fun y'' => T3 i j y'') y')
        from rfl]
    rw [_root_.MeasureTheory.integral_finsetSum _ (fun j _ => hT3_ij_int i j)]
  have h_cross3 : ∫ y in K_0, (∑ i, ∑ j, T4 i j y)
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      cross3TermChartBilinear (I := I) (M := M) D K_0 η k h := by
    rw [show (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), T4 i j y) =
        (fun y => ∑ i : Fin (Module.finrank ℝ E),
          (fun y' => ∑ j : Fin (Module.finrank ℝ E), T4 i j y') y) from rfl]
    rw [_root_.MeasureTheory.integral_finsetSum _ (fun i _ =>
      _root_.MeasureTheory.integrable_finsetSum _ (fun j _ => hT4_ij_int i j))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [show (fun y' : EuclN => ∑ j : Fin (Module.finrank ℝ E), T4 i j y') =
        (fun y' => ∑ j : Fin (Module.finrank ℝ E), (fun y'' => T4 i j y'') y')
        from rfl]
    rw [_root_.MeasureTheory.integral_finsetSum _ (fun j _ => hT4_ij_int i j)]
  rw [h_int_expand, h_thick_to_K_0, h_split, h_principalTerm, h_cross1,
    h_cross2, h_cross3]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.principal_post_ibp_integral_eq_symbolic
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.principal_post_ibp_integral_eq_symbolic target :: scope.openDecls } }


omit [NeZero (Module.finrank ℝ E)] in
theorem variational_identity_after_product_rule_of_compact_support
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    principalTermChartBilinear (I := I) (M := M) D K_0 η k h
      + cross1TermChartBilinear (I := I) (M := M) D K_0 η k h
      + cross2TermChartBilinear (I := I) (M := M) D K_0 η k h
      + cross3TermChartBilinear (I := I) (M := M) D K_0 η k h
      + fTermChartBilinear (I := I) (M := M) D K_0 η k h
      = cTermChartBilinear (I := I) (M := M) D K_0 η k h := by
  classical
  have h_after_ibp_eq :=
    variational_identity_after_ibp_of_compact_support (I := I) (M := M) D
      hK_0_compact hη hη_support hη_support_in_K_0 k hh h_thick
      (variational_identity_v_h_expanded_of_compact_support (I := I) (M := M) D
        hK_0_compact hη hη_support hη_support_in_K_0 k hh hh_le h_thick)
  have h_principal_in_K_0_eq :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weakPartial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.uChart y))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      principalTermChartBilinear (I := I) (M := M) D K_0 η k h
        + cross1TermChartBilinear (I := I) (M := M) D K_0 η k h
        + cross2TermChartBilinear (I := I) (M := M) D K_0 η k h
        + cross3TermChartBilinear (I := I) (M := M) D K_0 η k h :=
    principal_post_ibp_integral_eq_symbolic (I := I) (M := M) D
      hK_0_compact hK_0_in hη hη_support hη_support_in_K_0 k hh hh_le h_thick
  have h_c_term_eq :
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.uChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      cTermChartBilinear (I := I) (M := M) D K_0 η k h := rfl
  have h_f_term_eq :
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.fChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      fTermChartBilinear (I := I) (M := M) D K_0 η k h := rfl
  exact variational_identity_after_product_rule (I := I) (M := M) D
    k h_after_ibp_eq h_principal_in_K_0_eq h_c_term_eq h_f_term_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.variational_identity_after_product_rule_of_compact_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.variational_identity_after_product_rule_of_compact_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.variational_identity_after_product_rule_of_compact_support ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.variational_identity_after_product_rule_of_compact_support

omit [NeZero (Module.finrank ℝ E)] in
theorem chartBilinear_substitution_identity_holds
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    chartBilinearLHS (I := I) (M := M) D K_0 η k h =
    chartBilinearRHS (I := I) (M := M) D K_0 η k h := by
  unfold chartBilinearLHS chartBilinearRHS
  exact variational_identity_after_product_rule_of_compact_support (I := I) (M := M) D
    hK_0_compact hK_0_in hη hη_support hη_support_in_K_0 k hh hh_le h_thick

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.chartBilinear_substitution_identity_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.chartBilinear_substitution_identity_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.chartBilinear_substitution_identity_holds ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.chartBilinear_substitution_identity_holds

omit [NeZero (Module.finrank ℝ E)] in
theorem nirenberg_substitution_identity_chartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    (∫ x in K_0,
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.translate
              (d := Module.finrank ℝ E) k h
              (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
            (η x) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial i) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) x
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
    + (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ x in K_0,
            2 *
              DifferentialGeometry.Analysis.Sobolev.translate
                (d := Module.finrank ℝ E) k h
                (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
              (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart x
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
    + (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ x in K_0,
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
            (η x) ^ 2 *
            D.weakPartial i x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) x
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
    + (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ x in K_0,
            2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
              (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              D.weakPartial i x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart x
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
    + (∫ x in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α x * D.fChart x *
            nirenbergTestFunction
              (d := Module.finrank ℝ E) k h η D.uChart x
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
    = ∫ x in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α x * D.uChart x *
            nirenbergTestFunction
              (d := Module.finrank ℝ E) k h η D.uChart x
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  have h := chartBilinear_substitution_identity_holds (I := I) (M := M) D
    hK_0_compact hK_0_in hη hη_support hη_support_in_K_0 k hh hh_le h_thick
  unfold chartBilinearLHS chartBilinearRHS at h
  unfold principalTermChartBilinear cross1TermChartBilinear
    cross2TermChartBilinear cross3TermChartBilinear
    fTermChartBilinear cTermChartBilinear at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.nirenberg_substitution_identity_chartBilinear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.nirenberg_substitution_identity_chartBilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.nirenberg_substitution_identity_chartBilinear ``Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly.nirenberg_substitution_identity_chartBilinear

end SubstitutionDischargeAssembly
end Sobolev
end Analysis
end DifferentialGeometry
