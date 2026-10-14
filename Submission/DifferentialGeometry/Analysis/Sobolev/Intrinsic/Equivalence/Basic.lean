import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.Defs
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.MeasureComparison
import Submission.DifferentialGeometry.Geometry.Operator.DirectionalDerivative
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Equivalence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.EuclN
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.EuclN target :: scope.openDecls } }

private def chartPushedExt (α : M) (f : M → ℝ) : EuclN E → ℝ := by
  classical
  exact fun y =>
    if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma chartPushedExt_apply_of_mem_target
    (α : M) (f : M → ℝ) {y : EuclN E}
    (hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target) :
    chartPushedExt (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  rw [if_pos hy]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt_apply_of_mem_target
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt_apply_of_mem_target target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma chartPushedExt_apply_of_notMem_target
    (α : M) (f : M → ℝ) {y : EuclN E}
    (hy : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target) :
    chartPushedExt (I := I) (M := M) α f y = 0 := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = 0
  rw [if_neg hy]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt_apply_of_notMem_target
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt_apply_of_notMem_target target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma chartPushedExt_apply_of_mem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedExt (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  apply chartPushedExt_apply_of_mem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt_apply_of_mem_chartTargetEuclid
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt_apply_of_mem_chartTargetEuclid target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma chartPushedExt_apply_of_notMem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN E}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedExt (I := I) (M := M) α f y = 0 := by
  classical
  apply chartPushedExt_apply_of_notMem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt_apply_of_notMem_chartTargetEuclid
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt_apply_of_notMem_chartTargetEuclid target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma chartPushedExt_eq_chartPushed_on_target
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (α : M) (u : M → ℝ) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedExt (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y =
      chartPushed (I := I) (M := M) ρ α u y := by
  classical
  rw [chartPushedExt_apply_of_mem_chartTargetEuclid (I := I) (M := M) α _ hy]
  unfold chartPushed
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt_eq_chartPushed_on_target
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt_eq_chartPushed_on_target target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma image_toEuclidean_chart_tsupport_isCompact
    [CompactSpace M] {f : M → ℝ} {α : M}
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    IsCompact ((toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport f))) := by
  have hKE := image_extChartAt_tsupport_compact_subset_target
    (I := I) (M := M) (u := f) (α := α) hf_support
  exact hKE.1.image (toEuclidean (E := E)).continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.image_toEuclidean_chart_tsupport_isCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.image_toEuclidean_chart_tsupport_isCompact target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma image_toEuclidean_chart_tsupport_subset_chartTargetEuclid
    {f : M → ℝ} {α : M}
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
    (I := I) (M := M) (u := f) (α := α) hf_support

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.image_toEuclidean_chart_tsupport_subset_chartTargetEuclid
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.image_toEuclidean_chart_tsupport_subset_chartTargetEuclid target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma chartPushedExt_eq_zero_off_image_tsupport
    (α : M) {f : M → ℝ}
    (_hf_support : tsupport f ⊆ (chartAt H α).source) {y : EuclN E}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :
    chartPushedExt (I := I) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · obtain ⟨z, hz_target, hzy⟩ := hy_target
    have hy_target' : y ∈ chartTargetEuclid (I := I) (M := M) α := ⟨z, hz_target, hzy⟩
    have hsymm_source : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hz_target
    have hy_symm : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [chartPushedExt_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hy_target',
      hy_symm]
    by_contra hne
    apply hy_off
    have hsymm_in_support : (extChartAt I α).symm z ∈ tsupport f :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
      (extChartAt I α).right_inv hz_target
    refine ⟨z, ⟨(extChartAt I α).symm z, hsymm_in_support, hz_eq⟩, hzy⟩
  · exact chartPushedExt_apply_of_notMem_chartTargetEuclid (I := I) (M := M) α f hy_target

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt_eq_zero_off_image_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.chartPushedExt_eq_zero_off_image_tsupport target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma hasCompactSupport_chartPushedExt
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPushedExt (I := I) (M := M) α f) := by
  classical
  set K : Set (EuclN E) :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_chart_tsupport_isCompact
      (I := I) (M := M) (f := f) (α := α) hf_support
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_support
  by_contra hyK
  apply hy_support
  exact chartPushedExt_eq_zero_off_image_tsupport
    (I := I) (M := M) α (f := f) hf_support hyK

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.hasCompactSupport_chartPushedExt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.hasCompactSupport_chartPushedExt target :: scope.openDecls } }

private lemma contDiffOn_chartPushedExt_formula
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞
        (fun y : EuclN E =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hscalar : ContDiffOn ℝ ∞
      (fun y : E => f ((extChartAt I α).symm y))
      (extChartAt I α).target := by
    have h := scalarOnE_contDiffOn (I := I) α hf
    exact h
  have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
    ContinuousLinearEquiv.contDiff _
  have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hcomp := hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps
  exact hcomp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.contDiffOn_chartPushedExt_formula
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.contDiffOn_chartPushedExt_formula target :: scope.openDecls } }

private lemma contDiffAt_chartPushedExt_of_mem_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    [I.Boundaryless] {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (chartPushedExt (I := I) (M := M) α f) y := by
  classical
  have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hContDiffOn := contDiffOn_chartPushedExt_formula (I := I) (M := M) α hf
  have hContDiffAt_formula : ContDiffAt ℝ ∞
      (fun y : EuclN E => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) y := by
    have hwithin : ContDiffWithinAt ℝ ∞
        (fun y : EuclN E => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) y := hContDiffOn y hy
    exact hwithin.contDiffAt (hOpen.mem_nhds hy)
  apply hContDiffAt_formula.congr_of_eventuallyEq
  filter_upwards [hOpen.mem_nhds hy] with z hz
  rw [chartPushedExt_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hz]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.contDiffAt_chartPushedExt_of_mem_target
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.contDiffAt_chartPushedExt_of_mem_target target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma contDiffAt_chartPushedExt_of_notMem_image_tsupport_compact
    (α : M) {f : M → ℝ}
    (hf_support : tsupport f ⊆ (chartAt H α).source)
    (hf_compact : IsCompact (tsupport f)) {y : EuclN E}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :
    ContDiffAt ℝ ∞ (chartPushedExt (I := I) (M := M) α f) y := by
  classical
  set K : Set (EuclN E) :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K := by
    have hsub : tsupport f ⊆ (extChartAt I α).source := by
      intro x hx
      rw [extChartAt_source_eq_chartAt_source (I := I) (M := M)]
      exact hf_support hx
    have hcont : ContinuousOn (extChartAt I α) (tsupport f) :=
      (continuousOn_extChartAt α).mono hsub
    have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
      hf_compact.image_of_continuousOn hcont
    exact h1.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
  have hy_compl : y ∈ Kᶜ := hy_off
  apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclN E => (0 : ℝ)) contDiffAt_const
  filter_upwards [hK_compl_open.mem_nhds hy_compl] with z hz
  exact chartPushedExt_eq_zero_off_image_tsupport
    (I := I) (M := M) α (f := f) hf_support hz

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.contDiffAt_chartPushedExt_of_notMem_image_tsupport_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.contDiffAt_chartPushedExt_of_notMem_image_tsupport_compact target :: scope.openDecls } }

private lemma contDiff_chartPushedExt
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    [I.Boundaryless]
    (hf_support : tsupport f ⊆ (chartAt H α).source)
    (hf_compact : IsCompact (tsupport f)) :
    ContDiff ℝ ∞ (chartPushedExt (I := I) (M := M) α f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact contDiffAt_chartPushedExt_of_mem_target (I := I) (M := M) α hf hy_target
  · have hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) := by
      intro hy_in
      apply hy_target
      exact image_toEuclidean_chart_tsupport_subset_chartTargetEuclid
        (I := I) (M := M) (f := f) (α := α) hf_support hy_in
    exact contDiffAt_chartPushedExt_of_notMem_image_tsupport_compact
      (I := I) (M := M) α (f := f) hf_support hf_compact hy_off

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.contDiff_chartPushedExt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.contDiff_chartPushedExt target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma chartTargetEuclid_isOpen' [I.Boundaryless] (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
  chartTargetEuclid_isOpen (I := I) (M := M) α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.chartTargetEuclid_isOpen'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.chartTargetEuclid_isOpen' target :: scope.openDecls } }

private lemma memLp_chartPushedExt
    [CompactSpace M] [I.Boundaryless]
    (α : M) (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (p : ℝ≥0∞) :
    MemLp (chartPushedExt (I := I) (M := M) α
        (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x))
      p (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    ((ρ α : C^∞⟮I, M; ℝ⟯).contMDiff).mul hu
  have hf_support : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      apply tsupport_mul_subset_left
    exact h1.trans (hρ α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsmooth : ContDiff ℝ ∞ (chartPushedExt (I := I) (M := M) α f) :=
    contDiff_chartPushedExt (I := I) (M := M) α hf_smooth hf_support hf_compact
  have hcs : HasCompactSupport (chartPushedExt (I := I) (M := M) α f) :=
    hasCompactSupport_chartPushedExt (I := I) (M := M) α hf_support
  have hmemLp_global : _root_.MeasureTheory.MemLp (chartPushedExt (I := I) (M := M) α f) p volume :=
    hsmooth.continuous.memLp_of_hasCompactSupport hcs
  exact hmemLp_global.restrict _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.memLp_chartPushedExt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.memLp_chartPushedExt target :: scope.openDecls } }

private lemma fderiv_chartPushedExt_memLp
    [CompactSpace M] [I.Boundaryless]
    (α : M) (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (p : ℝ≥0∞)
    (i : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.MemLp (fun x : EuclN E =>
        (fderiv ℝ (chartPushedExt (I := I) (M := M) α
          (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) x)
          (EuclideanSpace.single i 1))
      p (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    ((ρ α : C^∞⟮I, M; ℝ⟯).contMDiff).mul hu
  have hf_support : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      apply tsupport_mul_subset_left
    exact h1.trans (hρ α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsmooth : ContDiff ℝ ∞ (chartPushedExt (I := I) (M := M) α f) :=
    contDiff_chartPushedExt (I := I) (M := M) α hf_smooth hf_support hf_compact
  have hcs : HasCompactSupport (chartPushedExt (I := I) (M := M) α f) :=
    hasCompactSupport_chartPushedExt (I := I) (M := M) α hf_support
  have hderiv_smooth : ContDiff ℝ ∞
      (fun x => (fderiv ℝ (chartPushedExt (I := I) (M := M) α f) x)
        (EuclideanSpace.single i 1)) :=
    (hsmooth.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
  have hderiv_cs : HasCompactSupport
      (fun x => (fderiv ℝ (chartPushedExt (I := I) (M := M) α f) x)
        (EuclideanSpace.single i 1)) :=
    hcs.fderiv_apply (𝕜 := ℝ) _
  have hmemLp_global : _root_.MeasureTheory.MemLp _ p volume :=
    hderiv_smooth.continuous.memLp_of_hasCompactSupport hderiv_cs
  exact hmemLp_global.restrict _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.fderiv_chartPushedExt_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.fderiv_chartPushedExt_memLp target :: scope.openDecls } }

private lemma memW1p_chartPushedExt
    [CompactSpace M] [I.Boundaryless]
    (α : M) (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) {p : ℝ≥0∞} (_hp : 1 ≤ p) :
    DeGiorgi.MemW1p p (chartPushedExt (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    ((ρ α : C^∞⟮I, M; ℝ⟯).contMDiff).mul hu
  have hf_support : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      apply tsupport_mul_subset_left
    exact h1.trans (hρ α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsmooth : ContDiff ℝ ∞ (chartPushedExt (I := I) (M := M) α f) :=
    contDiff_chartPushedExt (I := I) (M := M) α hf_smooth hf_support hf_compact
  refine ⟨?_, ?_⟩
  · exact memLp_chartPushedExt (I := I) (M := M) α ρ hρ hu p
  · intro i
    refine ⟨fun x : EuclN E =>
      (fderiv ℝ (chartPushedExt (I := I) (M := M) α f) x)
        (EuclideanSpace.single i 1), ?_, ?_⟩
    · exact fderiv_chartPushedExt_memLp (I := I) (M := M) α ρ hρ hu p i
    · exact DeGiorgi.HasWeakPartialDeriv.of_contDiff
        (chartTargetEuclid_isOpen' (I := I) (M := M) α)
        (hsmooth.of_le (by norm_cast))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.memW1p_chartPushedExt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.memW1p_chartPushedExt target :: scope.openDecls } }

private theorem memW1p_chartPushed_of_contMDiff
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    DeGiorgi.MemW1p p
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set ρ := chartAtlasPOU I M with hρ_def
  have hρ_sub : ρ.IsSubordinate (fun β : M => (chartAt H β).source) :=
    chartAtlasPOU_isSubordinate I M
  have hExt_memW1p : DeGiorgi.MemW1p p
      (chartPushedExt (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) :=
    memW1p_chartPushedExt (I := I) (M := M) α ρ hρ_sub hu hp
  have hae_eq : chartPushedExt (I := I) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) =ᵐ[volume.restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) ρ α u := by
    refine
      (MeasureTheory.ae_restrict_iff' (chartTargetEuclid_measurableSet
        (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact chartPushedExt_eq_chartPushed_on_target
      (I := I) (M := M) ρ α u hy
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
    (chartTargetEuclid_isOpen' (I := I) (M := M) α) hae_eq).mp hExt_memW1p

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.memW1p_chartPushed_of_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.memW1p_chartPushed_of_contMDiff target :: scope.openDecls } }

theorem MemWkpChart_of_contMDiff
    [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M]
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemWkpChart (I := I) (M := M) 1 p u := by
  intro α
  rw [show (1 : ℕ) = 0 + 1 from rfl,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ]
  refine ⟨?_, ?_⟩
  · exact memW1p_chartPushed_of_contMDiff (I := I) (M := M) α hu hp
  · intro i
    have hMW1p : DeGiorgi.MemW1p p
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) :=
      memW1p_chartPushed_of_contMDiff (I := I) (M := M) α hu hp
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
      (d := Module.finrank ℝ E) hMW1p i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff

theorem MemW1pIntrinsic_of_contMDiff_explicit
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (p : ℝ≥0∞) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    DifferentialGeometry.Analysis.Sobolev.Intrinsic.MemW1pIntrinsic
      (I := I) (M := M) g p u :=
  DifferentialGeometry.Analysis.Sobolev.Intrinsic.MemW1pIntrinsic_of_contMDiff
    (I := I) (M := M) g p hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Equivalence.MemW1pIntrinsic_of_contMDiff_explicit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Equivalence.MemW1pIntrinsic_of_contMDiff_explicit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Equivalence.MemW1pIntrinsic_of_contMDiff_explicit ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.MemW1pIntrinsic_of_contMDiff_explicit

theorem memWkpChart_iff_memW1pIntrinsic_of_contMDiff
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemWkpChart (I := I) (M := M) 1 p u ↔
      DifferentialGeometry.Analysis.Sobolev.Intrinsic.MemW1pIntrinsic
        (I := I) (M := M) g p u := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · exact MemW1pIntrinsic_of_contMDiff_explicit (I := I) (M := M) g p hu_smooth
  · exact MemWkpChart_of_contMDiff (I := I) (M := M) hp_one hu_smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Equivalence.memWkpChart_iff_memW1pIntrinsic_of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Equivalence.memWkpChart_iff_memW1pIntrinsic_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Equivalence.memWkpChart_iff_memW1pIntrinsic_of_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.memWkpChart_iff_memW1pIntrinsic_of_contMDiff

theorem wkpNormChart_lt_top_of_contMDiff
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    wkpNormChart (I := I) (M := M) 1 p u < ⊤ :=
  wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp
    (MemWkpChart_of_contMDiff (I := I) (M := M) hp hu)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Equivalence.wkpNormChart_lt_top_of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Equivalence.wkpNormChart_lt_top_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Equivalence.wkpNormChart_lt_top_of_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.wkpNormChart_lt_top_of_contMDiff

theorem w1pNormIntrinsic_lt_top_of_contMDiff
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (p : ℝ≥0∞) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    DifferentialGeometry.Analysis.Sobolev.Intrinsic.w1pNormIntrinsic
        (I := I) (M := M) g p u < ⊤ :=
  (MemW1pIntrinsic_of_contMDiff_explicit (I := I) (M := M) g p hu).w1pNormIntrinsic_lt_top

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Equivalence.w1pNormIntrinsic_lt_top_of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Equivalence.w1pNormIntrinsic_lt_top_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Equivalence.w1pNormIntrinsic_lt_top_of_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.w1pNormIntrinsic_lt_top_of_contMDiff

end Equivalence
end Sobolev
end Analysis
end DifferentialGeometry
