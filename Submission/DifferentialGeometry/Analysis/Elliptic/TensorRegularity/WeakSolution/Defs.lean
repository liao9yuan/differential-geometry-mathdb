import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.ChartWeakIdentity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

noncomputable def tensorComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) : EuclN → ℝ :=
  chartPushedRaw I α
    (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma tensorComponentEuclid_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) :
    tensorComponentEuclid (I := I) (M := M) g r s T α P₀ =
      chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_def ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_def

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma tensorComponentEuclid_apply_of_mem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorComponentEuclid (I := I) (M := M) g r s T α P₀ y =
      tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  rw [tensorComponentEuclid_def]
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_apply_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_apply_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_apply_of_mem ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_apply_of_mem

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma tensorComponentEuclid_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {y : EuclN} (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    tensorComponentEuclid (I := I) (M := M) g r s T α P₀ y = 0 := by
  rw [tensorComponentEuclid_def]
  exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_apply_of_notMem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_apply_of_notMem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_apply_of_notMem ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_apply_of_notMem

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorComponentEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) :
    ContDiffOn ℝ ∞ (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
    g r s T α P₀.1 P₀.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_contDiffOn

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_eq_zero_of_section_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {x : M} (hx : T.toSection x = 0) :
    tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x = 0 := by
  classical
  rw [tensorChartComponentRaw_def]
  unfold tensorTrivProj
  rw [hx, ContinuousLinearMap.map_zero, ContinuousLinearMap.map_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComponentRaw_eq_zero_of_section_eq_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComponentRaw_eq_zero_of_section_eq_zero target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma tensorChartComponentRaw_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) ⊆
      tsupport T.toFun := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hx_notsupp
  have hzero : T.toFun x = 0 := image_eq_zero_of_notMem_tsupport hx_notsupp
  have hsec : T.toSection x = 0 := by
    have hmod : TensorRSSpace.toModel (T.toSection x) = 0 := hzero
    have := (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).injective
      (a₁ := T.toSection x) (a₂ := 0)
    apply this
    rw [show (tensorRSSpaceContinuousLinearEquiv (I := I) r s x) (T.toSection x) =
        TensorRSSpace.toModel (T.toSection x) from rfl, hmod, ContinuousLinearEquiv.map_zero]
  exact hx (tensorChartComponentRaw_eq_zero_of_section_eq_zero
    (I := I) (M := M) g r s T α Idx Jdx hsec)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComponentRaw_tsupport_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComponentRaw_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComponentRaw_tsupport_subset ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComponentRaw_tsupport_subset

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_tsupport_subset_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (hT_support : tsupport T.toFun ⊆ (chartAt H α).source) :
    tsupport (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) ⊆
      (chartAt H α).source :=
  (tensorChartComponentRaw_tsupport_subset (I := I) (M := M) g r s T α Idx Jdx).trans
    hT_support

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComponentRaw_tsupport_subset_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorChartComponentRaw_tsupport_subset_chart_source target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem tensorComponentEuclid_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (hT_support : tsupport T.toFun ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) := by
  classical
  have hraw_support : tsupport
      (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) ⊆
      (chartAt H α).source :=
    tensorChartComponentRaw_tsupport_subset_chart_source
      (I := I) (M := M) g r s T α P₀.1 P₀.2 hT_support
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  set K : Set EuclN :=
    toEuclidean '' ((extChartAt I α) ''
      (tsupport (tensorChartComponentRaw (I := I) (M := M)
        g r s T α P₀.1 P₀.2))) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_extChartAt_tsupport_compact
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_support
  have hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_support
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact ((tensorComponentEuclid_contDiffOn (I := I) (M := M)
      g r s T α P₀).contDiffWithinAt hy).contDiffAt (hopen.mem_nhds hy)
  · have hyK : y ∉ K := fun h => hy (hK_target h)
    have hKc_open : IsOpen Kᶜ := hK_compact.isClosed.isOpen_compl
    refine (contDiff_const (c := (0 : ℝ))).contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hKc_open.mem_nhds hyK] with z hz
    by_cases hzT : z ∈ chartTargetEuclid (I := I) (M := M) α
    · exact chartPushedRaw_eq_zero_off_image_tsupport
        (I := I) (M := M)
        (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
        α hzT hz
    · exact tensorComponentEuclid_apply_of_notMem
        (I := I) (M := M) g r s T α P₀ hzT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_contDiff ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_contDiff

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorComponentEuclid_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (hT_support : tsupport T.toFun ⊆ (chartAt H α).source) :
    tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  have hraw_support : tsupport
      (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) ⊆
      (chartAt H α).source :=
    tensorChartComponentRaw_tsupport_subset_chart_source
      (I := I) (M := M) g r s T α P₀.1 P₀.2 hT_support
  set K : Set EuclN :=
    toEuclidean '' ((extChartAt I α) ''
      (tsupport (tensorChartComponentRaw (I := I) (M := M)
        g r s T α P₀.1 P₀.2))) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_extChartAt_tsupport_compact
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_support
  have hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_support
  have hsupp : Function.support
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K := by
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyK
    by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
    · exact hy (chartPushedRaw_eq_zero_off_image_tsupport
        (I := I) (M := M)
        (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
        α hyT hyK)
    · exact hy (tensorComponentEuclid_apply_of_notMem
        (I := I) (M := M) g r s T α P₀ hyT)
  exact (closure_minimal hsupp hK_compact.isClosed).trans hK_target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_tsupport_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_tsupport_subset ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_tsupport_subset

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorComponentEuclid_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (hT_support : tsupport T.toFun ⊆ (chartAt H α).source) :
    HasCompactSupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) := by
  classical
  have hraw_support : tsupport
      (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) ⊆
      (chartAt H α).source :=
    tensorChartComponentRaw_tsupport_subset_chart_source
      (I := I) (M := M) g r s T α P₀.1 P₀.2 hT_support
  set K : Set EuclN :=
    toEuclidean '' ((extChartAt I α) ''
      (tsupport (tensorChartComponentRaw (I := I) (M := M)
        g r s T α P₀.1 P₀.2))) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_extChartAt_tsupport_compact
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_support
  have hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_support
  have hsupp : Function.support
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K := by
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyK
    by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
    · exact hy (chartPushedRaw_eq_zero_off_image_tsupport
        (I := I) (M := M)
        (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
        α hyT hyK)
    · exact hy (tensorComponentEuclid_apply_of_notMem
        (I := I) (M := M) g r s T α P₀ hyT)
  exact HasCompactSupport.of_support_subset_isCompact hK_compact hsupp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponentEuclid_hasCompactSupport

omit [CompleteSpace E] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem tensorComponent_isSmoothWeakSolution_of_chartIdentity
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_support : tsupport T.toFun ⊆ (chartAt H α).source)
    (f : EuclN → ℝ)
    (hbilin :
      ∀ φ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (Set.univ : Set EuclN) →
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).bilin
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ =
          ∫ y in (Set.univ : Set EuclN), f y * φ y) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) f := by
  classical
  refine ⟨tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P₀ hT_support, ?_⟩
  intro φ hφ hφ_cs hφ_support
  exact hbilin φ hφ hφ_cs hφ_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponent_isSmoothWeakSolution_of_chartIdentity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponent_isSmoothWeakSolution_of_chartIdentity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponent_isSmoothWeakSolution_of_chartIdentity ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorComponent_isSmoothWeakSolution_of_chartIdentity

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
