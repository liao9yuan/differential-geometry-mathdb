import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionGlobal
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.L2Approximation
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.PartitionOfUnityBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.ENNReal _root_.NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def chartPouKernel (α : M) : Set EuclN :=
  toEuclidean '' ((extChartAt I α) ''
    (tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPouKernel_isCompact (α : M) :
    IsCompact (chartPouKernel (I := I) (M := M) α) :=
  (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartImage_pouTsupport_isCompact
    (I := I) (M := M) α).image (toEuclidean (E := E)).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel_isCompact ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel_isCompact

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPouKernel_measurableSet (α : M) :
    MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
  (chartPouKernel_isCompact (I := I) (M := M) α).isClosed.measurableSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel_measurableSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel_measurableSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel_measurableSet ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel_measurableSet

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma chartPouKernel_subset_chartTargetEuclid (α : M) :
    chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  rw [chartPouKernel, chartTargetEuclid]
  refine Set.image_mono ?_
  exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartImage_pouTsupport_subset_target
    (I := I) (M := M) α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel_subset_chartTargetEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel_subset_chartTargetEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel_subset_chartTargetEuclid ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel_subset_chartTargetEuclid

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma notMem_pouTsupport_of_notMem_chartPouKernel
    (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hker : y ∉ chartPouKernel (I := I) (M := M) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉
      tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
  classical
  intro hb
  apply hker
  refine ⟨(toEuclidean (E := E)).symm y, ⟨_, hb, ?_⟩, ?_⟩
  · have hmem : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
        (I := I) (M := M) hy
    exact (extChartAt I α).right_inv hmem
  · exact toEuclidean.apply_symm_apply y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.notMem_pouTsupport_of_notMem_chartPouKernel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.notMem_pouTsupport_of_notMem_chartPouKernel target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma tensorChartComponent_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx y = 0 := by
  classical
  by_cases htar : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [tensorChartComponent_def,
      chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx) htar]
    have hb := notMem_pouTsupport_of_notMem_chartPouKernel
      (I := I) (M := M) α htar hy
    have hb_support : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉
        Function.support
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
      fun hc => hb (subset_tsupport _ hc)
    have hρ : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
      by_contra hc; exact hb_support hc
    change tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0
    unfold tensorChartComponentPou
    rw [hρ, _root_.MulZeroClass.zero_mul]
  · rw [tensorChartComponent_def,
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ htar]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_zero_off_chartPouKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_zero_off_chartPouKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_zero_off_chartPouKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_zero_off_chartPouKernel

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma euclidPartial_tensorChartComponent_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    euclidPartial (E := E) k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y = 0 := by
  classical
  have hsupp : Function.support
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α := by
    intro z hz
    by_contra hzk
    exact hz (tensorChartComponent_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s S α Idx Jdx hzk)
  have htsupp : tsupport
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α :=
    (closure_minimal hsupp
      (chartPouKernel_isCompact (I := I) (M := M) α).isClosed)
  have hy_compl : y ∈ (tsupport
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx))ᶜ :=
    fun hc => hy (htsupp hc)
  have hopen : IsOpen (tsupport
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx))ᶜ :=
    (isClosed_tsupport _).isOpen_compl
  have hevt : tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx
      =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hy_compl) (fun z hz => ?_)
    exact image_eq_zero_of_notMem_tsupport hz
  rw [euclidPartial_def, hevt.fderiv_eq]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_tensorChartComponent_eq_zero_off_chartPouKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_tensorChartComponent_eq_zero_off_chartPouKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_tensorChartComponent_eq_zero_off_chartPouKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_tensorChartComponent_eq_zero_off_chartPouKernel

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma exists_bound_on_chartPouKernel
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ chartPouKernel (I := I) (M := M) α, ‖c y‖ ≤ C := by
  classical
  have hcont : ContinuousOn (fun y => ‖c y‖)
      (chartPouKernel (I := I) (M := M) α) :=
    (hc.continuousOn.mono
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).norm
  obtain ⟨C, hC⟩ := (chartPouKernel_isCompact (I := I) (M := M) α).bddAbove_image
    hcont
  refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
  exact (hC ⟨y, hy, rfl⟩).trans (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_bound_on_chartPouKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_bound_on_chartPouKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_bound_on_chartPouKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_bound_on_chartPouKernel

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma aestronglyMeasurable_indicator_mul
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    _root_.MeasureTheory.AEStronglyMeasurable
      (Set.indicator (chartPouKernel (I := I) (M := M) α) c)
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  have hcont : ContinuousOn c (chartPouKernel (I := I) (M := M) α) :=
    hc.continuousOn.mono
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  have hmeas : _root_.MeasureTheory.AEStronglyMeasurable c
      ((chartLebesgueMeasure (I := I) (M := M) α).restrict
        (chartPouKernel (I := I) (M := M) α)) :=
    hcont.aestronglyMeasurable
      (chartPouKernel_measurableSet (I := I) (M := M) α)
  exact (aestronglyMeasurable_indicator_iff
    (chartPouKernel_measurableSet (I := I) (M := M) α)).mpr hmeas

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_indicator_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_indicator_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_indicator_mul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_indicator_mul

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
