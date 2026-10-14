import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.MeasureComparison
import Submission.DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
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

private def pouTsupportSet (α : M) : Set M :=
  tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupportSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupportSet target :: scope.openDecls } }

private def pouChartKernel (α : M) : Set E :=
  (extChartAt I α) '' (pouTsupportSet (I := I) (M := M) α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouChartKernel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouChartKernel target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pouChartKernel_isCompact (α : M) :
    IsCompact (pouChartKernel (I := I) (M := M) α) :=
  chartImage_pouTsupport_isCompact (I := I) (M := M) α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouChartKernel_isCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouChartKernel_isCompact target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouChartKernel_subset_target (α : M) :
    pouChartKernel (I := I) (M := M) α ⊆ (extChartAt I α).target :=
  chartImage_pouTsupport_subset_target (I := I) (M := M) α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouChartKernel_subset_target
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouChartKernel_subset_target target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentScalar_tsupport_subset_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) ⊆
      pouTsupportSet (I := I) (M := M) α := by
  classical
  rw [tensorChartComponentScalar_def]
  unfold tensorChartComponentPou pouTsupportSet
  have h_eq :
      (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x) =
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x) := by
    funext x; rfl
  rw [h_eq]
  exact tsupport_smul_subset_left
    (f := fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    (g := tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_tsupport_subset_pouTsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_tsupport_subset_pouTsupport target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentScalar_tsupport_subset_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) ⊆
      (chartAt H α).source :=
  (tensorChartComponentScalar_tsupport_subset_pouTsupport
    (I := I) (M := M) g r s S α Idx Jdx).trans
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_tsupport_subset_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_tsupport_subset_chart_source target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentScalar_chartImage_tsupport_subset_kernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (extChartAt I α) ''
        (tsupport (tensorChartComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx)) ⊆
      pouChartKernel (I := I) (M := M) α :=
  Set.image_mono
    (tensorChartComponentScalar_tsupport_subset_pouTsupport
      (I := I) (M := M) g r s S α Idx Jdx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_chartImage_tsupport_subset_kernel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_chartImage_tsupport_subset_kernel target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorChartComponent_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) := by
  have h := tensorChartComponent_contMDiff (I := I) (M := M) g r s S α Idx Jdx
  exact h.continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_continuous target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorChartComponent_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) :=
  (tensorChartComponent_continuous (I := I) (M := M) g r s S α Idx Jdx).measurable

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_measurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_measurable target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentScalar_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous (tensorChartComponentScalar (I := I) (M := M)
      g r s S α Idx Jdx) :=
  (tensorChartComponentScalar_contMDiff
    (I := I) (M := M) g r s S α Idx Jdx).continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_continuous target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentScalar_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable (tensorChartComponentScalar (I := I) (M := M)
      g r s S α Idx Jdx) :=
  (tensorChartComponentScalar_continuous
    (I := I) (M := M) g r s S α Idx Jdx).measurable

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_measurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_measurable target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponent_eq_chartPushedRaw_scalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx =
      chartPushedRaw I α
        (tensorChartComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx) := by
  rw [tensorChartComponent_def, tensorChartComponentScalar_def]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_chartPushedRaw_scalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_chartPushedRaw_scalar target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponent_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) 2
            (chartLebesgueMeasure (I := I) (M := M) α) ≤
          ENNReal.ofReal C * ENNReal.ofReal ‖S‖ := by
  classical
  obtain ⟨C₁, hC₁_nn, h_scalar⟩ :=
    tensorChartComponentScalar_eLpNorm_le_uniform (I := I) (M := M) g r s α
  by_cases hker : (pouChartKernel (I := I) (M := M) α).Nonempty
  · obtain ⟨C₂, hC₂_pos, h_bridge⟩ :=
      eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform
        (I := I) (M := M) g α
        (pouChartKernel_isCompact (I := I) (M := M) α) hker
        (pouChartKernel_subset_target (I := I) (M := M) α)
        (p := 2) (by norm_num) (by norm_num)
    refine ⟨C₂ * C₁, mul_nonneg hC₂_pos.le hC₁_nn, ?_⟩
    intro S Idx Jdx
    rw [tensorChartComponent_eq_chartPushedRaw_scalar
      (I := I) (M := M) g r s S α Idx Jdx]
    have h1 :=
      h_bridge
        (tensorChartComponentScalar_measurable (I := I) (M := M) g r s S α Idx Jdx)
        (tensorChartComponentScalar_tsupport_subset_chart_source
          (I := I) (M := M) g r s S α Idx Jdx)
        (tensorChartComponentScalar_chartImage_tsupport_subset_kernel
          (I := I) (M := M) g r s S α Idx Jdx)
    have h2 := h_scalar S Idx Jdx
    have h_chain :
        _root_.MeasureTheory.eLpNorm (chartPushedRaw I α
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) 2
            ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal C₂ *
            (ENNReal.ofReal C₁ * ENNReal.ofReal ‖S‖) := by
      refine h1.trans ?_
      gcongr
      rwa [SmoothCcTensor.norm_def (I := I) (M := M)]
    rw [chartLebesgueMeasure, ENNReal.ofReal_mul hC₂_pos.le, mul_assoc]
    exact h_chain
  · refine ⟨0, le_refl 0, ?_⟩
    intro S Idx Jdx
    have h_support_empty :
        ¬ (tsupport (tensorChartComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx)).Nonempty := by
      intro h_ne
      exact hker
        ((h_ne.image (extChartAt I α)).mono
          (tensorChartComponentScalar_chartImage_tsupport_subset_kernel
            (I := I) (M := M) g r s S α Idx Jdx))
    have h_scalar_zero :
        tensorChartComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx = (fun _ : M => (0 : ℝ)) := by
      funext x
      have hx : x ∉ tsupport (tensorChartComponentScalar
          (I := I) (M := M) g r s S α Idx Jdx) := fun hxs =>
        h_support_empty ⟨x, hxs⟩
      exact image_eq_zero_of_notMem_tsupport hx
    have h_comp_zero :
        tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx =
          (fun _ : EuclN => (0 : ℝ)) := by
      rw [tensorChartComponent_eq_chartPushedRaw_scalar
        (I := I) (M := M) g r s S α Idx Jdx, h_scalar_zero]
      funext y
      by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
      · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
      · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    rw [h_comp_zero, ENNReal.ofReal_zero, _root_.MulZeroClass.zero_mul]
    rw [show (fun _ : EuclN => (0 : ℝ)) = (0 : EuclN → ℝ) from rfl, _root_.MeasureTheory.eLpNorm_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eLpNorm_le_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eLpNorm_le_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eLpNorm_le_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eLpNorm_le_uniform

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponent_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemLp (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, h_bound⟩ :=
    tensorChartComponent_eLpNorm_le_uniform (I := I) (M := M) g r s α
  refine ⟨?_, ?_⟩
  · exact (tensorChartComponent_continuous (I := I) (M := M)
      g r s S α Idx Jdx).aestronglyMeasurable
  · refine lt_of_le_of_lt (h_bound S Idx Jdx) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_memLp

private def smoothChartComponentLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  (tensorChartComponent_memLp (I := I) (M := M) g r s S α Idx Jdx).toLp _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLp target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartComponentLp_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ((smoothChartComponentLp (I := I) (M := M) g r s S α Idx Jdx :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx := by
  unfold smoothChartComponentLp
  exact MemLp.coeFn_toLp _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLp_coeFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLp_coeFn target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartComponentLp_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    smoothChartComponentLp (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx =
      smoothChartComponentLp (I := I) (M := M) g r s S₁ α Idx Jdx +
        smoothChartComponentLp (I := I) (M := M) g r s S₂ α Idx Jdx := by
  classical
  apply Lp.ext
  refine (smoothChartComponentLp_coeFn (I := I) (M := M)
    g r s (S₁ + S₂) α Idx Jdx).trans ?_
  have h_fun :
      tensorChartComponent (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx =
        tensorChartComponent (I := I) (M := M) g r s S₁ α Idx Jdx +
          tensorChartComponent (I := I) (M := M) g r s S₂ α Idx Jdx :=
    tensorChartComponent_add (I := I) (M := M) g r s S₁ S₂ α Idx Jdx
  rw [h_fun]
  have h_add :=
    (Lp.coeFn_add (smoothChartComponentLp (I := I) (M := M) g r s S₁ α Idx Jdx)
      (smoothChartComponentLp (I := I) (M := M) g r s S₂ α Idx Jdx))
  refine (Filter.EventuallyEq.add
    (smoothChartComponentLp_coeFn (I := I) (M := M) g r s S₁ α Idx Jdx)
    (smoothChartComponentLp_coeFn (I := I) (M := M) g r s S₂ α Idx Jdx)).symm.trans
    h_add.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLp_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLp_add target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartComponentLp_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    smoothChartComponentLp (I := I) (M := M) g r s (c • S) α Idx Jdx =
      c • smoothChartComponentLp (I := I) (M := M) g r s S α Idx Jdx := by
  classical
  apply Lp.ext
  refine (smoothChartComponentLp_coeFn (I := I) (M := M)
    g r s (c • S) α Idx Jdx).trans ?_
  have h_fun :
      tensorChartComponent (I := I) (M := M) g r s (c • S) α Idx Jdx =
        c • tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx :=
    tensorChartComponent_smul (I := I) (M := M) g r s c S α Idx Jdx
  rw [h_fun]
  have h_smul :=
    Lp.coeFn_smul c (smoothChartComponentLp (I := I) (M := M) g r s S α Idx Jdx)
  refine ((smoothChartComponentLp_coeFn (I := I) (M := M)
    g r s S α Idx Jdx).const_smul c).symm.trans h_smul.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLp_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLp_smul target :: scope.openDecls } }

private def smoothChartComponentLpLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    SmoothCcTensor g r s →ₗ[ℝ] _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) where
  toFun S := smoothChartComponentLp (I := I) (M := M) g r s S α P₀.1 P₀.2
  map_add' S₁ S₂ :=
    smoothChartComponentLp_add (I := I) (M := M) g r s S₁ S₂ α P₀.1 P₀.2
  map_smul' c S :=
    smoothChartComponentLp_smul (I := I) (M := M) g r s c S α P₀.1 P₀.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLpLin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLpLin target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma smoothChartComponentLpLin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (S : SmoothCcTensor g r s) :
    smoothChartComponentLpLin (I := I) (M := M) g r s α P₀ S =
      smoothChartComponentLp (I := I) (M := M) g r s S α P₀.1 P₀.2 := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLpLin_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLpLin_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartComponentLpLin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g r s,
        ‖smoothChartComponentLpLin (I := I) (M := M) g r s α P₀ S‖ ≤ C * ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, h_bound⟩ :=
    tensorChartComponent_eLpNorm_le_uniform (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S
  have h_norm_eq :
      ‖smoothChartComponentLpLin (I := I) (M := M) g r s α P₀ S‖ =
        (_root_.MeasureTheory.eLpNorm (tensorChartComponent (I := I) (M := M)
          g r s S α P₀.1 P₀.2) 2 (chartLebesgueMeasure (I := I) (M := M) α)).toReal := by
    rw [smoothChartComponentLpLin_apply]
    unfold smoothChartComponentLp
    exact MeasureTheory.Lp.norm_toLp _ _
  rw [h_norm_eq]
  have h_eLp := h_bound S P₀.1 P₀.2
  have h_rhs_lt_top :
      ENNReal.ofReal C * ENNReal.ofReal ‖S‖ ≠ (⊤ : ℝ≥0∞) :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
  have h_toReal_le :
      (_root_.MeasureTheory.eLpNorm (tensorChartComponent (I := I) (M := M)
        g r s S α P₀.1 P₀.2) 2 (chartLebesgueMeasure (I := I) (M := M) α)).toReal ≤
        (ENNReal.ofReal C * ENNReal.ofReal ‖S‖).toReal :=
    ENNReal.toReal_mono h_rhs_lt_top h_eLp
  refine h_toReal_le.trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_nn,
    ENNReal.toReal_ofReal (norm_nonneg _)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLpLin_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLpLin_norm_le target :: scope.openDecls } }

private def smoothChartComponentLpCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    SmoothCcTensor g r s →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  (smoothChartComponentLpLin (I := I) (M := M) g r s α P₀).mkContinuous
    (smoothChartComponentLpLin_norm_le (I := I) (M := M) g r s α P₀).choose
    (smoothChartComponentLpLin_norm_le (I := I) (M := M) g r s α P₀).choose_spec.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLpCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLpCLM target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma smoothChartComponentLpCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (S : SmoothCcTensor g r s) :
    smoothChartComponentLpCLM (I := I) (M := M) g r s α P₀ S =
      smoothChartComponentLp (I := I) (M := M) g r s S α P₀.1 P₀.2 := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLpCLM_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartComponentLpCLM_apply target :: scope.openDecls } }

def smoothToTensorL2 (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s →L[ℝ] TensorL2 r s g :=
  UniformSpace.Completion.toComplL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorL2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma smoothToTensorL2_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    smoothToTensorL2 (I := I) (M := M) g r s S = (S : TensorL2 r s g) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorL2_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorL2_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorL2_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorL2_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma denseRange_smoothToTensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    DenseRange (smoothToTensorL2 (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorL2 (I := I) (M := M) g r s :
        SmoothCcTensor g r s → TensorL2 r s g) =
      ((↑) : SmoothCcTensor g r s →
        UniformSpace.Completion (SmoothCcTensor g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.denseRange_smoothToTensorL2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.denseRange_smoothToTensorL2 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma isUniformInducing_smoothToTensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing (smoothToTensorL2 (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorL2 (I := I) (M := M) g r s :
        SmoothCcTensor g r s → TensorL2 r s g) =
      ((↑) : SmoothCcTensor g r s →
        UniformSpace.Completion (SmoothCcTensor g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensor g r s)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.isUniformInducing_smoothToTensorL2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.isUniformInducing_smoothToTensorL2 target :: scope.openDecls } }

def tensorL2ChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  ContinuousLinearMap.extend
    (smoothChartComponentLpCLM (I := I) (M := M) g r s α P₀)
    (smoothToTensorL2 (I := I) (M := M) g r s) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent

def tensorL2ChartComponentCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    TensorL2 r s g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  ContinuousLinearMap.extend
    (smoothChartComponentLpCLM (I := I) (M := M) g r s α P₀)
    (smoothToTensorL2 (I := I) (M := M) g r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCLM

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorL2ChartComponentCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (u : TensorL2 r s g) :
    tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀ u =
      tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCLM_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCLM_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponent_smoothToTensorL2_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        (S : TensorL2 r s g) α P₀ =
      (tensorChartComponent_memLp (I := I) (M := M)
        g r s S α P₀.1 P₀.2).toLp
        (tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2) := by
  classical
  have h_extend :
      tensorL2ChartComponent (I := I) (M := M) g r s
          (smoothToTensorL2 (I := I) (M := M) g r s S) α P₀ =
        smoothChartComponentLpCLM (I := I) (M := M) g r s α P₀ S := by
    unfold tensorL2ChartComponent
    exact ContinuousLinearMap.extend_eq
      (smoothChartComponentLpCLM (I := I) (M := M) g r s α P₀)
      (e := smoothToTensorL2 (I := I) (M := M) g r s)
      (denseRange_smoothToTensorL2 (I := I) (M := M) g r s)
      (isUniformInducing_smoothToTensorL2 (I := I) (M := M) g r s) S
  rw [smoothToTensorL2_apply] at h_extend
  rw [h_extend, smoothChartComponentLpCLM_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smoothToTensorL2_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smoothToTensorL2_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smoothToTensorL2_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smoothToTensorL2_eq

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponent_smoothToTensorL2_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (S : TensorL2 r s g) α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2 := by
  rw [tensorL2ChartComponent_smoothToTensorL2_eq (I := I) (M := M)
    g r s S α P₀]
  exact MemLp.coeFn_toLp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smoothToTensorL2_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smoothToTensorL2_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smoothToTensorL2_coeFn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smoothToTensorL2_coeFn

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorL2ChartComponent_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        (0 : TensorL2 r s g) α P₀ = 0 := by
  rw [← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀]
  exact map_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponent_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u v : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s (u + v) α P₀ =
      tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ +
        tensorL2ChartComponent (I := I) (M := M) g r s v α P₀ := by
  rw [← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀,
    ← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀ u,
    ← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀ v]
  exact map_add _ u v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_add

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponent_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s (c • u) α P₀ =
      c • tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ := by
  rw [← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀,
    ← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀ u]
  exact map_smul _ c u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_smul

omit [NeZero (Module.finrank ℝ E)] in
theorem continuous_tensorL2ChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    Continuous (fun u : TensorL2 r s g =>
      tensorL2ChartComponent (I := I) (M := M) g r s u α P₀) := by
  have h : (fun u : TensorL2 r s g =>
      tensorL2ChartComponent (I := I) (M := M) g r s u α P₀) =
      (tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀) := by
    funext u
    rw [tensorL2ChartComponentCLM_apply]
  rw [h]
  exact (tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuous_tensorL2ChartComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuous_tensorL2ChartComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuous_tensorL2ChartComponent ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.continuous_tensorL2ChartComponent

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
