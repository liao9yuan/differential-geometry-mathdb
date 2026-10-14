import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.ChartWeakIdentity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity

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

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EuclN
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EuclN target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx y =
      chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y *
        chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y := by
  classical
  rw [tensorChartComponent_def (I := I) (M := M) g r s S α Idx Jdx]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hy]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem tensorChartComponent_eventuallyEq_chartPushedRaw_pou_mul_chartPushedRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx =ᶠ[nhds y]
      (fun z : EuclN E =>
        chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
          chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M)
              g r s S α Idx Jdx) z) := by
  classical
  refine Filter.eventually_of_mem
    ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy) ?_
  intro z hz
  exact tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target
    (I := I) (M := M) g r s S α Idx Jdx hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eventuallyEq_chartPushedRaw_pou_mul_chartPushedRaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eventuallyEq_chartPushedRaw_pou_mul_chartPushedRaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eventuallyEq_chartPushedRaw_pou_mul_chartPushedRaw ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eventuallyEq_chartPushedRaw_pou_mul_chartPushedRaw

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem chartPushedRaw_chartAtlasPOU_contDiffOn (α : M) :
    ContDiffOn ℝ ∞
      (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hPOU_global : ContMDiff I 𝓘(ℝ, ℝ) ∞
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  have hPOU_source : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
      ((chartAt H α).source) :=
    hPOU_global.contMDiffOn
  exact chartPushedRaw_bump_contDiffOn (I := I) (M := M) α hPOU_source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_chartAtlasPOU_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_chartAtlasPOU_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_chartAtlasPOU_contDiffOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_chartAtlasPOU_contDiffOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem differentiableAt_chartPushedRaw_chartAtlasPOU
    (α : M) {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    DifferentiableAt ℝ
      (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y := by
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hcontDiffAt : ContDiffAt ℝ ∞
      (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y :=
    (chartPushedRaw_chartAtlasPOU_contDiffOn (I := I) (M := M) α y hy).contDiffAt
      (hopen.mem_nhds hy)
  exact hcontDiffAt.differentiableAt (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_chartPushedRaw_chartAtlasPOU then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_chartPushedRaw_chartAtlasPOU"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_chartPushedRaw_chartAtlasPOU ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_chartPushedRaw_chartAtlasPOU

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem differentiableAt_chartPushedRaw_tensorChartComponentRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    DifferentiableAt ℝ
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y := by
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hcontDiffAt : ContDiffAt ℝ ∞
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y :=
    (chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
      g r s S α Idx Jdx y hy).contDiffAt (hopen.mem_nhds hy)
  exact hcontDiffAt.differentiableAt (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_chartPushedRaw_tensorChartComponentRaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_chartPushedRaw_tensorChartComponentRaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_chartPushedRaw_tensorChartComponentRaw ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_chartPushedRaw_tensorChartComponentRaw

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem chartPushedRaw_pou_mul_euclidPartial_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y
        * euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S α Idx Jdx)) y =
      euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y
        - euclidPartial (E := E) k
              (chartPushedRaw I α
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y
            * chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S α Idx Jdx) y := by
  classical
  set P : EuclN E → ℝ :=
    chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hP_def
  set R : EuclN E → ℝ :=
    chartPushedRaw I α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) with hR_def
  have h_component_deriv :
      euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y =
        euclidPartial (E := E) k (fun z : EuclN E => P z * R z) y := by
    rw [euclidPartial_def, euclidPartial_def]
    congr 1
    exact Filter.EventuallyEq.fderiv_eq
      (tensorChartComponent_eventuallyEq_chartPushedRaw_pou_mul_chartPushedRaw
        (I := I) (M := M) g r s S α Idx Jdx hy)
  have hP_diff : DifferentiableAt ℝ P y :=
    differentiableAt_chartPushedRaw_chartAtlasPOU (I := I) (M := M) α hy
  have hR_diff : DifferentiableAt ℝ R y :=
    differentiableAt_chartPushedRaw_tensorChartComponentRaw
      (I := I) (M := M) g r s S α Idx Jdx hy
  have h_leibniz :
      euclidPartial (E := E) k (fun z : EuclN E => P z * R z) y =
        euclidPartial (E := E) k P y * R y +
          P y * euclidPartial (E := E) k R y :=
    euclidPartial_mul (E := E) k hP_diff hR_diff
  rw [h_component_deriv, h_leibniz]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_pou_mul_euclidPartial_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_pou_mul_euclidPartial_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_pou_mul_euclidPartial_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_pou_mul_euclidPartial_eq

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
