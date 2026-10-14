import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.SmoothRepresentative.Approximation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

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

noncomputable def eigenvectorSmoothApprox
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ℕ → SmoothCcTensorH1 g r s :=
  Classical.choose (exists_smoothApprox (I := I) (M := M) g r s i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothApprox then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothApprox"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothApprox ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothApprox

theorem eigenvectorSmoothApprox_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Filter.Tendsto
      (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n))
      _root_.Filter.atTop
      (𝓝 (eigenvectorResolvent (I := I) (M := M) g r s i)) :=
  Classical.choose_spec
    (exists_smoothApprox (I := I) (M := M) g r s i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothApprox_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothApprox_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothApprox_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmoothApprox_tendsto

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
private lemma resolventL2_eq_smul_eigenvector
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i) =
      i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_eq := eigenvector_eq_resolvent_smul (I := I) (M := M) g r s i
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rw [h_eq, smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.resolventL2_eq_smul_eigenvector
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.resolventL2_eq_smul_eigenvector target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
private lemma smoothApprox_coe_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Filter.Tendsto
      (fun n => (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g))
      _root_.Filter.atTop
      (𝓝 (i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_l2 :
      Filter.Tendsto
        (fun n => TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)))
        _root_.Filter.atTop
        (𝓝 (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i))) :=
    ((TensorH1ComplToTensorL2 (I := I) (M := M) g r s).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  have h_term :
      (fun n => TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n))) =
        fun n => (((eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor) : TensorL2 r s g) := by
    funext n
    exact TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
      (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
  rw [h_term, resolventL2_eq_smul_eigenvector (I := I) (M := M)
    g r s i] at h_l2
  exact h_l2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothApprox_coe_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothApprox_coe_tendsto target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
private lemma smoothApprox_smul_coe_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g))
      _root_.Filter.atTop
      (𝓝 (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        i)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_smul :=
    (smoothApprox_coe_tendsto (I := I) (M := M) g r s i).const_smul
      (i.fst.val)⁻¹
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rwa [smul_smul, inv_mul_cancel₀ hμ_ne, one_smul] at h_smul

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothApprox_smul_coe_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothApprox_smul_coe_tendsto target :: scope.openDecls } }

theorem eigenvectorChartComponentL2_approx_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ =
      (i.fst.val)⁻¹ •
        (tensorChartComponent_memLp (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2).toLp
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P₀.1 P₀.2) := by
  rw [tensorL2ChartComponent_smul (I := I) (M := M) g r s (i.fst.val)⁻¹
    (((eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor) : TensorL2 r s g) α P₀]
  rw [tensorL2ChartComponent_smoothToTensorL2_eq (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
    α P₀]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentL2_approx_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentL2_approx_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentL2_approx_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentL2_approx_eq

theorem eigenvectorChartComponentL2_approx_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      fun y => (i.fst.val)⁻¹ •
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2 y := by
  rw [tensorL2ChartComponent_smul (I := I) (M := M) g r s (i.fst.val)⁻¹
    (((eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor) : TensorL2 r s g) α P₀]
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    (tensorL2ChartComponent (I := I) (M := M) g r s
      (((eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor) : TensorL2 r s g) α P₀)).trans ?_
  exact (tensorL2ChartComponent_smoothToTensorL2_coeFn (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
    α P₀).const_smul (i.fst.val)⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentL2_approx_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentL2_approx_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentL2_approx_coeFn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentL2_approx_coeFn

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
theorem eigenvectorChartComponentL2_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Filter.Tendsto
      (fun n => tensorL2ChartComponent (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀)
      _root_.Filter.atTop
      (𝓝 (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i) α P₀)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_clm :=
    ((tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀).continuous.tendsto
      _).comp
      (smoothApprox_smul_coe_tendsto (I := I) (M := M) g r s i)
  simp only [Function.comp_def, tensorL2ChartComponentCLM_apply] at h_clm
  exact h_clm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentL2_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentL2_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentL2_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentL2_tendsto

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
