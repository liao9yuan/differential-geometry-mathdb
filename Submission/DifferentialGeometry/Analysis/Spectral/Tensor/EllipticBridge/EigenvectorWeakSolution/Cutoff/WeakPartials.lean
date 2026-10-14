import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.ChartPartialL2Approximation
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
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
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean

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

def eigenvectorCutoffChartWeakPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  (eigenvectorCutoffChartPartialLp (I := I) (M := M)
      g r s i α P₀ k :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartWeakPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartWeakPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartWeakPartial ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartWeakPartial

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
private lemma cutoff_smoothApprox_smul_coe_tendsto
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
  have h_l2 :
      Filter.Tendsto
        (fun n => TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n)))
        _root_.Filter.atTop
        (𝓝 (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i))) :=
    ((TensorH1ComplToTensorL2 (I := I) (M := M) g r s).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  have h_term :
      (fun n => TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n))) =
        fun n => (((eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor) : TensorL2 r s g) := by
    funext n
    exact TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
      (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  have h_shadow :
      TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i) =
        i.fst.val •
          tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i := by
    have h_eq := eigenvector_eq_resolvent_smul
      (I := I) (M := M) g r s i
    rw [h_eq, smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]
  rw [h_term, h_shadow] at h_l2
  have h_smul := h_l2.const_smul (i.fst.val)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hμ_ne, one_smul] at h_smul

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoff_smoothApprox_smul_coe_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoff_smoothApprox_smul_coe_tendsto target :: scope.openDecls } }

lemma eigenvectorCutoffChartComponentL2_approx_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      fun y => (i.fst.val)⁻¹ •
        cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2 y := by
  classical
  rw [show tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ =
      (i.fst.val)⁻¹ •
        tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g) α P₀ from by
    rw [← tensorL2ChartComponentCutoffCLM_apply, map_smul,
      tensorL2ChartComponentCutoffCLM_apply]]
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
      (((eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor) : TensorL2 r s g) α P₀)).trans ?_
  exact (tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn (I := I) (M := M)
    g r s (eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor
    α P₀).const_smul (i.fst.val)⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartComponentL2_approx_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartComponentL2_approx_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartComponentL2_approx_coeFn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartComponentL2_approx_coeFn

lemma eigenvectorCutoffChartPartialLp_approx_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    (((i.fst.val)⁻¹ •
        eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n)) :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      fun y => (i.fst.val)⁻¹ •
        chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α) y := by
  classical
  rw [eigenvectorCutoffChartPartialLp_approx_eq (I := I) (M := M)
    g r s i α P₀ k n]
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    ((chosenWeakPartialOrZero_cutoffComponentEuclid_memLp (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
      α P₀.1 P₀.2 k).toLp
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α)))).trans ?_
  exact (MemLp.coeFn_toLp _).const_smul (i.fst.val)⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_approx_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_approx_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_approx_coeFn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_approx_coeFn

private lemma eigenvectorCutoffChartWeakPartial_approx_hasWeakPartialDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (((i.fst.val)⁻¹ •
          eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
            (smoothToTensorH1Compl (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n)) :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          ((i.fst.val)⁻¹ •
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_w1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) :=
    cutoffComponentEuclid_memW1p (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
      α P₀.1 P₀.2
  have h_weak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α))
        (cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem h_w1p k
  have h_weak_smul :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (fun y => (i.fst.val)⁻¹ •
          chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
            (cutoffComponentEuclid (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α) y)
        (fun y => (i.fst.val)⁻¹ •
          cutoffComponentEuclid (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P₀.1 P₀.2 y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_weak.const_smul (i.fst.val)⁻¹
  refine h_weak_smul.congr_ae ?_ ?_
  · exact (eigenvectorCutoffChartComponentL2_approx_coeFn
      (I := I) (M := M) g r s i α P₀ n).symm
  · exact (eigenvectorCutoffChartPartialLp_approx_coeFn
      (I := I) (M := M) g r s i α P₀ k n).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartWeakPartial_approx_hasWeakPartialDeriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartWeakPartial_approx_hasWeakPartialDeriv target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
private lemma eigenvectorCutoffChartComponentL2_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Filter.Tendsto
      (fun n => tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀)
      _root_.Filter.atTop
      (𝓝 (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i) α P₀)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_clm :=
    ((tensorL2ChartComponentCutoffCLM (I := I) (M := M)
        g r s α P₀).continuous.tendsto _).comp
      (cutoff_smoothApprox_smul_coe_tendsto (I := I) (M := M) g r s i)
  simp only [Function.comp_def, tensorL2ChartComponentCutoffCLM_apply] at h_clm
  exact h_clm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartComponentL2_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartComponentL2_tendsto target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
private lemma eigenvectorCutoffChartComponent_eLpNorm_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Filter.Tendsto
      (fun n => _root_.MeasureTheory.eLpNorm
        (((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            ((i.fst.val)⁻¹ •
              (((eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) -
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i)
            α P₀ :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)) 2
        (chartLebesgueMeasure (I := I) (M := M) α))
      atTop (𝓝 0) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun n => tensorL2ChartComponentCutoff (I := I) (M := M) g r s
      ((i.fst.val)⁻¹ •
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g)) α P₀)
    (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
      α P₀)).mp
    (eigenvectorCutoffChartComponentL2_tendsto (I := I) (M := M)
      g r s i α P₀)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartComponent_eLpNorm_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartComponent_eLpNorm_tendsto target :: scope.openDecls } }

private lemma eigenvectorCutoffChartPartial_eLpNorm_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => _root_.MeasureTheory.eLpNorm
        ((((i.fst.val)⁻¹ •
            eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
              (smoothToTensorH1Compl (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n)) :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) -
          ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
            g r s i α P₀ k :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)) 2
        (chartLebesgueMeasure (I := I) (M := M) α))
      atTop (𝓝 0) :=
  (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun n => (i.fst.val)⁻¹ •
      eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)))
    (eigenvectorCutoffChartPartialLp (I := I) (M := M)
      g r s i α P₀ k)).mp
    (eigenvectorCutoffChartPartialLp_tendsto (I := I) (M := M)
      g r s i α P₀ k)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartial_eLpNorm_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartial_eLpNorm_tendsto target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
theorem eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s i α P₀ k :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  set uApprox : ℕ → EuclN → ℝ := fun n =>
    ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
    with huApprox_def
  set gApprox : ℕ → EuclN → ℝ := fun n =>
    (((i.fst.val)⁻¹ •
        eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n)) :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
    with hgApprox_def
  set uLim : EuclN → ℝ :=
    ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i) α P₀ :
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
    with huLim_def
  set gLim : EuclN → ℝ :=
    ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
        g r s i α P₀ k :
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
    with hgLim_def
  have hu_n_memLp : ∀ n, _root_.MeasureTheory.MemLp (uApprox n) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    intro n
    simp only [huApprox_def]
    exact Lp.memLp _
  have hg_n_memLp : ∀ n, _root_.MeasureTheory.MemLp (gApprox n) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    intro n
    simp only [hgApprox_def]
    exact Lp.memLp _
  have hu_memLp : _root_.MeasureTheory.MemLp uLim 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    simp only [huLim_def]
    exact Lp.memLp _
  have hg_memLp : _root_.MeasureTheory.MemLp gLim 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    simp only [hgLim_def]
    exact Lp.memLp _
  have h_weak : ∀ n,
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (gApprox n) (uApprox n) (chartTargetEuclid (I := I) (M := M) α) := by
    intro n
    simp only [hgApprox_def, huApprox_def]
    exact eigenvectorCutoffChartWeakPartial_approx_hasWeakPartialDeriv
      (I := I) (M := M) g r s i α P₀ k n
  have h_u_tendsto :
      Filter.Tendsto
        (fun n => _root_.MeasureTheory.eLpNorm (fun x => uApprox n x - uLim x) 2
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        atTop (𝓝 0) := by
    have h := eigenvectorCutoffChartComponent_eLpNorm_tendsto
      (I := I) (M := M) g r s i α P₀
    simp only [huApprox_def, huLim_def]
    exact h
  have h_g_tendsto :
      Filter.Tendsto
        (fun n => _root_.MeasureTheory.eLpNorm (fun x => gApprox n x - gLim x) 2
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        atTop (𝓝 0) := by
    have h := eigenvectorCutoffChartPartial_eLpNorm_tendsto
      (I := I) (M := M) g r s i α P₀ k
    simp only [hgApprox_def, hgLim_def]
    exact h
  have h_closure :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k gLim uLim
        (chartTargetEuclid (I := I) (M := M) α) :=
    hasWeakPartialDeriv_of_tendsto_eLpNorm
      (d := Module.finrank ℝ E) (p := 2) (by norm_num)
      k hu_n_memLp hg_n_memLp hu_memLp hg_memLp h_weak
      h_u_tendsto h_g_tendsto
  rw [hgLim_def, huLim_def] at h_closure
  exact h_closure

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv

theorem eigenvectorCutoffChartWeakPartial_locally_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (eigenvectorCutoffChartWeakPartial (I := I) (M := M)
        g r s i α P₀ k) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
  classical
  let _ := hK
  have h_memLp : _root_.MeasureTheory.MemLp (eigenvectorCutoffChartWeakPartial
      (I := I) (M := M) g r s i α P₀ k) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
    rw [eigenvectorCutoffChartWeakPartial]
    exact Lp.memLp _
  have h_le : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K ≤
      chartLebesgueMeasure (I := I) (M := M) α := by
    rw [chartLebesgueMeasure]
    exact Measure.restrict_mono hK_in (le_refl _)
  exact h_memLp.mono_measure h_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartWeakPartial_locally_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartWeakPartial_locally_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartWeakPartial_locally_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartWeakPartial_locally_memLp

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
