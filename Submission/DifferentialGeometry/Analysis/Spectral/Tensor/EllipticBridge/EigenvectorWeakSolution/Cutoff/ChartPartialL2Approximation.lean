import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.L2Approximation
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.ChartPartialUniformBound.UniformBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
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
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound

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

omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffComponentEuclid_contDiff'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞
      (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) := by
  classical
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  refine
    Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
    (I := I) (M := M) ?_ ?_
  · exact cutoffComponentScalar_contMDiff
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx
  · exact cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_contDiff'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_contDiff' target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_hasCompactSupport'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport
      (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact
    chartPushedRaw_smooth_hasCompactSupport_local
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_hasCompactSupport'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_hasCompactSupport' target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_tsupport_subset'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      ⊆ chartTargetEuclid (I := I) (M := M) α := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact
    tsupport_chartPushedRaw_subset_chartTargetEuclid
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_tsupport_subset'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_tsupport_subset' target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
lemma cutoffComponentEuclid_memW1p
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_W1 : MemWkp (d := Module.finrank ℝ E) 1 2
      (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_of_smooth_compactSupport (d := Module.finrank ℝ E) hΩ_open
      (cutoffComponentEuclid_contDiff' (I := I) (M := M) g r s S α Idx Jdx)
      (cutoffComponentEuclid_hasCompactSupport' (I := I) (M := M)
        g r s S α Idx Jdx)
      (cutoffComponentEuclid_tsupport_subset' (I := I) (M := M)
        g r s S α Idx Jdx)
      hp_one 1
  exact MemWkp.one_iff_memW1p.mp h_W1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_memW1p then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_memW1p"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_memW1p ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_memW1p

omit [NeZero (Module.finrank ℝ E)] in
lemma chosenWeakPartialOrZero_cutoffComponentEuclid_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.MemLp
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  have h := chosenWeakPartialOrZero_memLp_of_mem
    (cutoffComponentEuclid_memW1p (I := I) (M := M) g r s S α Idx Jdx) k
  rwa [chartLebesgueMeasure]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_cutoffComponentEuclid_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_cutoffComponentEuclid_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_cutoffComponentEuclid_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_cutoffComponentEuclid_memLp

private def smoothCutoffChartPartialLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  (chosenWeakPartialOrZero_cutoffComponentEuclid_memLp
    (I := I) (M := M) g r s S α P₀.1 P₀.2 k).toLp _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLp target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothCutoffChartPartialLp_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ((smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) := by
  unfold smoothCutoffChartPartialLp
  exact MemLp.coeFn_toLp _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLp_coeFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLp_coeFn target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothCutoffChartPartialLp_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    smoothCutoffChartPartialLp (I := I) (M := M) g r s (S₁ + S₂) α P₀ k =
      smoothCutoffChartPartialLp (I := I) (M := M) g r s S₁ α P₀ k +
        smoothCutoffChartPartialLp (I := I) (M := M) g r s S₂ α P₀ k := by
  classical
  apply Lp.ext
  have h_fun :
      cutoffComponentEuclid (I := I) (M := M) g r s
          (S₁ + S₂).toCcTensor α P₀.1 P₀.2 =
        (fun y => cutoffComponentEuclid (I := I) (M := M)
            g r s S₁.toCcTensor α P₀.1 P₀.2 y +
          cutoffComponentEuclid (I := I) (M := M)
            g r s S₂.toCcTensor α P₀.1 P₀.2 y) := by
    rw [SmoothCcTensorH1.toCcTensor_add,
      cutoffComponentEuclid_add (I := I) (M := M)
        g r s S₁.toCcTensor S₂.toCcTensor α P₀.1 P₀.2]
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_partial_ae :
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (S₁ + S₂).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      (fun y =>
        chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S₁.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α) y +
          chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S₂.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α) y) := by
    rw [chartLebesgueMeasure, h_fun]
    exact chosenWeakPartialOrZero_add_ae (d := Module.finrank ℝ E) hp_one hΩ_open
      (cutoffComponentEuclid_memW1p (I := I) (M := M) g r s S₁ α P₀.1 P₀.2)
      (cutoffComponentEuclid_memW1p (I := I) (M := M) g r s S₂ α P₀.1 P₀.2) k
  refine (smoothCutoffChartPartialLp_coeFn
    (I := I) (M := M) g r s (S₁ + S₂) α P₀ k).trans (h_partial_ae.trans ?_)
  have h_add :=
    Lp.coeFn_add (smoothCutoffChartPartialLp (I := I) (M := M) g r s S₁ α P₀ k)
      (smoothCutoffChartPartialLp (I := I) (M := M) g r s S₂ α P₀ k)
  refine (Filter.EventuallyEq.add
    (smoothCutoffChartPartialLp_coeFn (I := I) (M := M) g r s S₁ α P₀ k)
    (smoothCutoffChartPartialLp_coeFn (I := I) (M := M) g r s S₂ α P₀ k)).symm.trans
    h_add.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLp_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLp_add target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothCutoffChartPartialLp_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    smoothCutoffChartPartialLp (I := I) (M := M) g r s (c • S) α P₀ k =
      c • smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k := by
  classical
  apply Lp.ext
  have h_fun :
      cutoffComponentEuclid (I := I) (M := M) g r s
          (c • S).toCcTensor α P₀.1 P₀.2 =
        (fun y => c • cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2 y) := by
    rw [SmoothCcTensorH1.toCcTensor_smul,
      cutoffComponentEuclid_smul (I := I) (M := M)
        g r s c S.toCcTensor α P₀.1 P₀.2]
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_partial_ae :
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (c • S).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      (fun y => c * chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M)
          g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) y) := by
    rw [chartLebesgueMeasure]
    have h_fun' :
        cutoffComponentEuclid (I := I) (M := M) g r s
            (c • S).toCcTensor α P₀.1 P₀.2 =
          (fun y => c * cutoffComponentEuclid (I := I) (M := M)
              g r s S.toCcTensor α P₀.1 P₀.2 y) := by
      rw [h_fun]; funext y; rw [smul_eq_mul]
    rw [h_fun']
    exact chosenWeakPartialOrZero_const_smul_ae (d := Module.finrank ℝ E) hp_one hΩ_open
      (cutoffComponentEuclid_memW1p (I := I) (M := M) g r s S α P₀.1 P₀.2) c k
  refine (smoothCutoffChartPartialLp_coeFn
    (I := I) (M := M) g r s (c • S) α P₀ k).trans (h_partial_ae.trans ?_)
  have h_smul :=
    Lp.coeFn_smul c (smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k)
  refine Filter.EventuallyEq.trans ?_ h_smul.symm
  filter_upwards [smoothCutoffChartPartialLp_coeFn
    (I := I) (M := M) g r s S α P₀ k] with y hy
  rw [Pi.smul_apply, hy, smul_eq_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLp_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLp_smul target :: scope.openDecls } }

private def smoothCutoffChartPartialLpLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    SmoothCcTensorH1 g r s →ₗ[ℝ] _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) where
  toFun S := smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k
  map_add' S₁ S₂ :=
    smoothCutoffChartPartialLp_add (I := I) (M := M) g r s S₁ S₂ α P₀ k
  map_smul' c S :=
    smoothCutoffChartPartialLp_smul (I := I) (M := M) g r s c S α P₀ k

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLpLin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLpLin target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma smoothCutoffChartPartialLpLin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (S : SmoothCcTensorH1 g r s) :
    smoothCutoffChartPartialLpLin (I := I) (M := M) g r s α P₀ k S =
      smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLpLin_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLpLin_apply target :: scope.openDecls } }

private lemma smoothCutoffChartPartialLpLin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensorH1 g r s,
        ‖smoothCutoffChartPartialLpLin (I := I) (M := M) g r s α P₀ k S‖
          ≤ C * ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, h_bound⟩ :=
    exists_const_sum_eLpNorm_chosenWeakPartialOrZero_cutoffComponentEuclid_le_uniform
      (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S
  have h_sum := h_bound S P₀.1 P₀.2
  have h_single :
      eLpNorm (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ∑ j : Fin (Module.finrank ℝ E),
        eLpNorm (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 j
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) 2
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
    Finset.single_le_sum
      (f := fun j : Fin (Module.finrank ℝ E) =>
        eLpNorm (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 j
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) 2
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
      (fun j _ => zero_le) (Finset.mem_univ k)
  have h_eLp :
      eLpNorm (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        (chartLebesgueMeasure (I := I) (M := M) α) ≤
      ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
    rw [chartLebesgueMeasure]
    exact h_single.trans h_sum
  have h_norm_eq :
      ‖smoothCutoffChartPartialLpLin (I := I) (M := M) g r s α P₀ k S‖ =
        (_root_.MeasureTheory.eLpNorm (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
          (chartLebesgueMeasure (I := I) (M := M) α)).toReal := by
    rw [smoothCutoffChartPartialLpLin_apply]
    unfold smoothCutoffChartPartialLp
    exact MeasureTheory.Lp.norm_toLp _ _
  rw [h_norm_eq]
  have h_rhs_lt_top :
      ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top).ne
  have h_toReal_le :
      (_root_.MeasureTheory.eLpNorm (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M)
          g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α)) 2
        (chartLebesgueMeasure (I := I) (M := M) α)).toReal ≤
        (ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)).toReal :=
    ENNReal.toReal_mono h_rhs_lt_top h_eLp
  refine h_toReal_le.trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_nn,
    ENNReal.coe_toReal, coe_nnnorm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLpLin_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLpLin_norm_le target :: scope.openDecls } }

private def smoothCutoffChartPartialLpCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    SmoothCcTensorH1 g r s →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  (smoothCutoffChartPartialLpLin (I := I) (M := M) g r s α P₀ k).mkContinuous
    (smoothCutoffChartPartialLpLin_norm_le (I := I) (M := M) g r s α P₀ k).choose
    (smoothCutoffChartPartialLpLin_norm_le
      (I := I) (M := M) g r s α P₀ k).choose_spec.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLpCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLpCLM target :: scope.openDecls } }

@[simp] private lemma smoothCutoffChartPartialLpCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (S : SmoothCcTensorH1 g r s) :
    smoothCutoffChartPartialLpCLM (I := I) (M := M) g r s α P₀ k S =
      smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLpCLM_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCutoffChartPartialLpCLM_apply target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_smoothToTensorH1Compl'
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing (smoothToTensorH1Compl (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorH1Compl (I := I) (M := M) g r s :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensorH1 g r s)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.isUniformInducing_smoothToTensorH1Compl'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.isUniformInducing_smoothToTensorH1Compl' target :: scope.openDecls } }

def eigenvectorCutoffChartPartialCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    TensorH1Compl g r s →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  ContinuousLinearMap.extend
    (smoothCutoffChartPartialLpCLM (I := I) (M := M) g r s α P₀ k)
    (smoothToTensorH1Compl (I := I) (M := M) g r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialCLM

theorem eigenvectorCutoffChartPartialCLM_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s S) =
      smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k := by
  unfold eigenvectorCutoffChartPartialCLM
  rw [ContinuousLinearMap.extend_eq
    (smoothCutoffChartPartialLpCLM (I := I) (M := M) g r s α P₀ k)
    (denseRange_smoothToTensorH1Compl (I := I) (M := M) g r s)
    (isUniformInducing_smoothToTensorH1Compl' (I := I) (M := M) g r s) S]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialCLM_smoothToTensorH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialCLM_smoothToTensorH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialCLM_smoothToTensorH1Compl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialCLM_smoothToTensorH1Compl

def eigenvectorCutoffChartPartialLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  (i.fst.val)⁻¹ •
    eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
      (eigenvectorResolvent (I := I) (M := M) g r s i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp

theorem eigenvectorCutoffChartPartialLp_approx_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    (i.fst.val)⁻¹ •
        eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)) =
      (i.fst.val)⁻¹ •
        (chosenWeakPartialOrZero_cutoffComponentEuclid_memLp (I := I) (M := M)
          g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
          α P₀.1 P₀.2 k).toLp
          (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
            (cutoffComponentEuclid (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [eigenvectorCutoffChartPartialCLM_smoothToTensorH1Compl
    (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n) α P₀ k]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_approx_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_approx_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_approx_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_approx_eq

theorem eigenvectorCutoffChartPartialLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)))
      _root_.Filter.atTop
      (𝓝 (eigenvectorCutoffChartPartialLp (I := I) (M := M)
        g r s i α P₀ k)) := by
  have h_clm :=
    ((eigenvectorCutoffChartPartialCLM
        (I := I) (M := M) g r s α P₀ k).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  have h_smul := h_clm.const_smul (i.fst.val)⁻¹
  simp only [Function.comp_def] at h_smul
  exact h_smul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCutoffChartPartialLp_tendsto

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
