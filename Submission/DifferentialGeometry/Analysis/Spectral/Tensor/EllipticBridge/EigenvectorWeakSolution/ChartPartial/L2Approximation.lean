import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.L2Approximation
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.UniformBound

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
private lemma tensorChartComponent_contDiff_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞
      (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) := by
  classical
  rw [tensorChartComponent_def]
  refine
    Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
    (I := I) (M := M) ?_ ?_
  · exact tensorChartComponentPou_contMDiff
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx
  · exact tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_contDiff_top
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_contDiff_top target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorChartComponent_hasCompactSupport''
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport
      (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) := by
  rw [tensorChartComponent_def]
  exact
    chartPushedRaw_smooth_hasCompactSupport_local
    (I := I) (M := M)
    (tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_hasCompactSupport''
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_hasCompactSupport'' target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorChartComponent_tsupport_subset'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      ⊆ chartTargetEuclid (I := I) (M := M) α := by
  rw [tensorChartComponent_def]
  exact
    tsupport_chartPushedRaw_subset_chartTargetEuclid
    (I := I) (M := M)
    (tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_tsupport_subset'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_tsupport_subset' target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorChartComponent_memW1p
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_W1 : MemWkp (d := Module.finrank ℝ E) 1 2
      (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_of_smooth_compactSupport (d := Module.finrank ℝ E) hΩ_open
      (tensorChartComponent_contDiff_top (I := I) (M := M) g r s S α Idx Jdx)
      (tensorChartComponent_hasCompactSupport'' (I := I) (M := M) g r s S α Idx Jdx)
      (tensorChartComponent_tsupport_subset' (I := I) (M := M) g r s S α Idx Jdx)
      hp_one 1
  exact MemWkp.one_iff_memW1p.mp h_W1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_memW1p then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_memW1p"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_memW1p ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_memW1p

omit [NeZero (Module.finrank ℝ E)] in
lemma chosenWeakPartialOrZero_tensorChartComponent_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.MemLp
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)) 2
      (chartLebesgueMeasure (I := I) (M := M) α) := by
  have h := chosenWeakPartialOrZero_memLp_of_mem
    (tensorChartComponent_memW1p (I := I) (M := M) g r s S α Idx Jdx) k
  rwa [chartLebesgueMeasure]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_tensorChartComponent_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_tensorChartComponent_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_tensorChartComponent_memLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_tensorChartComponent_memLp

private def smoothChartPartialLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  (chosenWeakPartialOrZero_tensorChartComponent_memLp
    (I := I) (M := M) g r s S α P₀.1 P₀.2 k).toLp _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLp target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartPartialLp_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ((smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartLebesgueMeasure (I := I) (M := M) α]
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) := by
  unfold smoothChartPartialLp
  exact MemLp.coeFn_toLp _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLp_coeFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLp_coeFn target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartPartialLp_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    smoothChartPartialLp (I := I) (M := M) g r s (S₁ + S₂) α P₀ k =
      smoothChartPartialLp (I := I) (M := M) g r s S₁ α P₀ k +
        smoothChartPartialLp (I := I) (M := M) g r s S₂ α P₀ k := by
  classical
  apply Lp.ext
  have h_fun :
      tensorChartComponent (I := I) (M := M) g r s
          (S₁ + S₂).toCcTensor α P₀.1 P₀.2 =
        (fun y => tensorChartComponent (I := I) (M := M)
            g r s S₁.toCcTensor α P₀.1 P₀.2 y +
          tensorChartComponent (I := I) (M := M)
            g r s S₂.toCcTensor α P₀.1 P₀.2 y) := by
    rw [SmoothCcTensorH1.toCcTensor_add,
      tensorChartComponent_add (I := I) (M := M)
        g r s S₁.toCcTensor S₂.toCcTensor α P₀.1 P₀.2]
    rfl
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_partial_ae :
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
          (tensorChartComponent (I := I) (M := M) g r s
            (S₁ + S₂).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      (fun y =>
        chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
            (tensorChartComponent (I := I) (M := M)
              g r s S₁.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α) y +
          chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
            (tensorChartComponent (I := I) (M := M)
              g r s S₂.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α) y) := by
    rw [chartLebesgueMeasure, h_fun]
    exact chosenWeakPartialOrZero_add_ae (d := Module.finrank ℝ E) hp_one hΩ_open
      (tensorChartComponent_memW1p (I := I) (M := M) g r s S₁ α P₀.1 P₀.2)
      (tensorChartComponent_memW1p (I := I) (M := M) g r s S₂ α P₀.1 P₀.2) k
  refine (smoothChartPartialLp_coeFn
    (I := I) (M := M) g r s (S₁ + S₂) α P₀ k).trans (h_partial_ae.trans ?_)
  have h_add :=
    Lp.coeFn_add (smoothChartPartialLp (I := I) (M := M) g r s S₁ α P₀ k)
      (smoothChartPartialLp (I := I) (M := M) g r s S₂ α P₀ k)
  refine (Filter.EventuallyEq.add
    (smoothChartPartialLp_coeFn (I := I) (M := M) g r s S₁ α P₀ k)
    (smoothChartPartialLp_coeFn (I := I) (M := M) g r s S₂ α P₀ k)).symm.trans
    h_add.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLp_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLp_add target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothChartPartialLp_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    smoothChartPartialLp (I := I) (M := M) g r s (c • S) α P₀ k =
      c • smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k := by
  classical
  apply Lp.ext
  have h_fun :
      tensorChartComponent (I := I) (M := M) g r s
          (c • S).toCcTensor α P₀.1 P₀.2 =
        (fun y => c * tensorChartComponent (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2 y) := by
    rw [SmoothCcTensorH1.toCcTensor_smul,
      tensorChartComponent_smul (I := I) (M := M)
        g r s c S.toCcTensor α P₀.1 P₀.2]
    rfl
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_partial_ae :
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
          (tensorChartComponent (I := I) (M := M) g r s
            (c • S).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      (fun y => c * chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M)
          g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) y) := by
    rw [chartLebesgueMeasure, h_fun]
    exact chosenWeakPartialOrZero_const_smul_ae (d := Module.finrank ℝ E) hp_one hΩ_open
      (tensorChartComponent_memW1p (I := I) (M := M) g r s S α P₀.1 P₀.2) c k
  refine (smoothChartPartialLp_coeFn
    (I := I) (M := M) g r s (c • S) α P₀ k).trans (h_partial_ae.trans ?_)
  have h_smul :=
    Lp.coeFn_smul c (smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k)
  refine Filter.EventuallyEq.trans ?_ h_smul.symm
  filter_upwards [smoothChartPartialLp_coeFn
    (I := I) (M := M) g r s S α P₀ k] with y hy
  rw [Pi.smul_apply, hy, smul_eq_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLp_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLp_smul target :: scope.openDecls } }

private def smoothChartPartialLpLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    SmoothCcTensorH1 g r s →ₗ[ℝ] _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) where
  toFun S := smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k
  map_add' S₁ S₂ :=
    smoothChartPartialLp_add (I := I) (M := M) g r s S₁ S₂ α P₀ k
  map_smul' c S :=
    smoothChartPartialLp_smul (I := I) (M := M) g r s c S α P₀ k

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLpLin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLpLin target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma smoothChartPartialLpLin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (S : SmoothCcTensorH1 g r s) :
    smoothChartPartialLpLin (I := I) (M := M) g r s α P₀ k S =
      smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLpLin_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLpLin_apply target :: scope.openDecls } }

private lemma smoothChartPartialLpLin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensorH1 g r s,
        ‖smoothChartPartialLpLin (I := I) (M := M) g r s α P₀ k S‖ ≤ C * ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, h_bound⟩ :=
    exists_const_sum_eLpNorm_chosenWeakPartialOrZero_tensorChartComponent_le_uniform
      (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S
  have h_sum := h_bound S P₀.1 P₀.2
  have h_single :
      eLpNorm (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
          (tensorChartComponent (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ∑ j : Fin (Module.finrank ℝ E),
        eLpNorm (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 j
            (tensorChartComponent (I := I) (M := M)
              g r s S.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) 2
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
    Finset.single_le_sum
      (f := fun j : Fin (Module.finrank ℝ E) =>
        eLpNorm (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 j
            (tensorChartComponent (I := I) (M := M)
              g r s S.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) 2
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
      (fun j _ => zero_le) (Finset.mem_univ k)
  have h_eLp :
      eLpNorm (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
          (tensorChartComponent (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        (chartLebesgueMeasure (I := I) (M := M) α) ≤
      ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
    rw [chartLebesgueMeasure]
    exact h_single.trans h_sum
  have h_norm_eq :
      ‖smoothChartPartialLpLin (I := I) (M := M) g r s α P₀ k S‖ =
        (_root_.MeasureTheory.eLpNorm (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
          (tensorChartComponent (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
          (chartLebesgueMeasure (I := I) (M := M) α)).toReal := by
    rw [smoothChartPartialLpLin_apply]
    unfold smoothChartPartialLp
    exact MeasureTheory.Lp.norm_toLp _ _
  rw [h_norm_eq]
  have h_rhs_lt_top :
      ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top).ne
  have h_toReal_le :
      (_root_.MeasureTheory.eLpNorm (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M)
          g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α)) 2
        (chartLebesgueMeasure (I := I) (M := M) α)).toReal ≤
        (ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)).toReal :=
    ENNReal.toReal_mono h_rhs_lt_top h_eLp
  refine h_toReal_le.trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_nn,
    ENNReal.coe_toReal, coe_nnnorm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLpLin_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLpLin_norm_le target :: scope.openDecls } }

private def smoothChartPartialLpCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    SmoothCcTensorH1 g r s →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  (smoothChartPartialLpLin (I := I) (M := M) g r s α P₀ k).mkContinuous
    (smoothChartPartialLpLin_norm_le (I := I) (M := M) g r s α P₀ k).choose
    (smoothChartPartialLpLin_norm_le (I := I) (M := M) g r s α P₀ k).choose_spec.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLpCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLpCLM target :: scope.openDecls } }

@[simp] private lemma smoothChartPartialLpCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (S : SmoothCcTensorH1 g r s) :
    smoothChartPartialLpCLM (I := I) (M := M) g r s α P₀ k S =
      smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLpCLM_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothChartPartialLpCLM_apply target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing (smoothToTensorH1Compl (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorH1Compl (I := I) (M := M) g r s :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensorH1 g r s)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.isUniformInducing_smoothToTensorH1Compl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.isUniformInducing_smoothToTensorH1Compl target :: scope.openDecls } }

def eigenvectorChartPartialCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    TensorH1Compl g r s →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  ContinuousLinearMap.extend
    (smoothChartPartialLpCLM (I := I) (M := M) g r s α P₀ k)
    (smoothToTensorH1Compl (I := I) (M := M) g r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialCLM

theorem eigenvectorChartPartialCLM_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s S) =
      smoothChartPartialLp (I := I) (M := M) g r s S α P₀ k := by
  unfold eigenvectorChartPartialCLM
  rw [ContinuousLinearMap.extend_eq
    (smoothChartPartialLpCLM (I := I) (M := M) g r s α P₀ k)
    (denseRange_smoothToTensorH1Compl (I := I) (M := M) g r s)
    (isUniformInducing_smoothToTensorH1Compl (I := I) (M := M) g r s) S]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialCLM_smoothToTensorH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialCLM_smoothToTensorH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialCLM_smoothToTensorH1Compl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialCLM_smoothToTensorH1Compl

def eigenvectorChartPartialLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  (i.fst.val)⁻¹ •
    eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
      (eigenvectorResolvent (I := I) (M := M) g r s i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialLp

theorem eigenvectorChartPartialLp_approx_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    (i.fst.val)⁻¹ •
        eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)) =
      (i.fst.val)⁻¹ •
        (chosenWeakPartialOrZero_tensorChartComponent_memLp (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
          α P₀.1 P₀.2 k).toLp
          (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
            (tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [eigenvectorChartPartialCLM_smoothToTensorH1Compl
    (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n) α P₀ k]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialLp_approx_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialLp_approx_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialLp_approx_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialLp_approx_eq

theorem eigenvectorChartPartialLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)))
      _root_.Filter.atTop
      (𝓝 (eigenvectorChartPartialLp (I := I) (M := M)
        g r s i α P₀ k)) := by
  have h_clm :=
    ((eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k).continuous.tendsto
      _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  have h_smul := h_clm.const_smul (i.fst.val)⁻¹
  simp only [Function.comp_def] at h_smul
  exact h_smul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialLp_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialLp_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialLp_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartPartialLp_tendsto

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
