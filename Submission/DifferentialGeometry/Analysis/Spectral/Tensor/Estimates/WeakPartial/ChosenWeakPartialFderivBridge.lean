import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.WeakPartial.ComponentSobolevBoundDerivBridge
import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence.IntrinsicToChart.ComponentNormBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
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

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EuclN
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EuclN target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartSmoothExt
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN E => fderiv ℝ
        (chartSmoothExt (I := I) (M := M) α
          (fun z : M => ((chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
          (EuclideanSpace.single k (1 : ℝ))) := by
  have hp_one : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
  exact
    Analysis.Sobolev.EquivalenceReverse.chosenWeakPartial_chartPushed_ae_eq_fderiv
    (I := I) (M := M) α hp_one hu k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartSmoothExt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartSmoothExt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartSmoothExt ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartSmoothExt

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem chartPushed_eq_chartSmoothExt_on_target
    (α : M) (u : M → ℝ) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u y =
      chartSmoothExt (I := I) (M := M) α
        (fun z : M => ((chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z) y :=
  (Analysis.Sobolev.EquivalenceReverse.chartSmoothExt_eq_chartPushed_pou_on_target
    (I := I) (M := M) α u hy).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_eq_chartSmoothExt_on_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_eq_chartSmoothExt_on_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_eq_chartSmoothExt_on_target ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_eq_chartSmoothExt_on_target

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem fderiv_chartPushed_eq_fderiv_chartSmoothExt_on_target
    (α : M) (u : M → ℝ) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    fderiv ℝ (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u) y =
      fderiv ℝ (chartSmoothExt (I := I) (M := M) α
        (fun z : M => ((chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_nhds : chartTargetEuclid (I := I) (M := M) α ∈ nhds y :=
    h_open.mem_nhds hy
  have h_eventually :
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u =ᶠ[nhds y]
        chartSmoothExt (I := I) (M := M) α
          (fun z : M => ((chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z) := by
    refine Filter.eventually_of_mem h_nhds ?_
    intro z hz
    exact chartPushed_eq_chartSmoothExt_on_target (I := I) (M := M) α u hz
  exact Filter.EventuallyEq.fderiv_eq h_eventually

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_chartPushed_eq_fderiv_chartSmoothExt_on_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_chartPushed_eq_fderiv_chartSmoothExt_on_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_chartPushed_eq_fderiv_chartSmoothExt_on_target ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_chartPushed_eq_fderiv_chartSmoothExt_on_target

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartPushed
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN E => fderiv ℝ
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u) y
          (EuclideanSpace.single k (1 : ℝ))) := by
  classical
  have h_smooth_form :=
    chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartSmoothExt
      (I := I) (M := M) (α := α) (u := u) hu k
  have h_fderiv_eq_ae :
      (fun y : EuclN E => fderiv ℝ
        (chartSmoothExt (I := I) (M := M) α
          (fun z : M => ((chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
          (EuclideanSpace.single k (1 : ℝ)))
        =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclN E)).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN E => fderiv ℝ
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u) y
          (EuclideanSpace.single k (1 : ℝ))) := by
    have h_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    refine Filter.eventually_of_mem (_root_.MeasureTheory.self_mem_ae_restrict h_meas) ?_
    intro y hy
    simp only
    rw [fderiv_chartPushed_eq_fderiv_chartSmoothExt_on_target
      (I := I) (M := M) α u hy]
  exact h_smooth_form.trans h_fderiv_eq_ae

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartPushed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartPushed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartPushed ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartPushed

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartSmoothExt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx))
        (chartTargetEuclid (I := I) (M := M) β)
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) β)]
      (fun y : EuclN E => fderiv ℝ
        (chartSmoothExt (I := I) (M := M) β
          (fun z : M => ((chartAtlasPOU I M β
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
            tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx z)) y
          (EuclideanSpace.single k (1 : ℝ))) :=
  chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartSmoothExt
    (I := I) (M := M) (α := β)
    (u := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartSmoothExt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartSmoothExt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartSmoothExt ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartSmoothExt

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx))
        (chartTargetEuclid (I := I) (M := M) β)
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) β)]
      (fun y : EuclN E => fderiv ℝ
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) y
          (EuclideanSpace.single k (1 : ℝ))) :=
  chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartPushed
    (I := I) (M := M) (α := β)
    (u := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartPushed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartPushed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartPushed ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartPushed

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chosenWeakPartialOrZero_chartPushed_eq_eLpNorm_fderiv_chartSmoothExt
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) =
      _root_.MeasureTheory.eLpNorm
        (fun y : EuclN E => fderiv ℝ
          (chartSmoothExt (I := I) (M := M) α
            (fun z : M => ((chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
            (EuclideanSpace.single k (1 : ℝ))) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
  _root_.MeasureTheory.eLpNorm_congr_ae
    (chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartSmoothExt
      (I := I) (M := M) (α := α) (u := u) hu k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_eq_eLpNorm_fderiv_chartSmoothExt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_eq_eLpNorm_fderiv_chartSmoothExt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_eq_eLpNorm_fderiv_chartSmoothExt ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_eq_eLpNorm_fderiv_chartSmoothExt

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chosenWeakPartialOrZero_chartPushed_eq_eLpNorm_fderiv_chartPushed
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) =
      _root_.MeasureTheory.eLpNorm
        (fun y : EuclN E => fderiv ℝ
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u) y
            (EuclideanSpace.single k (1 : ℝ))) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
  _root_.MeasureTheory.eLpNorm_congr_ae
    (chosenWeakPartialOrZero_chartPushed_ae_eq_fderiv_chartPushed
      (I := I) (M := M) (α := α) (u := u) hu k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_eq_eLpNorm_fderiv_chartPushed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_eq_eLpNorm_fderiv_chartPushed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_eq_eLpNorm_fderiv_chartPushed ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_eq_eLpNorm_fderiv_chartPushed

omit [NeZero (Module.finrank ℝ E)] in
theorem
    eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorComponentScalar_eq_eLpNorm_fderiv_chartSmoothExt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) β)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) =
      _root_.MeasureTheory.eLpNorm
        (fun y : EuclN E => fderiv ℝ
          (chartSmoothExt (I := I) (M := M) β
            (fun z : M => ((chartAtlasPOU I M β
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
              tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx z)) y
            (EuclideanSpace.single k (1 : ℝ))) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) :=
  eLpNorm_chosenWeakPartialOrZero_chartPushed_eq_eLpNorm_fderiv_chartSmoothExt
    (I := I) (M := M) (α := β)
    (u := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorComponentScalar_eq_eLpNorm_fderiv_chartSmoothExt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorComponentScalar_eq_eLpNorm_fderiv_chartSmoothExt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorComponentScalar_eq_eLpNorm_fderiv_chartSmoothExt ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorComponentScalar_eq_eLpNorm_fderiv_chartSmoothExt

omit [NeZero (Module.finrank ℝ E)] in
theorem
    eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_eq_eLpNorm_fderiv_chartPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) β)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) =
      _root_.MeasureTheory.eLpNorm
        (fun y : EuclN E => fderiv ℝ
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) y
            (EuclideanSpace.single k (1 : ℝ))) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) :=
  eLpNorm_chosenWeakPartialOrZero_chartPushed_eq_eLpNorm_fderiv_chartPushed
    (I := I) (M := M) (α := β)
    (u := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_eq_eLpNorm_fderiv_chartPushed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_eq_eLpNorm_fderiv_chartPushed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_eq_eLpNorm_fderiv_chartPushed ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_eq_eLpNorm_fderiv_chartPushed

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
