import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.CoordinateFormula.Decomposition
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.ChartPullbackSmoothness.LeviCivitaChartFrameSelfChartCoordPullback
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.SecondCovDerivExpansion.SmoothExtensionComponent
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ComponentFormula
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartForm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private noncomputable def chartModelBasisProjE (m : Fin (Module.finrank ℝ E)) :
    E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.proj m).comp ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun.toLinearMap)) :
      E →ₗ[ℝ] ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartModelBasisProjE
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartModelBasisProjE target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma chartModelBasisProjE_apply (m : Fin (Module.finrank ℝ E))
    (v : E) :
    chartModelBasisProjE (E := E) m v =
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) m := by
  classical
  unfold chartModelBasisProjE
  change ((LinearMap.proj m).comp ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun.toLinearMap)) v = _
  rw [LinearMap.comp_apply]
  simp [Module.Basis.equivFun]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartModelBasisProjE_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartModelBasisProjE_apply target :: scope.openDecls } }

private noncomputable def leviCivitaFrameSelfCoord
    (g : SmoothRiemannianMetric I M) (α : M)
    (i m : Fin (Module.finrank ℝ E)) (b : M) : ℝ := by
  classical
  exact
    if h : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet then
      (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) α h).repr
        ((LeviCivita (I := I) g).toFun
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)) m
    else 0

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.leviCivitaFrameSelfCoord
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.leviCivitaFrameSelfCoord target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [BoundarylessManifold I M] in
private lemma lcFrameSelfCoord_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    (i m : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    leviCivitaFrameSelfCoord (I := I) (M := M) g α i m b =
      (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) α hb).repr
        ((LeviCivita (I := I) g).toFun
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)) m := by
  classical
  unfold leviCivitaFrameSelfCoord
  rw [dif_pos hb]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.lcFrameSelfCoord_of_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.lcFrameSelfCoord_of_mem target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [BoundarylessManifold I M] in
private lemma lcFrameSelfCoord_eq_clmAt_proj
    (g : SmoothRiemannianMetric I M) (α : M)
    (i m : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    leviCivitaFrameSelfCoord (I := I) (M := M) g α i m b =
      chartModelBasisProjE (E := E) m
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))) := by
  classical
  rw [lcFrameSelfCoord_of_mem (I := I) (M := M) g α i m hb]
  unfold DifferentialGeometry.Tensor.Coordinates.chartBasisFamily
  rw [Module.Basis.map_repr]
  simp only [LinearEquiv.trans_apply]
  rw [chartModelBasisProjE_apply]
  congr 2
  have h := Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ)
    (e := _root_.FiberBundle.trivializationAt E (TangentSpace I) α) (b := b) hb
  exact congrArg (fun (f : TangentSpace I b → E) => f
    ((LeviCivita (I := I) g).toFun
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
      ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))) h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.lcFrameSelfCoord_eq_clmAt_proj
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.lcFrameSelfCoord_eq_clmAt_proj target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [BoundarylessManifold I M] in
private lemma lcFrameSelf_eq_lcFrameSelfCoord_sum
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (LeviCivita (I := I) g).toFun
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) =
      ∑ m : Fin (Module.finrank ℝ E),
        leviCivitaFrameSelfCoord (I := I) (M := M) g α i m b •
          DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b := by
  classical
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hsum := (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) α hb_base).sum_repr
      ((LeviCivita (I := I) g).toFun
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
  rw [← hsum]
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [lcFrameSelfCoord_of_mem (I := I) (M := M) g α i m hb_base]
  rw [DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply (I := I) α hb_base m]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.lcFrameSelf_eq_lcFrameSelfCoord_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.lcFrameSelf_eq_lcFrameSelfCoord_sum target :: scope.openDecls } }

private noncomputable def lcFrameSelfCoordPullback
    (g : SmoothRiemannianMetric I M) (α : M)
    (i m : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    chartModelBasisProjE (E := E) m
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        ((LeviCivita (I := I) g).toFun
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.lcFrameSelfCoordPullback
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.lcFrameSelfCoordPullback target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
private lemma lcFrameSelfCoordPullback_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (lcFrameSelfCoordPullback (I := I) (M := M) g α i m)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_sub4 :=
    leviCivita_chartFrame_self_chartCoord_pullback_contDiffOn_chartTarget
      (I := I) (M := M) g α i m
  refine h_sub4.congr (fun y _ => ?_)
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.lcFrameSelfCoordPullback_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.lcFrameSelfCoordPullback_contDiffOn target :: scope.openDecls } }

private noncomputable def chartFrameTraceΓPrincipalCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    (if I' = Idx ∧ J' = Jdx then (1 : ℝ) else 0) *
      ∑ i : Fin (Module.finrank ℝ E),
        lcFrameSelfCoordPullback (I := I) (M := M) g α i m y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓPrincipalCoeff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓPrincipalCoeff target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
private lemma chartFrameTraceΓPrincipalCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (chartFrameTraceΓPrincipalCoeff (I := I) (M := M) g r s α Idx Jdx I' J' m)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold chartFrameTraceΓPrincipalCoeff
  refine contDiffOn_const.mul ?_
  refine ContDiffOn.sum (fun i _ => ?_)
  exact lcFrameSelfCoordPullback_contDiffOn (I := I) (M := M) g α i m

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓPrincipalCoeff_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓPrincipalCoeff_contDiffOn target :: scope.openDecls } }

private noncomputable def chartFrameTraceΓZerothCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ m : Fin (Module.finrank ℝ E),
        lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx I' Jdx J' y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓZerothCoeff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓZerothCoeff target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
private lemma chartFrameTraceΓZerothCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (chartFrameTraceΓZerothCoeff (I := I) (M := M) g r s α Idx Jdx I' J')
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold chartFrameTraceΓZerothCoeff
  refine ContDiffOn.sum (fun i _ => ?_)
  refine ContDiffOn.sum (fun m _ => ?_)
  exact (lcFrameSelfCoordPullback_contDiffOn (I := I) (M := M) g α i m).mul
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx I' Jdx J')

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓZerothCoeff_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓZerothCoeff_contDiffOn target :: scope.openDecls } }

omit [I.Boundaryless] in
private lemma chart_α_proj_lcFrameSelfTraceSummand_eq_coord_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (fun z : M => T₀.toSection z) b
            ((LeviCivita (I := I) g).toFun
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))) =
      ∑ m : Fin (Module.finrank ℝ E),
        leviCivitaFrameSelfCoord (I := I) (M := M) g α i m b *
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))) := by
  classical
  rw [lcFrameSelf_eq_lcFrameSelfCoord_sum (I := I) (M := M) g α i hb]
  set L : TensorRSSpace r s I b →L[ℝ] ℝ :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b)
    with hL_def
  set Lcov : TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
      (fun z : M => T₀.toSection z) b
    with hLcov_def
  have hApply :
      L (Lcov (∑ m : Fin (Module.finrank ℝ E),
            leviCivitaFrameSelfCoord (I := I) (M := M) g α i m b •
              DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b)) =
        ∑ m : Fin (Module.finrank ℝ E),
          leviCivitaFrameSelfCoord (I := I) (M := M) g α i m b •
            L (Lcov (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b)) := by
    rw [map_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [Lcov.map_smul, L.map_smul]
  simp only [smul_eq_mul] at hApply
  simp only [hL_def, hLcov_def, ContinuousLinearMap.comp_apply] at hApply
  exact hApply

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chart_α_proj_lcFrameSelfTraceSummand_eq_coord_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chart_α_proj_lcFrameSelfTraceSummand_eq_coord_sum target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma chart_α_proj_covRS_T₀_at_chartBasisVec_eq_euclidPartial_plus_lower
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (fun z : M => T₀.toSection z) b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))) =
      euclidPartial (E := E) m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
        ((toEuclidean (E := E)) ((extChartAt I α) b)) +
      covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx
        ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
  classical
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  have hb_source : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_target : (extChartAt I α) b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_source
  have hy_mem : y ∈ chartTargetEuclid (I := I) (M := M) α :=
    ⟨(extChartAt I α) b, hb_target, rfl⟩
  have hsymm_te : (toEuclidean (E := E)).symm y = (extChartAt I α) b := by
    rw [hy_def]
    exact (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_source
  have hb_eq : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b := by
    rw [hsymm_te, hleft_inv]
  have hagree : tensorCovDerivAt (I := I) (M := M) g r s T₀ b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b) =
      chartTensorRSCovariantDerivative (I := I) r s g α T₀.toSection
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m) b :=
    tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
      (I := I) (M := M) g r s T₀ α m hb
  have hLHS_eq :
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (fun z : M => T₀.toSection z) b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b) =
      chartTensorRSCovariantDerivative (I := I) r s g α T₀.toSection
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m) b := by
    have htdef := tensorCovDerivAt_def (I := I) (M := M) g r s T₀ b
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b)
    exact htdef.symm.trans hagree
  rw [hLHS_eq]
  have hB1 := covDerivComponent_eq_euclidPartial_add_lowerOrder
    (I := I) (M := M) g r s T₀ α m Idx Jdx hy_mem
  rw [hb_eq] at hB1
  exact hB1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chart_α_proj_covRS_T₀_at_chartBasisVec_eq_euclidPartial_plus_lower
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chart_α_proj_covRS_T₀_at_chartBasisVec_eq_euclidPartial_plus_lower target :: scope.openDecls } }

theorem chartFrameTraceΓCorrection_eq_T₀_linear
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (Coeff_1 : (Fin r → Fin (Module.finrank ℝ E)) →
                  (Fin s → Fin (Module.finrank ℝ E)) →
                  Fin (Module.finrank ℝ E) →
                  EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
    ∃ (Coeff_0 : (Fin r → Fin (Module.finrank ℝ E)) →
                  (Fin s → Fin (Module.finrank ℝ E)) →
                  EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
      (∀ I' J' m, ContDiffOn ℝ ∞ (Coeff_1 I' J' m)
        (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J', ContDiffOn ℝ ∞ (Coeff_0 I' J')
        (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ (T₀ : SmoothCcTensor g r s),
        ∀ {b : M}, b ∈ chartLeviCivitaGoodSet (I := I) α →
        chartFrameTraceΓCorrection (I := I) (M := M) g r s α T₀ Idx Jdx b =
          (∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ m : Fin (Module.finrank ℝ E),
                Coeff_1 I' J' m ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                  euclidPartial (E := E) m
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
                    ((toEuclidean (E := E)) ((extChartAt I α) b))) +
          (∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              Coeff_0 I' J' ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) := by
  classical
  refine ⟨chartFrameTraceΓPrincipalCoeff (I := I) (M := M) g r s α Idx Jdx,
          chartFrameTraceΓZerothCoeff (I := I) (M := M) g r s α Idx Jdx,
          ?_, ?_, ?_⟩
  · intro I' J' m
    exact chartFrameTraceΓPrincipalCoeff_contDiffOn
      (I := I) (M := M) g r s α Idx Jdx I' J' m
  · intro I' J'
    exact chartFrameTraceΓZerothCoeff_contDiffOn
      (I := I) (M := M) g r s α Idx Jdx I' J'
  · intro T₀ b hb
    set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
      (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
    have hb_source : b ∈ (extChartAt I α).source :=
      chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
    have hb_target : (extChartAt I α) b ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hb_source
    have hy_mem : y ∈ chartTargetEuclid (I := I) (M := M) α :=
      ⟨(extChartAt I α) b, hb_target, rfl⟩
    have hsymm_te : (toEuclidean (E := E)).symm y = (extChartAt I α) b := by
      rw [hy_def]
      exact (toEuclidean (E := E)).symm_apply_apply _
    have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
      (extChartAt I α).left_inv hb_source
    have hb_eq : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b := by
      rw [hsymm_te, hleft_inv]
    unfold chartFrameTraceΓCorrection
    have hStep1 :
        (∑ i : Fin (Module.finrank ℝ E),
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                  ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            leviCivitaFrameSelfCoord (I := I) (M := M) g α i m b *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                  ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g)).toFun
                    (fun z : M => T₀.toSection z) b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact chart_α_proj_lcFrameSelfTraceSummand_eq_coord_sum
        (I := I) (M := M) g r s α T₀ Idx Jdx i hb
    rw [hStep1]
    have hStep2 :
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            leviCivitaFrameSelfCoord (I := I) (M := M) g α i m b *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                  ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g)).toFun
                    (fun z : M => T₀.toSection z) b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b)))) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            leviCivitaFrameSelfCoord (I := I) (M := M) g α i m b *
              (euclidPartial (E := E) m
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y +
                covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [chart_α_proj_covRS_T₀_at_chartBasisVec_eq_euclidPartial_plus_lower
        (I := I) (M := M) g r s α T₀ m Idx Jdx hb]
    rw [hStep2]
    have hcoord_eq : ∀ i m : Fin (Module.finrank ℝ E),
        leviCivitaFrameSelfCoord (I := I) (M := M) g α i m b =
        lcFrameSelfCoordPullback (I := I) (M := M) g α i m y := by
      intro i m
      have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
        chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
      rw [lcFrameSelfCoord_eq_clmAt_proj (I := I) (M := M) g α i m hb_base]
      unfold lcFrameSelfCoordPullback
      rw [hb_eq]
    have hStep3 :
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            leviCivitaFrameSelfCoord (I := I) (M := M) g α i m b *
              (euclidPartial (E := E) m
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y +
                covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
              (euclidPartial (E := E) m
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y +
                covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hcoord_eq i m]
    rw [hStep3]
    have hStep4 :
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
              (euclidPartial (E := E) m
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y +
                covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
              euclidPartial (E := E) m
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y) +
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hStep4]
    have hPrincipal_block_eq :
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
              euclidPartial (E := E) m
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              chartFrameTraceΓPrincipalCoeff
                  (I := I) (M := M) g r s α Idx Jdx I' J' m y *
                euclidPartial (E := E) m
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y := by
      rw [Finset.sum_comm]
      have hLHS :
          (∑ m : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E),
              lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
                euclidPartial (E := E) m
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y) =
          ∑ m : Fin (Module.finrank ℝ E),
            (∑ i : Fin (Module.finrank ℝ E),
                lcFrameSelfCoordPullback (I := I) (M := M) g α i m y) *
              euclidPartial (E := E) m
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.sum_mul]
      rw [hLHS]
      have hRHS :
          (∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ m : Fin (Module.finrank ℝ E),
                chartFrameTraceΓPrincipalCoeff
                    (I := I) (M := M) g r s α Idx Jdx I' J' m y *
                  euclidPartial (E := E) m
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y) =
          ∑ m : Fin (Module.finrank ℝ E),
            (∑ i : Fin (Module.finrank ℝ E),
                lcFrameSelfCoordPullback (I := I) (M := M) g α i m y) *
              euclidPartial (E := E) m
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y := by
        rw [Finset.sum_eq_single Idx]
        · rw [Finset.sum_eq_single Jdx]
          · refine Finset.sum_congr rfl (fun m _ => ?_)
            unfold chartFrameTraceΓPrincipalCoeff
            simp [and_self]
          · intro J' _ hJne
            refine Finset.sum_eq_zero (fun m _ => ?_)
            unfold chartFrameTraceΓPrincipalCoeff
            simp [hJne]
          · intro hJ; exact absurd (Finset.mem_univ _) hJ
        · intro I' _ hIne
          refine Finset.sum_eq_zero (fun J' _ => ?_)
          refine Finset.sum_eq_zero (fun m _ => ?_)
          unfold chartFrameTraceΓPrincipalCoeff
          simp [hIne]
        · intro hI; exact absurd (Finset.mem_univ _) hI
      rw [hRHS]
    have hZeroth_block_eq :
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            chartFrameTraceΓZerothCoeff
                (I := I) (M := M) g r s α Idx Jdx I' J' y *
              chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
                y := by
      have hLowerEq : ∀ m,
          covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y =
          ∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx I' Jdx J' y *
                chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J') y := by
        intro m
        rw [covDerivComponent_lowerOrder_eq_linearCombination
          (I := I) (M := M) g r s T₀ α m Idx Jdx y]
        rw [← Finset.sum_product']
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2) hy_mem]
      have hSubst :
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
                covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              ∑ I' : Fin r → Fin (Module.finrank ℝ E),
                ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                  lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
                    (covDerivLowerOrderCoeff (I := I) (M := M)
                        g r s α m Idx I' Jdx J' y *
                      chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s T₀ α I' J') y) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [hLowerEq m, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun I' _ => ?_)
        rw [Finset.mul_sum]
      rw [hSubst]
      have hReorder :
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              ∑ I' : Fin r → Fin (Module.finrank ℝ E),
                ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                  lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
                    (covDerivLowerOrderCoeff (I := I) (M := M)
                        g r s α m Idx I' Jdx J' y *
                      chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s T₀ α I' J') y)) =
          ∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ m : Fin (Module.finrank ℝ E),
                  lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
                    (covDerivLowerOrderCoeff (I := I) (M := M)
                        g r s α m Idx I' Jdx J' y *
                      chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s T₀ α I' J') y) := by
        have h1 :
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ m : Fin (Module.finrank ℝ E),
                ∑ I' : Fin r → Fin (Module.finrank ℝ E),
                  ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                    lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
                      (covDerivLowerOrderCoeff (I := I) (M := M)
                          g r s α m Idx I' Jdx J' y *
                        chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s T₀ α I' J') y)) =
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ I' : Fin r → Fin (Module.finrank ℝ E),
                ∑ m : Fin (Module.finrank ℝ E),
                  ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                    lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
                      (covDerivLowerOrderCoeff (I := I) (M := M)
                          g r s α m Idx I' Jdx J' y *
                        chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s T₀ α I' J') y) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_comm]
        rw [h1]
        rw [Finset.sum_comm]
        have h3 :
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ m : Fin (Module.finrank ℝ E),
                  ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                    lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
                      (covDerivLowerOrderCoeff (I := I) (M := M)
                          g r s α m Idx I' Jdx J' y *
                        chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s T₀ α I' J') y)) =
            ∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                  ∑ m : Fin (Module.finrank ℝ E),
                    lcFrameSelfCoordPullback (I := I) (M := M) g α i m y *
                      (covDerivLowerOrderCoeff (I := I) (M := M)
                          g r s α m Idx I' Jdx J' y *
                        chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s T₀ α I' J') y) := by
          refine Finset.sum_congr rfl (fun I' _ => ?_)
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_comm]
        rw [h3]
        refine Finset.sum_congr rfl (fun I' _ => ?_)
        rw [Finset.sum_comm]
      rw [hReorder]
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      refine Finset.sum_congr rfl (fun J' _ => ?_)
      unfold chartFrameTraceΓZerothCoeff
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hPrincipal_block_eq, hZeroth_block_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓCorrection_eq_T₀_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓCorrection_eq_T₀_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓCorrection_eq_T₀_linear ``Submission.DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓCorrection_eq_T₀_linear

end Elliptic
end Analysis
end DifferentialGeometry

end
