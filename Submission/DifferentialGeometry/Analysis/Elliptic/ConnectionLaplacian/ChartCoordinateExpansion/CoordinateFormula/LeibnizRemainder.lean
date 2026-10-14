import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.CoordinateFormula.LeibnizCancellation
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.SecondCovDerivExpansion.SmoothExtensionComponent
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ComponentFormula

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Filter _root_.NormedSpace
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
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity

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

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma tensorChartComponentProjection_covApply_eq_covDerivComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (fun z : M => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k z)
            (fun z : M => T₀.toSection z) b)) =
      covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx
        ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
  classical
  have hb_source : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb_good
  have hb_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_source
  have hsymm_te : (toEuclidean (E := E)).symm
      ((toEuclidean (E := E)) ((extChartAt I α) b)) =
      (extChartAt I α) b :=
    (toEuclidean (E := E)).symm_apply_apply _
  have hpullback :
      (extChartAt I α).symm
          ((toEuclidean (E := E)).symm
              ((toEuclidean (E := E)) ((extChartAt I α) b))) = b := by
    rw [hsymm_te]; exact hb_inv
  rw [covDerivComponentEuclid_def]
  rw [hpullback]
  congr 1
  congr 1
  rw [covApply_apply]
  have hCovDerivAt : (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun (fun z : M => T₀.toSection z) b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b) =
      tensorCovDerivAt (I := I) (M := M) g r s T₀ b
        (tangentSpaceModelContinuousLinearEquiv (I := I) b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)) := by
    rw [tensorCovDerivAt_def]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [hCovDerivAt]
  exact tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
    (I := I) (M := M) g r s T₀ α k (b := b) hb_good

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorChartComponentProjection_covApply_eq_covDerivComponentEuclid
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorChartComponentProjection_covApply_eq_covDerivComponentEuclid target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma tensorChartComponentProjection_covApply_eq_T₀_expansion
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (fun z : M => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k z)
            (fun z : M => T₀.toSection z) b)) =
      euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
          ((toEuclidean (E := E)) ((extChartAt I α) b)) +
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α k Idx p.1 Jdx p.2
              ((toEuclidean (E := E)) ((extChartAt I α) b)) *
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2)
              ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
  classical
  rw [tensorChartComponentProjection_covApply_eq_covDerivComponentEuclid
    (I := I) (M := M) g r s α T₀ k Idx Jdx hb_good]
  have hb_source : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb_good
  have hb_target : (extChartAt I α) b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_source
  have hy_target :
      (toEuclidean (E := E)) ((extChartAt I α) b) ∈
        chartTargetEuclid (I := I) (M := M) α :=
    ⟨(extChartAt I α) b, hb_target, rfl⟩
  have hEqOn := covDerivComponentEuclid_eqOn (I := I) (M := M) g r s α T₀ k Idx
    Jdx hy_target
  simp only at hEqOn
  rw [hEqOn]
  rw [covDerivLowerOrderTerm_def]
  congr 1
  refine Finset.sum_congr rfl (fun p _ => ?_)
  congr 1
  exact (chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2)
    hy_target).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorChartComponentProjection_covApply_eq_T₀_expansion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorChartComponentProjection_covApply_eq_T₀_expansion target :: scope.openDecls } }

theorem chartLeibnizRemainder_eq_T₀_linear
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    chartLeibnizRemainder (I := I) (M := M) g r s α T₀ Idx Jdx b =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
              (mvfderiv (I := I) (fun z : M =>
                  chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                    g α i k z) b
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l b)) *
              (euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx
                      Jdx))
                  ((toEuclidean (E := E)) ((extChartAt I α) b)) +
                ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                        (Fin s → Fin (Module.finrank ℝ E)),
                  covDerivLowerOrderCoeff (I := I) (M := M) g r s α k Idx p.1
                      Jdx p.2
                      ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                    chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α
                        p.1 p.2)
                      ((toEuclidean (E := E)) ((extChartAt I α) b))) := by
  classical
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  rw [chartLeibnizRemainder_eq_firstDerivOnly
    (I := I) (M := M) g r s α T₀ Idx Jdx hb]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [tensorChartComponentProjection_covApply_eq_T₀_expansion
    (I := I) (M := M) g r s α T₀ k Idx Jdx hb_good]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartLeibnizRemainder_eq_T₀_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartLeibnizRemainder_eq_T₀_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartLeibnizRemainder_eq_T₀_linear ``Submission.DifferentialGeometry.Analysis.Elliptic.chartLeibnizRemainder_eq_T₀_linear

end Elliptic
end Analysis
end DifferentialGeometry

end
