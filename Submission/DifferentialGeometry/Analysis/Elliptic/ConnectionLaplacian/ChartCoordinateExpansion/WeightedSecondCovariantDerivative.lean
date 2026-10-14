import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.ChartComponentFrameTrace
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.LocalizedFrame.Coordinates
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Iterates

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
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

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

omit [I.Boundaryless] in
private lemma covRS_covApply_B_i_T₀_at_B_i_eq_coord_sum_outer
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (i : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
          (fun z : M => T₀.toSection z)) b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b •
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
              (fun z : M => T₀.toSection z)) b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l b) := by
  classical
  have hExpand :
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b =
        ∑ l : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b •
            DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l b := by
    have h := chartFrameNormGlobalSmooth_eq_coordMatrix_sum
      (I := I) (M := M) g α i (b := b) hb
    have hcoerce : ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i :
          Π b : M, TangentSpace I b) b)
        = (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b := rfl
    rw [hcoerce] at h
    exact h
  rw [hExpand]
  set Lcov : TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
      (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g))
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
        (fun z : M => T₀.toSection z)) b
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Lcov.map_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.covRS_covApply_B_i_T₀_at_B_i_eq_coord_sum_outer
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.covRS_covApply_B_i_T₀_at_B_i_eq_coord_sum_outer target :: scope.openDecls } }

omit [I.Boundaryless] in
private lemma chart_α_proj_covRS_covApply_B_i_T₀_at_B_i_eq_coord_sum_outer
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                (fun z : M => T₀.toSection z)) b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                    (fun z : M => T₀.toSection z)) b
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l b))) := by
  classical
  rw [covRS_covApply_B_i_T₀_at_B_i_eq_coord_sum_outer
      (I := I) (M := M) g r s α T₀ i (b := b) hb]
  set L : TensorRSSpace r s I b →L[ℝ] ℝ :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b)
    with hL_def
  have hApply :
      L (∑ l : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b •
              (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  (fun z : M => T₀.toSection z)) b
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l b)) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b •
            L ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  (fun z : M => T₀.toSection z)) b
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l b)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [L.map_smul]
  simp only [hL_def, ContinuousLinearMap.comp_apply, smul_eq_mul] at hApply
  exact hApply

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chart_α_proj_covRS_covApply_B_i_T₀_at_B_i_eq_coord_sum_outer
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chart_α_proj_covRS_covApply_B_i_T₀_at_B_i_eq_coord_sum_outer target :: scope.openDecls } }

omit [I.Boundaryless] in
theorem chartPushed_rawConnLap_chart_α_proj_eq_weighted_secondCovDeriv_minus_frameTraceΓ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                    (fun z : M => T₀.toSection z)) b
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l b)))) -
      (∑ i : Fin (Module.finrank ℝ E),
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))) := by
  classical
  have hLHS_eq :
      tensorChartComponentRaw (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (rawTensorConnLap (I := I) g r s
              (fun z : M => T₀.toSection z) b)) := by
    unfold tensorChartComponentRaw tensorTrivProj
    rw [rawTensorConnLapSmooth_toSection_apply (I := I) g r s T₀ b]
  rw [hLHS_eq]
  have hStep2 :=
    tensorChartComponentRaw_rawTensorConnLap_eq_chart_frame_trace_sum
      (I := I) (M := M) g r s α T₀ Idx Jdx (b := b) hb
  rw [hStep2]
  have hperI : ∀ i : Fin (Module.finrank ℝ E),
      tensorChartComponentProjection (E := E) r s Idx Jdx
          ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  (fun z : M => T₀.toSection z)) b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) -
              (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                  ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))) =
        (∑ l : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                  ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g)).toFun
                    (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g))
                      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                      (fun z : M => T₀.toSection z)) b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l b)))) -
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                  ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))) := by
    intro i
    rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_sub]
    rw [chart_α_proj_covRS_covApply_B_i_T₀_at_B_i_eq_coord_sum_outer
        (I := I) (M := M) g r s α T₀ Idx Jdx i (b := b) hb.2]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  (fun z : M => T₀.toSection z)) b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) -
              (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                  ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))) =
      ∑ i : Fin (Module.finrank ℝ E),
        ((∑ l : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                  ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g)).toFun
                    (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g))
                      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                      (fun z : M => T₀.toSection z)) b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l b)))) -
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                  ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))) from
    Finset.sum_congr rfl (fun i _ => hperI i)]
  rw [Finset.sum_sub_distrib]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLap_chart_α_proj_eq_weighted_secondCovDeriv_minus_frameTraceΓ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLap_chart_α_proj_eq_weighted_secondCovDeriv_minus_frameTraceΓ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLap_chart_α_proj_eq_weighted_secondCovDeriv_minus_frameTraceΓ ``Submission.DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLap_chart_α_proj_eq_weighted_secondCovDeriv_minus_frameTraceΓ

end Elliptic
end Analysis
end DifferentialGeometry

end
