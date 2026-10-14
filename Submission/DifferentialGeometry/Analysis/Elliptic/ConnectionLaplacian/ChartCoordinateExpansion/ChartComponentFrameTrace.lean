import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.FrameTrace
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs

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
theorem tensorChartComponentRaw_rawTensorConnLap_eq_chart_frame_trace_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (rawTensorConnLap (I := I) g r s
            (fun z : M => T₀.toSection z) b)) =
      ∑ i : Fin (Module.finrank ℝ E),
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
                  ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))) := by
  classical
  have hExp :
      rawTensorConnLap (I := I) g r s
          (fun z : M => T₀.toSection z) b =
        rawTensorConnLapFixedFrame (I := I) g r s
          (fun i : Fin (Module.finrank ℝ E) =>
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
          (fun z : M => T₀.toSection z) b :=
    rawTensorConnLap_eq_rawTensorConnLapFixedFrame
      (I := I) (M := M) g r s T₀ α hb
  have hSum :
      rawTensorConnLapFixedFrame (I := I) g r s
          (fun i : Fin (Module.finrank ℝ E) =>
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
          (fun z : M => T₀.toSection z) b =
        ∑ i : Fin (Module.finrank ℝ E),
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
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))) :=
    rawTensorConnLap_fixedFrame_def (I := I) g r s
      (fun i : Fin (Module.finrank ℝ E) =>
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
      (fun z : M => T₀.toSection z) b
  have hRaw_sum :
      rawTensorConnLap (I := I) g r s
          (fun z : M => T₀.toSection z) b =
        ∑ i : Fin (Module.finrank ℝ E),
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
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))) :=
    hExp.trans hSum
  set L : TensorRSSpace r s I b →L[ℝ] ℝ :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b) with hL
  have hApply : L (rawTensorConnLap (I := I) g r s
        (fun z : M => T₀.toSection z) b) =
      L (∑ i : Fin (Module.finrank ℝ E),
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
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))) :=
    congrArg L hRaw_sum
  rw [map_sum] at hApply
  simpa [hL, ContinuousLinearMap.comp_apply] using hApply

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorChartComponentRaw_rawTensorConnLap_eq_chart_frame_trace_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorChartComponentRaw_rawTensorConnLap_eq_chart_frame_trace_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorChartComponentRaw_rawTensorConnLap_eq_chart_frame_trace_sum ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorChartComponentRaw_rawTensorConnLap_eq_chart_frame_trace_sum

end Elliptic
end Analysis
end DifferentialGeometry
