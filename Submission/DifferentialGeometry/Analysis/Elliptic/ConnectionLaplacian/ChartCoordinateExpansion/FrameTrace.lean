import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.TensorConnLaplacian
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.LocalizedFrame.Basic
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs

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
theorem rawTensorConnLap_eq_rawTensorConnLapFixedFrame
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) {b : M}
    (hb : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α) :
    rawTensorConnLap (I := I) g r s
        (fun y : M => T.toSection y) b =
      rawTensorConnLapFixedFrame (I := I) g r s
        (fun i : Fin (Module.finrank ℝ E) =>
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
        (fun y : M => T.toSection y) b := by
  classical
  have hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T.toSection y)) :=
    T.toSection.contMDiff
  have hB_smooth : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) y
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun y)) :=
    fun i => (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).contMDiff
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α j).toFun b) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j =>
      chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet
        (I := I) (M := M) g α hb i j
  exact rawTensorConnLap_eq_fixedFrame_of_orthonormal (I := I) g r s
    (fun y : M => T.toSection y) hT_total
    (B := fun i : Fin (Module.finrank ℝ E) =>
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
    hB_smooth b hB_orth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLap_eq_rawTensorConnLapFixedFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.rawTensorConnLap_eq_rawTensorConnLapFixedFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.rawTensorConnLap_eq_rawTensorConnLapFixedFrame ``Submission.DifferentialGeometry.Analysis.Elliptic.rawTensorConnLap_eq_rawTensorConnLapFixedFrame

end Elliptic
end Analysis
end DifferentialGeometry
