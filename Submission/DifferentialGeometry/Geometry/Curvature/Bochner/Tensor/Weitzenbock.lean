import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Curvature.Tensor0S
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Curvature.TensorRS
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.FiberBundle _root_.NormedSpace _root_.Filter _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem riemannSec_tensorCov_baseSlot_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) b (A b)))
    (x : M) (u : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval
        (riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (fun b => X b) (fun b => W b) A x) u =
      - ∑ k : Fin s,
          Tensor0SSpace.eval (A x)
            (Function.update u k (baseSlotCurv (I := I) g X W x (u k))) :=
  riemannSec_tensor0SCov_apply_eval (I := I) (M := M) g s X W A hA x u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemannSec_tensorCov_baseSlot_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemannSec_tensorCov_baseSlot_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemannSec_tensorCov_baseSlot_eval ``Submission.DifferentialGeometry.Geometry.Curvature.riemannSec_tensorCov_baseSlot_eval

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem smoothOrthoFrame_riemannOp_trace_eq_ricci
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (riemannOp (LeviCivita (I := I) g) x
          (smoothOrthoFrame (I := I) g x i x) v w)
          (smoothOrthoFrame (I := I) g x i x) =
      ricciTensor (I := I) g x v w :=
  (ricciTensor_eq_orthonormal_trace (I := I) g x v w
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.smoothOrthoFrame_riemannOp_trace_eq_ricci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.smoothOrthoFrame_riemannOp_trace_eq_ricci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.smoothOrthoFrame_riemannOp_trace_eq_ricci ``Submission.DifferentialGeometry.Geometry.Curvature.smoothOrthoFrame_riemannOp_trace_eq_ricci

end Curvature
end Geometry
end DifferentialGeometry

end
