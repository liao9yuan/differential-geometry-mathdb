import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Curvature.Tensor0S

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.FiberBundle _root_.NormedSpace _root_.Filter _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

omit [I.Boundaryless] in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
theorem riemannSec_tensorCov_apply_eval
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (τ : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (Y : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun x : M => Tensor0SSpace r I x)⟯)
    (x : M) (u : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            riemannSec (tensorCov (I := I) g r s)
              (fun b => X b) (fun b => W b) (fun b => τ b) x) (Y x)) u =
      Tensor0SSpace.toModel
          (riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b)
            (fun b => (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from τ b) (Y b)) x) u -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from τ x)
            (riemannSec (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
              (fun b => X b) (fun b => W b) (fun b => Y b) x)) u := by
  classical
  have hkey :=
    HomConnection.riemannSec_homBundle_apply_eq I M
      (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x)
      (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
      (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
      (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
      X W τ Y x
  have heq :
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          riemannSec (tensorCov (I := I) g r s)
            (fun b => X b) (fun b => W b) (fun b => τ b) x) (Y x) =
        riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b)
            (HomConnection.pairedSection (M := M)
              (U := fun x : M => Tensor0SSpace r I x) (V := fun x : M => Tensor0SSpace s I x)
              (fun b => τ b) (fun b => Y b)) x -
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from τ x)
            (riemannSec (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
              (fun b => X b) (fun b => W b) (fun b => Y b) x) := hkey
  rw [heq, Tensor0SSpace.toModel_sub, sub_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.riemannSec_tensorCov_apply_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.riemannSec_tensorCov_apply_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.riemannSec_tensorCov_apply_eval ``Submission.DifferentialGeometry.Geometry.Connection.riemannSec_tensorCov_apply_eval

end Connection
end Geometry
end DifferentialGeometry

end
