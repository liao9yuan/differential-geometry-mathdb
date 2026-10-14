import Submission.DifferentialGeometry.Geometry.Connection.HomBundle.Basic
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Bundle _root_.Submission.Bundle _root_.CovariantDerivative _root_.Submission.CovariantDerivative
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace TensorRSNabla

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

noncomputable def tensorRSCovariantDerivative (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
  HomConnection.homBundleCovariantDerivative I M
    (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x)
    (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
    (Tensor0SNabla.tensor0SCovariantDerivative I M r cov)
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative ``Submission.DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative

noncomputable instance tensorRSCovariantDerivative_contMDiff (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative (tensorRSCovariantDerivative I M r s cov) ∞ :=
  HomConnection.homBundleCovariantDerivative_contMDiff I M
    (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x)
    (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
    (Tensor0SNabla.tensor0SCovariantDerivative I M r cov)
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative_contMDiff ``Submission.DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative_contMDiff

omit [CompleteSpace E] in
theorem tensorRSCovariantDerivative_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (τ : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun x : M => Tensor0SSpace r I x)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M r s cov τ x v) (w x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M s cov
        (fun y =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from τ y) (w y)) x v -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from τ x)
        (Tensor0SNabla.tensor0SCovariantDerivative I M r cov w x v) :=
  HomConnection.homBundleCovariantDerivative_apply I M
    (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x)
    (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
    (Tensor0SNabla.tensor0SCovariantDerivative I M r cov)
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov)
    τ w x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative_apply ``Submission.DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative_apply

omit [CompleteSpace E] in
theorem tensorRSCovariantDerivative_apply_of_mdifferentiableAt (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (τ : Π x : M, TensorRSSpace r s I x)
    (w : Π x : M, Tensor0SSpace r I x)
    (V_field : Π x : M, TangentSpace I x)
    {x : M}
    (hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (τ y)) x)
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E))
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y (w y)) x)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E
        (E := fun z : M => TangentSpace I z) y (V_field y)) x) :
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M r s cov τ x (V_field x)) (w x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M s cov
        (fun y =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from τ y) (w y))
          x (V_field x) -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from τ x)
        (Tensor0SNabla.tensor0SCovariantDerivative I M r cov w x (V_field x)) := by
  exact HomConnection.homBundleCovariantDerivative_apply_of_mdifferentiableAt
    I M (Tensor0SModel r ℝ E) (fun y : M => Tensor0SSpace r I y)
    (Tensor0SModel s ℝ E) (fun y : M => Tensor0SSpace s I y)
    (Tensor0SNabla.tensor0SCovariantDerivative I M r cov)
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov)
    τ hτ hV hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative_apply_of_mdifferentiableAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative_apply_of_mdifferentiableAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative_apply_of_mdifferentiableAt ``Submission.DifferentialGeometry.TensorRSNabla.tensorRSCovariantDerivative_apply_of_mdifferentiableAt

end TensorRSNabla

end DifferentialGeometry
end
