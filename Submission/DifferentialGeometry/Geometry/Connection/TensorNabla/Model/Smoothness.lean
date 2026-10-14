import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Model.TensorRS
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry
namespace TensorLieDeriv

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.VectorField _root_.Filter
    DifferentialGeometry.Tensor0SBundle Function
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section ModelCovariantDerivative

theorem contDiffWithinAt_covariantDeriv_tensor0SModelWithin (s : ℕ)
    {m n' : WithTop ℕ∞} {X : E → E} {ΓX : E → E →L[𝕜] E}
    {α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s}
    {u : Set E} {x : E}
    (hα : ContDiffWithinAt 𝕜 n' α u x)
    (hX : ContDiffWithinAt 𝕜 m X u x)
    (hΓ : ContDiffWithinAt 𝕜 m ΓX u x)
    (hu : UniqueDiffOn 𝕜 u) (hmn : m + 1 ≤ n') (hx : x ∈ u) :
    ContDiffWithinAt 𝕜 m
      (fun y => covariantDerivTensor0SModelWithin (𝕜 := 𝕜) (E := E)
        s X ΓX α u y) u x := by
  have hprincipal :
      ContDiffWithinAt 𝕜 m
        (fun y => fderivWithin 𝕜 α u y (X y)) u x :=
    hα.fderivWithin_right_apply hX hu hmn hx
  have hα_m : ContDiffWithinAt 𝕜 m α u x :=
    hα.of_le (le_trans le_self_add hmn)
  have hCorrectionOp :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s (ΓX y)) u x := by
    let h := hΓ.continuousLinearMap_comp
      (lieDerivCorrectionOpL (𝕜 := 𝕜) (E := E) s)
    exact h.congr_of_eventuallyEq
      (Eventually.of_forall fun y ↦
        (lieDeriv_correctionOpL_apply (𝕜 := 𝕜) (E := E) (s := s) (ΓX y)).symm)
      (lieDeriv_correctionOpL_apply (𝕜 := 𝕜) (E := E) (s := s) (ΓX x)).symm
  have hCorrection :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDerivCorrection (𝕜 := 𝕜) (E := E) s (ΓX y) (α y)) u x := by
    simpa [lieDerivCorrectionL] using hCorrectionOp.clm_apply hα_m
  simpa [covariantDerivTensor0SModelWithin, covariantDerivTensor0SModelAt] using
    hprincipal.sub hCorrection

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_covariantDeriv_tensor0SModelWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_covariantDeriv_tensor0SModelWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_covariantDeriv_tensor0SModelWithin ``Submission.DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_covariantDeriv_tensor0SModelWithin

theorem contDiffWithinAt_covariantDeriv_tensorRSModelWithin (r s : ℕ)
    {m n' : WithTop ℕ∞} {X : E → E} {ΓX : E → E →L[𝕜] E}
    {T : E → TensorRSModel r s 𝕜 E}
    {u : Set E} {x : E}
    (hT : ContDiffWithinAt 𝕜 n' T u x)
    (hX : ContDiffWithinAt 𝕜 m X u x)
    (hΓ : ContDiffWithinAt 𝕜 m ΓX u x)
    (hu : UniqueDiffOn 𝕜 u) (hmn : m + 1 ≤ n') (hx : x ∈ u) :
    ContDiffWithinAt 𝕜 m
      (fun y => covariantDerivTensorRSModelWithin (𝕜 := 𝕜) (E := E)
        r s X ΓX T u y) u x := by
  have hprincipal :
      ContDiffWithinAt 𝕜 m
        (fun y => fderivWithin 𝕜 T u y (X y)) u x :=
    hT.fderivWithin_right_apply hX hu hmn hx
  have hT_m : ContDiffWithinAt 𝕜 m T u x :=
    hT.of_le (le_trans le_self_add hmn)
  have hCorrectionS :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s (ΓX y)) u x := by
    let h := hΓ.continuousLinearMap_comp
      (lieDerivCorrectionOpL (𝕜 := 𝕜) (E := E) s)
    exact h.congr_of_eventuallyEq
      (Eventually.of_forall fun y ↦
        (lieDeriv_correctionOpL_apply (𝕜 := 𝕜) (E := E) (s := s) (ΓX y)).symm)
      (lieDeriv_correctionOpL_apply (𝕜 := 𝕜) (E := E) (s := s) (ΓX x)).symm
  have hCorrectionR :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r (ΓX y)) u x := by
    let h := hΓ.continuousLinearMap_comp
      (lieDerivCorrectionOpL (𝕜 := 𝕜) (E := E) r)
    exact h.congr_of_eventuallyEq
      (Eventually.of_forall fun y ↦
        (lieDeriv_correctionOpL_apply (𝕜 := 𝕜) (E := E) (s := r) (ΓX y)).symm)
      (lieDeriv_correctionOpL_apply (𝕜 := 𝕜) (E := E) (s := r) (ΓX x)).symm
  have hOut :
      ContDiffWithinAt 𝕜 m
        (fun y => (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s (ΓX y)).comp (T y)) u x :=
    hCorrectionS.clm_comp hT_m
  have hIn :
      ContDiffWithinAt 𝕜 m
        (fun y => (T y).comp (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r (ΓX y))) u x :=
    hT_m.clm_comp hCorrectionR
  simpa [covariantDerivTensorRSModelWithin, covariantDerivTensorRSModelAt] using
    (hprincipal.sub hOut).add hIn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_covariantDeriv_tensorRSModelWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_covariantDeriv_tensorRSModelWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_covariantDeriv_tensorRSModelWithin ``Submission.DifferentialGeometry.TensorLieDeriv.contDiffWithinAt_covariantDeriv_tensorRSModelWithin

end ModelCovariantDerivative

end

end TensorLieDeriv
end DifferentialGeometry
