import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Smooth
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Tangent
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Endomorphism
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Submission.Bundle.Submission.Trivialization.continuousMultilinearMap then
    throwError "Refusing to shadow existing declaration Submission.Bundle.Submission.Trivialization.continuousMultilinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `Submission.Bundle.Submission.Trivialization.continuousMultilinearMap ``Submission.Bundle.Trivialization.continuousMultilinearMap

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

section SmoothVectorFieldRSNabla

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

omit [CompleteSpace 𝕜] in
theorem tensor0SModelAt_apply (s : ℕ) (x₀ x : M)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → E) :
    tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x A slots =
      A (fun a : Fin s =>
        (_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀).symmL 𝕜 x (slots a)) := by
  unfold tensor0SModelAt
  let e₀ := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀
  change (((e₀.continuousMultilinearMap 𝕜 s) ⟨x, A⟩).2) slots =
    A (fun a : Fin s => e₀.symmL 𝕜 x (slots a))
  rw [Bundle.Trivialization.continuousMultilinearMap_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.tensor0SModelAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.tensor0SModelAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.tensor0SModelAt_apply ``Submission.DifferentialGeometry.TensorLieDeriv.tensor0SModelAt_apply

omit [CompleteSpace 𝕜] in
theorem tensor0SModelInChart_center_eq_tensor0SModelAt (s : ℕ) (x₀ : M)
    (A : (x : M) →
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ A (extChartAt I x₀ x₀) =
      tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀ (A x₀) := by
  unfold tensor0SModelInChart
  rw [extChartAt_to_inv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.tensor0SModelInChart_center_eq_tensor0SModelAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.tensor0SModelInChart_center_eq_tensor0SModelAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.tensor0SModelInChart_center_eq_tensor0SModelAt ``Submission.DifferentialGeometry.TensorLieDeriv.tensor0SModelInChart_center_eq_tensor0SModelAt

omit [CompleteSpace 𝕜] in
theorem tensor0SModelInChart_apply (s : ℕ) (x₀ : M)
    (A : (x : M) →
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (y : E) (slots : Fin s → E) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) s x₀ A y slots =
      A ((extChartAt I x₀).symm y)
        (fun a : Fin s =>
          (_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀).symmL 𝕜
            ((extChartAt I x₀).symm y) (slots a)) := by
  unfold tensor0SModelInChart
  rw [tensor0SModelAt_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.tensor0SModelInChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.tensor0SModelInChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.tensor0SModelInChart_apply ``Submission.DifferentialGeometry.TensorLieDeriv.tensor0SModelInChart_apply

noncomputable def tensorRSModelAt (r s : ℕ) (x₀ x : M)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x) :
    TensorRSModel r s 𝕜 E := by
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  exact ((_root_.FiberBundle.trivializationAt (TensorRSModel r s 𝕜 E)
    (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.tensorRSModelAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.tensorRSModelAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.tensorRSModelAt ``Submission.DifferentialGeometry.TensorLieDeriv.tensorRSModelAt

omit [CompleteSpace 𝕜] in
theorem tensorRSModelAt_trivializationAt_symm (r s : ℕ) (x₀ : M)
    (T : TensorRSModel r s 𝕜 E) :
    letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s x₀ x₀
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀).symm x₀ T) = T := by
  let := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  unfold tensorRSModelAt
  exact congrArg Prod.snd
    ((_root_.FiberBundle.trivializationAt (TensorRSModel r s 𝕜 E)
      (fun x => TensorRSSpace r s I x) x₀).apply_mk_symm
        (_root_.FiberBundle.mem_baseSet_trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀)
        T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.tensorRSModelAt_trivializationAt_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.tensorRSModelAt_trivializationAt_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.tensorRSModelAt_trivializationAt_symm ``Submission.DifferentialGeometry.TensorLieDeriv.tensorRSModelAt_trivializationAt_symm

noncomputable def tensorRSModelInChart (r s : ℕ) (x₀ : M)
    (T : (x : M) →
      TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (y : E) : TensorRSModel r s 𝕜 E :=
  tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    r s x₀ ((extChartAt I x₀).symm y) (T ((extChartAt I x₀).symm y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.tensorRSModelInChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.tensorRSModelInChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.tensorRSModelInChart ``Submission.DifferentialGeometry.TensorLieDeriv.tensorRSModelInChart
end SmoothVectorFieldRSNabla

end

end TensorLieDeriv
end DifferentialGeometry
