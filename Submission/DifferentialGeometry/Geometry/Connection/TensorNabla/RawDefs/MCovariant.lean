import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.FixedChart.Models
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.FixedChart.Nabla0S
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
variable (n : WithTop ℕ∞ := ∞) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section SmoothVectorFieldRSNabla

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
theorem modelAt_mcovRS {r s : ℕ}
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s)
    (u : Set M) (x₀ : M) :
    tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s x₀ x₀
        (mcovariantDerivTensorRSWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) r s X ΓX T u x₀) =
      covariantDerivTensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
        (fun z => tangentSpaceModelContinuousLinearEquiv z
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            X (Set.range I) z))
        ΓX
        (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r s x₀ (fun x => T x))
        ((extChartAt I x₀).symm ⁻¹' u ∩ Set.range I)
        (extChartAt I x₀ x₀) := by
  unfold mcovariantDerivTensorRSWithin
  rw [tensorRSModelAt_trivializationAt_symm]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.modelAt_mcovRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.modelAt_mcovRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.modelAt_mcovRS ``Submission.DifferentialGeometry.TensorLieDeriv.modelAt_mcovRS

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
omit [CompleteSpace 𝕜] in
theorem mcovariantDeriv_tensor0SWithin_apply_slots {s : ℕ}
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (u : Set M) (x₀ : M) (slots : Fin s → E) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀
        (mcovariantDerivTensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) s X ΓX α u x₀))
        slots =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) s x₀ (fun x => α x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ _root_.Set.range I)
          (extChartAt I x₀ x₀)
          (tangentSpaceModelContinuousLinearEquiv (extChartAt I x₀ x₀)
            (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
              X (_root_.Set.range I) (extChartAt I x₀ x₀)))
          slots -
        ∑ a : Fin s,
          (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s x₀ x₀ (α x₀))
            (Function.update slots a (ΓX (extChartAt I x₀ x₀) (slots a))) := by
  unfold mcovariantDerivTensor0SWithin
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [covariantDeriv_tensor0SModelWithin_apply_slots]
  simp only [tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.mcovariantDeriv_tensor0SWithin_apply_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.mcovariantDeriv_tensor0SWithin_apply_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.mcovariantDeriv_tensor0SWithin_apply_slots ``Submission.DifferentialGeometry.TensorLieDeriv.mcovariantDeriv_tensor0SWithin_apply_slots

section ExtractedConnection

variable [IsManifold I 2 M]

end ExtractedConnection

end SmoothVectorFieldRSNabla

end

end TensorLieDeriv
end DifferentialGeometry
