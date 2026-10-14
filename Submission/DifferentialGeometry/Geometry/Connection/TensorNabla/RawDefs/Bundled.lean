import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.RawDefs.MCovariant
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.VectorField _root_.Filter _root_.Function
    DifferentialGeometry.TensorLieDeriv
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [CompleteSpace 𝕜]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]

omit [IsManifold I ∞ M] in
theorem nabla0SFun_apply_selfChart_slots (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (slots : Fin s → E) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x)
      (fun a : Fin s =>
        tangentConstInChart (𝕜 := 𝕜) (I := I) x (slots a) x) =
      fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s cov X α x
        (extChartAt I x x) slots := by
  unfold tangentConstInChart
  rw [← tensor0SModelAt_apply (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) s x x
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α x) slots]
  unfold nabla0SFun TensorLieDeriv.mcovariantDerivTensor0SFromConnection
    TensorLieDeriv.mcovariantDerivTensor0SWithinFromConnection
  rw [TensorLieDeriv.mcovariantDeriv_tensor0SWithin_apply_slots
    (n := (∞ : WithTop ℕ∞))]
  rw [fixedChartNabla0SModel_apply_slots
    (n := (∞ : WithTop ℕ∞))]
  simp only [Set.preimage_univ, Set.univ_inter, tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.nabla0SFun_apply_selfChart_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.nabla0SFun_apply_selfChart_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.nabla0SFun_apply_selfChart_slots ``Submission.DifferentialGeometry.Tensor0SBundle.nabla0SFun_apply_selfChart_slots

end

noncomputable section RealDerivationSmoothness

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace Real E₀]
variable [FiniteDimensional Real E₀]
variable {H₀ : Type*} [TopologicalSpace H₀]
variable {I₀ : ModelWithCorners Real E₀ H₀}
variable {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H₀ M₀]
variable [IsManifold I₀ ∞ M₀]

theorem tensor0S_eval_covariantDerivative_slot_contMDiff {s : ℕ}
    (cov : CovariantDerivative I₀ E₀ (TangentSpace I₀ : M₀ → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    (X : ContMDiffSection I₀ E₀ ∞ (TangentSpace I₀ : M₀ → Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E₀) (H := H₀) (I := I₀) (M := M₀)
      (n := ∞) s)
    (Y : Fin s → ContMDiffSection I₀ E₀ ∞ (TangentSpace I₀ : M₀ → Type _))
    (a : Fin s) :
    ContMDiff I₀ 𝓘(Real, Real) ∞
      (fun p : M₀ =>
        α p
          (Function.update (fun b : Fin s => Y b p) a
            ((cov (fun q : M₀ => Y a q) p) (X p)))) := by
  let W : (p : M₀) → TangentSpace I₀ p :=
    fun p => (cov (fun q : M₀ => Y a q) p) (X p)
  have hW :
      ContMDiff I₀ (I₀.prod 𝓘(Real, E₀)) ∞
        (fun p : M₀ => (⟨p, W p⟩ : _root_.Bundle.TotalSpace E₀ (TangentSpace I₀ : M₀ → Type _))) := by
    refine
      (CovariantDerivative.ContMDiffCovariantDerivative.contMDiff_apply
        (𝕜 := Real) (I := I₀) (M := M₀) cov hcov X (Y a)).congr ?_
    intro p
    rfl
  let V : Fin s → (p : M₀) → TangentSpace I₀ p :=
    Function.update (fun b : Fin s => fun p : M₀ => Y b p) a W
  have hV : ∀ i : Fin s,
      ContMDiff I₀ (I₀.prod 𝓘(Real, E₀)) ∞
        (fun p : M₀ => (⟨p, V i p⟩ : _root_.Bundle.TotalSpace E₀ (TangentSpace I₀ : M₀ → Type _))) := by
    intro i
    by_cases hi : i = a
    · subst hi
      simpa [V] using hW
    · simpa [V, Function.update, hi] using (Y i).contMDiff
  let Vsec : Fin s → ContMDiffSection I₀ E₀ ∞ (TangentSpace I₀ : M₀ → Type _) :=
    fun i => ⟨V i, hV i⟩
  have hev' := TensorMultilinear.contMDiff_tensor0SField_apply
    (E := E₀) (H := H₀) (I := I₀) (M := M₀) (n := s) α Vsec
  refine hev'.congr ?_
  intro p
  congr 1
  funext i
  by_cases hi : i = a
  · subst hi
    simp [Vsec, V, W]
  · simp [Vsec, V, Function.update, hi]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tensor0S_eval_covariantDerivative_slot_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tensor0S_eval_covariantDerivative_slot_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tensor0S_eval_covariantDerivative_slot_contMDiff ``Submission.DifferentialGeometry.Tensor0SBundle.tensor0S_eval_covariantDerivative_slot_contMDiff

end RealDerivationSmoothness

end Tensor0SBundle
end DifferentialGeometry
