import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold
open scoped _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem mfderiv_comp_add_apply_one {γ : ℝ → M} (s d : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (s + d)) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun t ↦ γ (t + d)) s (1 : ℝ) : E) =
      mfderiv 𝓘(ℝ, ℝ) I γ (s + d) (1 : ℝ) := by
  have hadd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ ↦ t + d) s
      (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) s)) :=
    ((hasFDerivAt_id s).add_const d).hasMFDerivAt
  exact congrArg (fun A : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace I (γ (s + d)) ↦ A (1 : ℝ))
    (hγ.hasMFDerivAt.comp s hadd).mfderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mfderiv_comp_add_apply_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mfderiv_comp_add_apply_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mfderiv_comp_add_apply_one ``Submission.DifferentialGeometry.Geometry.mfderiv_comp_add_apply_one

theorem mfderiv_comp_affine_apply_one {γ : ℝ → M} (s c d : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (c * s + d)) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun t ↦ γ (c * t + d)) s (1 : ℝ) : E) =
      c • (mfderiv 𝓘(ℝ, ℝ) I γ (c * s + d) (1 : ℝ) : E) := by
  have ha : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ ↦ c * t + d) s
      (c • ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) s)) :=
    (((hasFDerivAt_id s).const_smul c).add_const d).hasMFDerivAt
  have hh := congrArg
    (fun A : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace I (γ (c * s + d)) ↦ A (1 : ℝ))
    (hγ.hasMFDerivAt.comp s ha).mfderiv
  exact hh.trans ((mfderiv 𝓘(ℝ, ℝ) I γ (c * s + d)).map_smul c (1 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mfderiv_comp_affine_apply_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mfderiv_comp_affine_apply_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mfderiv_comp_affine_apply_one ``Submission.DifferentialGeometry.Geometry.mfderiv_comp_affine_apply_one

end DifferentialGeometry.Geometry
