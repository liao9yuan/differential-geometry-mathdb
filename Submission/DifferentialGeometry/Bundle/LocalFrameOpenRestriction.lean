import Submission.DifferentialGeometry.Bundle.LocalFramePullback
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Geometry.Manifold.VectorField.Pullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.IsLocalFrameOn in
theorem IsLocalFrameOn.restrict_open
    {ι : Type*} {frame : ι → (x : M) → TangentSpace I x} {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (U : TopologicalSpace.Opens M) :
    IsLocalFrameOn (V := (TangentSpace I : U → Type _)) I E (∞ : WithTop ℕ∞)
      (fun i (x : U) => frame i (x : M)) (Subtype.val ⁻¹' u) where
  linearIndependent hx := hframe.linearIndependent hx
  generating hx := hframe.generating hx
  contMDiffOn i := by
    have h := (hframe.contMDiffOn i).mpullback_vectorField_preimage
      (contMDiff_subtype_val (I := I) (U := U) (n := ∞))
      (by intro x _; rw [DifferentialGeometry.mfderiv_subtype_val]
          exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩) (by simp)
    have heq (x : U) : VectorField.mpullback I I (Subtype.val : U → M) (frame i) x =
        frame i (x : M) := by
      simp only [VectorField.mpullback, DifferentialGeometry.mfderiv_subtype_val]
      change (ContinuousLinearMap.id ℝ E).inverse _ = _
      rw [ContinuousLinearMap.inverse_id]
      rfl
    simpa only [heq] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsLocalFrameOn.restrict_open then
    throwError "Refusing to shadow existing declaration IsLocalFrameOn.restrict_open"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalFrameOn.restrict_open ``Submission.IsLocalFrameOn.restrict_open
