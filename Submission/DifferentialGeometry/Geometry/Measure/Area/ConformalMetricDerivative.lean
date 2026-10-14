import Submission.DifferentialGeometry.Geometry.Measure.Area.Riemannian
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]






theorem hasDerivAt_tangentTwoJacobian_at_conformal
    {G : ℝ → SmoothRiemannianMetric I M} {t : ℝ} {x : M} {v w : TangentSpace I x}
    {A B C : ℝ}
    (hA : HasDerivAt (fun r => (G r).inner x v v) A t)
    (hB : HasDerivAt (fun r => (G r).inner x w w) B t)
    (hC : HasDerivAt (fun r => (G r).inner x v w) C t)
    (horth : (G t).inner x v w = 0)
    (heq : (G t).inner x v v = (G t).inner x w w) :
    HasDerivAt (fun r => tangentTwoJacobian (G r) v w) ((A + B) / 2) t := by
  by_cases hv : v = 0
  · subst v
    have hw : w = 0 := by
      by_contra hw
      have hp := (G t).pos x w hw
      have hz : (G t).inner x w w = 0 := by simpa using heq.symm
      linarith
    subst w
    have hAz : A = 0 := by
      have h := hA.deriv
      simpa using h.symm
    have hBz : B = 0 := by
      have h := hB.deriv
      simpa using h.symm
    simp only [hAz, hBz, add_zero, zero_div]
    have he : (fun r => tangentTwoJacobian (G r) (0 : TangentSpace I x) 0) =
        (fun _ : ℝ => (0 : ℝ)) := by
      funext r
      simp [tangentTwoJacobian]
    rw [he]
    exact hasDerivAt_const t (0 : ℝ)
  · have hp := (G t).pos x v hv
    have hdet : (G t).inner x v v * (G t).inner x w w - (G t).inner x v w ^ 2 ≠ 0 := by
      rw [horth, ← heq]
      nlinarith
    have h := ((hA.mul hB).sub (hC.pow 2)).sqrt hdet
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Nat.reduceSub, pow_one] at h
    have hsqrt : Real.sqrt ((G t).inner x v v * (G t).inner x w w - (G t).inner x v w ^ 2) =
        (G t).inner x v v := tangentTwoJacobian_of_conformal (G t) horth heq
    change HasDerivAt (fun r => tangentTwoJacobian (G r) v w)
      ((A * (G t).inner x w w + (G t).inner x v v * B -
        2 * (G t).inner x v w * C) /
        (2 * Real.sqrt ((G t).inner x v v * (G t).inner x w w - (G t).inner x v w ^ 2))) t at h
    have he : (A * (G t).inner x w w + (G t).inner x v v * B -
        2 * (G t).inner x v w * C) /
        (2 * Real.sqrt ((G t).inner x v v * (G t).inner x w w - (G t).inner x v w ^ 2)) =
        (A + B) / 2 := by
      rw [hsqrt, horth, ← heq]
      field_simp
      ring
    rw [he] at h
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasDerivAt_tangentTwoJacobian_at_conformal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasDerivAt_tangentTwoJacobian_at_conformal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasDerivAt_tangentTwoJacobian_at_conformal ``Submission.DifferentialGeometry.Geometry.hasDerivAt_tangentTwoJacobian_at_conformal

end DifferentialGeometry.Geometry

end

section

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]






theorem hasDerivWithinAt_tangentTwoJacobian_at_conformal
    {G : ℝ → SmoothRiemannianMetric I M} {t : ℝ} {x : M} {v w : TangentSpace I x}
    {A B C : ℝ} {s : Set ℝ} (hs : UniqueDiffWithinAt ℝ s t)
    (hA : HasDerivWithinAt (fun r => (G r).inner x v v) A s t)
    (hB : HasDerivWithinAt (fun r => (G r).inner x w w) B s t)
    (hC : HasDerivWithinAt (fun r => (G r).inner x v w) C s t)
    (horth : (G t).inner x v w = 0)
    (heq : (G t).inner x v v = (G t).inner x w w) :
    HasDerivWithinAt (fun r => tangentTwoJacobian (G r) v w) ((A + B) / 2) s t := by
  by_cases hv : v = 0
  · subst v
    have hw : w = 0 := by
      by_contra hw
      have hp := (G t).pos x w hw
      have hz : (G t).inner x w w = 0 := by simpa using heq.symm
      linarith
    subst w
    have hAz : A = 0 := by
      have h := hA.derivWithin hs
      simpa using h.symm
    have hBz : B = 0 := by
      have h := hB.derivWithin hs
      simpa using h.symm
    simp only [hAz, hBz, add_zero, zero_div]
    have he : (fun r => tangentTwoJacobian (G r) (0 : TangentSpace I x) 0) =
        (fun _ : ℝ => (0 : ℝ)) := by
      funext r
      simp [tangentTwoJacobian]
    rw [he]
    exact hasDerivWithinAt_const t s (0 : ℝ)
  · have hp := (G t).pos x v hv
    have hdet : (G t).inner x v v * (G t).inner x w w - (G t).inner x v w ^ 2 ≠ 0 := by
      rw [horth, ← heq]
      nlinarith
    have h := ((hA.mul hB).sub (hC.pow 2)).sqrt hdet
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Nat.reduceSub, pow_one] at h
    have hsqrt : Real.sqrt ((G t).inner x v v * (G t).inner x w w - (G t).inner x v w ^ 2) =
        (G t).inner x v v := tangentTwoJacobian_of_conformal (G t) horth heq
    change HasDerivWithinAt (fun r => tangentTwoJacobian (G r) v w)
      ((A * (G t).inner x w w + (G t).inner x v v * B -
        2 * (G t).inner x v w * C) /
        (2 * Real.sqrt ((G t).inner x v v * (G t).inner x w w - (G t).inner x v w ^ 2))) s t at h
    have he : (A * (G t).inner x w w + (G t).inner x v v * B -
        2 * (G t).inner x v w * C) /
        (2 * Real.sqrt ((G t).inner x v v * (G t).inner x w w - (G t).inner x v w ^ 2)) =
        (A + B) / 2 := by
      rw [hsqrt, horth, ← heq]
      field_simp
      ring
    rw [he] at h
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasDerivWithinAt_tangentTwoJacobian_at_conformal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasDerivWithinAt_tangentTwoJacobian_at_conformal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasDerivWithinAt_tangentTwoJacobian_at_conformal ``Submission.DifferentialGeometry.Geometry.hasDerivWithinAt_tangentTwoJacobian_at_conformal

end DifferentialGeometry.Geometry

end

end
