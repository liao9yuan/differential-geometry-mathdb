import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianSign

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem det_fderivWithin_ne_zero_of_inverse
    {S T : Set E} (hS : UniqueDiffOn ℝ S)
    (f g : E → E) (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g T)
    (hmap : _root_.Set.MapsTo f S T) (hleft : ∀ x ∈ S, g (f x) = x) {x : E} (hx : x ∈ S) :
    (fderivWithin ℝ f S x).toLinearMap.det ≠ 0 := by
  let A := fderivWithin ℝ f S x
  let B := fderivWithin ℝ g T (f x)
  have hA : HasFDerivWithinAt f A S x :=
    (hf.differentiableOn (by simp) x hx).hasFDerivWithinAt
  have hB : HasFDerivWithinAt g B T (f x) :=
    (hg.differentiableOn (by simp) (f x) (hmap hx)).hasFDerivWithinAt
  have heq : (id : E → E) =ᶠ[𝓝[S] x] g ∘ f := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hleft y hy).symm
  have hBA : B.comp A = ContinuousLinearMap.id ℝ E :=
    (hS x hx).eq ((hB.comp x hA hmap).congr_of_eventuallyEq heq (hleft x hx).symm)
      (hasFDerivAt_id x).hasFDerivWithinAt
  have hprod : B.toLinearMap.det * A.toLinearMap.det = 1 := by
    rw [← LinearMap.det_comp]
    change (B.comp A).toLinearMap.det = 1
    rw [hBA]
    simp
  intro h
  change A.toLinearMap.det = 0 at h
  rw [h, _root_.MulZeroClass.mul_zero] at hprod
  exact zero_ne_one hprod

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.det_fderivWithin_ne_zero_of_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.det_fderivWithin_ne_zero_of_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.det_fderivWithin_ne_zero_of_inverse ``Submission.DifferentialGeometry.Analysis.det_fderivWithin_ne_zero_of_inverse

theorem det_fderivWithin_pos_iff_of_inverse
    {S T : Set E} (hS : UniqueDiffOn ℝ S) (hconn : IsPreconnected S)
    (f g : E → E) (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g T)
    (hmap : _root_.Set.MapsTo f S T) (hleft : ∀ x ∈ S, g (f x) = x)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    0 < (fderivWithin ℝ f S x).toLinearMap.det ↔
      0 < (fderivWithin ℝ f S y).toLinearMap.det := by
  have hc : ContinuousOn (fun z ↦ (fderivWithin ℝ f S z).toLinearMap.det) S :=
    ContinuousLinearMap.continuous_det.comp_continuousOn (hf.continuousOn_fderivWithin hS (by simp))
  have hprop (a b : E) (ha : a ∈ S) (hb : b ∈ S)
      (hp : 0 < (fderivWithin ℝ f S a).toLinearMap.det) :
      0 < (fderivWithin ℝ f S b).toLinearMap.det := by
    by_contra hn
    obtain ⟨z, hz, hzero⟩ := hconn.intermediate_value hb ha hc
      (show (0 : ℝ) ∈ _root_.Set.Icc (fderivWithin ℝ f S b).toLinearMap.det
        (fderivWithin ℝ f S a).toLinearMap.det from ⟨le_of_not_gt hn, hp.le⟩)
    exact det_fderivWithin_ne_zero_of_inverse hS f g hf hg hmap hleft hz hzero
  exact ⟨hprop x y hx hy, hprop y x hy hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.det_fderivWithin_pos_iff_of_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.det_fderivWithin_pos_iff_of_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.det_fderivWithin_pos_iff_of_inverse ``Submission.DifferentialGeometry.Analysis.det_fderivWithin_pos_iff_of_inverse

end DifferentialGeometry.Analysis
