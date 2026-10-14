import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.First
import Mathlib.Analysis.Calculus.TangentCone.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Analysis
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]

theorem scalar_linear_reaction_bound_compact
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) (T : ℝ) (hT : 0 < T)
    (X : ℝ → (x : M) → TangentSpace I x) (u : ℝ → M → ℝ)
    (a b A : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (_root_.Set.Icc 0 T ×ˢ _root_.Set.univ))
    (htime : ∀ t ∈ _root_.Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt ℝ (fun s => u s x) (_root_.Set.Icc 0 T) t)
    (hspace : ∀ t ∈ _root_.Set.Icc 0 T, 0 < t → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hinit : ∀ x : M, u 0 x ≤ A)
    (hheat : ∀ t ∈ _root_.Set.Icc 0 T, 0 < t → ∀ x : M,
      parabolicOperatorWithDrift G T X u t x ≤ a * u t x + b) :
    ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : M, u t x ≤ Real.exp (a * t) * (A + b * t) := by
  let F : ℝ → M → ℝ := fun t x => Real.exp (-a * t) * u t x
  have hscale : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-a * t)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hFtime : ∀ t ∈ _root_.Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt ℝ (fun s => F s x) (_root_.Set.Icc 0 T) t :=
    fun t ht hp x => ((hscale.differentiable (by simp)) t).differentiableWithinAt.mul
      (htime t ht hp x)
  have hFsmooth : ∀ t ∈ _root_.Set.Icc 0 T, 0 < t → ContMDiff I 𝓘(ℝ, ℝ) ∞ (F t) :=
    fun t ht hp => contMDiff_const.mul (hspace t ht hp)
  have hFcont : ContinuousOn (fun p : ℝ × M => (A + b * p.1) - F p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    have he : Continuous (fun p : ℝ × M => Real.exp (-a * p.1)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_fst)
    exact (continuous_const.add (continuous_const.mul continuous_fst)).continuousOn.sub
      (he.continuousOn.mul hu)
  have hFbound : ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : M, F t x ≤ A + b * t := by
    apply scalar_subsolution_affine_bound G T X F A b hFcont hFtime
      (fun t ht hp x => (hFsmooth t ht hp).mdifferentiableAt (by simp))
      (fun t ht hp x => gradientFun_mdiffAt (G.metric t) (hFsmooth t ht hp) x)
    · intro x
      simpa only [F, _root_.MulZeroClass.mul_zero, Real.exp_zero, one_mul] using hinit x
    · intro t ht hp x
      have hid := parabolic_exp_rescale_identity G T a X u t ((uniqueDiffOn_Icc hT) t ht)
        (fun y => (hspace t ht hp).mdifferentiableAt (by simp)) x
        (gradientFun_mdiffAt (G.metric t) (hspace t ht hp) x) (htime t ht hp x)
        ((hscale.differentiable (by simp)) t).differentiableWithinAt
      change parabolicOperatorWithDrift G T X F t x = _ at hid
      rw [hid]
      have hsub : parabolicOperatorWithDrift G T X u t x - a * u t x ≤ b := by
        linarith [hheat t ht hp x]
      have hexp : Real.exp (-a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
      exact (mul_le_mul_of_nonneg_left hsub (Real.exp_pos _).le).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp hb)
  intro t ht x
  have h := mul_le_mul_of_nonneg_left (hFbound t ht x) (Real.exp_pos (a * t)).le
  have he : Real.exp (a * t) * F t x = u t x := by
    dsimp only [F]
    rw [← mul_assoc, ← Real.exp_add]
    simp only [neg_mul, add_neg_cancel, Real.exp_zero, one_mul]
  rwa [he] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalar_linear_reaction_bound_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalar_linear_reaction_bound_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalar_linear_reaction_bound_compact ``Submission.DifferentialGeometry.Analysis.scalar_linear_reaction_bound_compact
end DifferentialGeometry.Analysis
