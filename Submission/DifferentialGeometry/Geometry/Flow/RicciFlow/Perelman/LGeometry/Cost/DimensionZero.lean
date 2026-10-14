import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem lCost_eq_zero_of_finrank_eq_zero
    (hdim : Module.finrank ℝ E = 0)
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x y : M) (tau : ℝ) :
    lCost S T x y tau = 0 := by
  let : Subsingleton E := Module.finrank_zero_iff.mp hdim
  let : Subsingleton H := I.injective.subsingleton
  let : DiscreteTopology M := ChartedSpace.discreteTopology H M
  have hv (z : M) (v : TangentSpace I z) : v = 0 := by
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) z).injective
    exact Subsingleton.elim _ _
  have hscalar (t : ℝ) (z : M) : S.scalar t z = 0 := by
    apply abs_eq_zero.mp
    have h := scalar_abs_le_rm (S.base.metric t) z
    change |S.scalar t z| ≤ (Module.finrank ℝ E : ℝ) ^ 2 * _ at h
    exact le_antisymm
      (by simpa only [hdim, Nat.cast_zero, zero_pow two_ne_zero, _root_.MulZeroClass.zero_mul] using h)
      (abs_nonneg _)
  have hlen (alpha : ℝ → M) : lLength S T alpha 0 tau = 0 := by
    have hspeed (t : ℝ) : lSpeedSq S T alpha t = 0 := by
      unfold lSpeedSq
      rw [hv (alpha t) (lVelocity (I := I) alpha t)]
      simp
    have hden (t : ℝ) : lDensity S T alpha t = 0 := by
      change Real.sqrt t * (S.scalar (T - t) (alpha t) + lSpeedSq S T alpha t) = 0
      rw [hscalar, hspeed, zero_add, _root_.MulZeroClass.mul_zero]
    simp only [lLength, hden, intervalIntegral.integral_zero]
  unfold lCost
  let A : Set ℝ := {r | ∃ alpha : ℝ → M,
    ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = x ∧
      alpha (Real.sqrt tau) = y ∧
      lLength S T (squareRootReparametrization alpha) 0 tau = r}
  change _root_.InfSet.sInf A = 0
  by_cases hA : A.Nonempty
  · have hEq : A = {0} := by
      apply Set.Subset.antisymm
      · rintro r ⟨alpha, _, _, _, hr⟩
        exact Set.mem_singleton_iff.mpr (hr.symm.trans (hlen _))
      · rintro r (rfl : r = 0)
        obtain ⟨q, alpha, ha, hx, hy, hq⟩ := hA
        exact ⟨alpha, ha, hx, hy, hlen _⟩
    rw [hEq, csInf_singleton]
  · rw [Set.not_nonempty_iff_eq_empty.mp hA, Real.sInf_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_eq_zero_of_finrank_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_eq_zero_of_finrank_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_eq_zero_of_finrank_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_eq_zero_of_finrank_eq_zero

end DifferentialGeometry.PDE.RicciFlow.Perelman
