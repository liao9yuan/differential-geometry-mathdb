import Submission.DifferentialGeometry.Analysis.Parabolic.Energy.ParabolicLocalAlgebra
import Mathlib.Geometry.Manifold.Algebra.LieGroup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem parabolic_div_at_zero_unit_denominator
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T t : ℝ) (b d : ℝ → M → ℝ) (x : M)
    (hbtime :
      DifferentiableWithinAt ℝ (fun s => b s x) (_root_.Set.Icc 0 T) t)
    (hdtime :
      DifferentiableWithinAt ℝ (fun s => d s x) (_root_.Set.Icc 0 T) t)
    (hbspace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (b t))
    (hdspace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (d t))
    (hbzero : b t x = 0)
    (hdone : d t x = 1)
    (hdgrad :
      gradientFun (I := I) (G.metric t) (d t) x = 0) :
    parabolicOperatorWithDrift G T (fun _ _ => 0)
        (fun s y => b s y / d s y) t x =
      parabolicOperatorWithDrift G T (fun _ _ => 0) b t x := by
  have hdne : d t x ≠ 0 := by
    rw [hdone]
    norm_num
  have hnear : ∀ᶠ y in 𝓝 x, d t y ≠ 0 :=
    hdspace.continuous.continuousAt.eventually_ne hdne
  have hbin :
      ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (b t) y :=
    Eventually.of_forall fun y => hbspace.mdifferentiableAt (by simp)
  have hdin :
      ∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => (d t z)⁻¹) y :=
    hnear.mono fun y hy =>
      (hdspace.mdifferentiableAt (by simp)).inv hy
  have hditime :
      DifferentiableWithinAt ℝ (fun s => (d s x)⁻¹) (_root_.Set.Icc 0 T) t :=
    hdtime.inv hdne
  have hdiAt :
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => (d t y)⁻¹) x :=
    hdspace.contMDiffAt.inv₀ hdne
  have hdigradReg :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (T% fun y =>
          gradientFun (I := I) (G.metric t)
            (fun z => (d t z)⁻¹) y) x :=
    (gradientFun_contMDiffAt (G.metric t) hdiAt).mdifferentiableAt
      (by simp)
  have hdigrad :
      gradientFun (I := I) (G.metric t)
        (fun y => (d t y)⁻¹) x = 0 := by
    have h :=
      gradientFun_comp (I := I) (G.metric t)
        (φ := fun r : ℝ => r⁻¹) (f := d t)
        (hasDerivAt_inv hdne).differentiableAt
        (hdspace.mdifferentiableAt (by simp))
    simpa only [hdgrad, smul_zero] using h
  have hm :=
    parabolic_mul_local G T (fun _ _ => 0)
      b (fun s y => (d s y)⁻¹) t x
      hbtime hditime hbin hdin
      (gradientFun_mdiffAt (G.metric t) hbspace x)
      hdigradReg
  simpa only [div_eq_mul_inv, hbzero, hdone, inv_one,
    _root_.MulZeroClass.zero_mul, one_mul, gradientAt, hdigrad, map_zero,
    _root_.MulZeroClass.mul_zero, sub_zero, zero_add] using hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.parabolic_div_at_zero_unit_denominator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.parabolic_div_at_zero_unit_denominator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.parabolic_div_at_zero_unit_denominator ``Submission.DifferentialGeometry.Analysis.parabolic_div_at_zero_unit_denominator

end DifferentialGeometry.Analysis
