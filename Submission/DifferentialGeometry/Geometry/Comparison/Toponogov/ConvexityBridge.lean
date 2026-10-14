import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.Convexity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

noncomputable section

namespace DifferentialGeometry.Toponogov

structure C2LowerSupportAt (f : ℝ → ℝ) (I : Set ℝ) (x : ℝ) where

  left : ℝ

  right : ℝ

  center_mem : x ∈ _root_.Set.Ioo left right

  interval_subset : _root_.Set.Ioo left right ⊆ I

  support : ℝ → ℝ

  contDiffOn_support : ContDiffOn ℝ 2 support (_root_.Set.Ioo left right)

  support_le : ∀ y ∈ _root_.Set.Ioo left right, support y ≤ f y

  support_eq : support x = f x

  secondDeriv_nonneg : 0 ≤ deriv (deriv support) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.C2LowerSupportAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.C2LowerSupportAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.C2LowerSupportAt ``Submission.DifferentialGeometry.Toponogov.C2LowerSupportAt

def C2LowerSupportAt.toLowerSupportAt {f : ℝ → ℝ} {I : Set ℝ} {x : ℝ}
    (S : C2LowerSupportAt f I x) : LowerSupportAt f I x where
  support := S.support
  supportDeriv := deriv S.support
  supportSecondDeriv := deriv (deriv S.support) x
  domain := _root_.Set.Ioo S.left S.right
  domain_mem_nhds := Ioo_mem_nhds S.center_mem.1 S.center_mem.2
  domain_subset := S.interval_subset
  support_le := S.support_le
  support_eq := S.support_eq
  hasDerivAt_support := by
    intro y hy
    exact ((S.contDiffOn_support.differentiableOn (by norm_num)) y hy).differentiableAt
      (isOpen_Ioo.mem_nhds hy) |>.hasDerivAt
  hasDerivAt_supportDeriv := by
    have hderiv : ContDiffOn ℝ 1 (deriv S.support) (_root_.Set.Ioo S.left S.right) :=
      S.contDiffOn_support.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact ((hderiv.differentiableOn (by norm_num)) x S.center_mem).differentiableAt
      (isOpen_Ioo.mem_nhds S.center_mem) |>.hasDerivAt
  supportSecondDeriv_nonneg := S.secondDeriv_nonneg

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Toponogov.C2LowerSupportAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.C2LowerSupportAt.toLowerSupportAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.C2LowerSupportAt.toLowerSupportAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.C2LowerSupportAt.toLowerSupportAt ``Submission.DifferentialGeometry.Toponogov.C2LowerSupportAt.toLowerSupportAt

theorem convexOn_of_c2LowerSupport {I : Set ℝ} {f : ℝ → ℝ}
    (hI : Convex ℝ I) (hf : ContinuousOn f I)
    (hsupport : ∀ x ∈ interior I, C2LowerSupportAt f I x) :
    ConvexOn ℝ I f := by
  exact convexOn_of_lowerSupport hI hf fun x hx ↦ (hsupport x hx).toLowerSupportAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.convexOn_of_c2LowerSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.convexOn_of_c2LowerSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.convexOn_of_c2LowerSupport ``Submission.DifferentialGeometry.Toponogov.convexOn_of_c2LowerSupport

end DifferentialGeometry.Toponogov
