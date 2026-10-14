import Submission.DifferentialGeometry.Analysis.ODE.Flow.Planar.CompactFlowGerm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Filter _root_.Topology
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Analysis

theorem exists_compact_isotopy_realizing_complex_mul
    (a : ℂ) (ha : a ≠ 0) (r : ℝ) (hr : 0 < r) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞ ∧
      (D 1 : ℂ → ℂ) =ᶠ[𝓝 0] (fun z ↦ a * z) ∧
      ∀ p z, z ∉ _root_.Metric.closedBall 0 (2 * r) → D p z = z ∧ (D p).symm z = z := by
  let v : ℂ → ℂ := fun z ↦ Complex.log a * z
  let Γ : ℂ × ℝ → ℂ := fun q ↦ Complex.exp ((q.2 : ℂ) * Complex.log a) * q.1
  have hv : ContDiff ℝ ∞ v := contDiff_const.mul contDiff_id
  have hΓ : Continuous Γ := by fun_prop
  have hzero (z : ℂ) : Γ (z, 0) = z := by simp [Γ]
  have hfixed (t : ℝ) (_ : t ∈ _root_.Set.Icc (0 : ℝ) 1) : Γ (0, t) = 0 := by simp [Γ]
  have hderiv (z : ℂ) (t : ℝ) (_ : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
      HasDerivAt (fun s ↦ Γ (z, s)) (v (Γ (z, t))) t := by
    have hd := ((((hasDerivAt_id (t : ℂ)).mul_const (Complex.log a)).cexp).mul_const z).comp_ofReal
    convert hd using 1 <;> first | rfl | dsimp [Γ, v]; ring
  obtain ⟨D, hD, hDi, hD0, hgerm, hfix⟩ :=
    exists_compact_isotopy_realizing_flow_germ hv Γ hΓ hzero hfixed hderiv r hr
  refine ⟨D, hD, hDi, hD0, ?_, hfix⟩
  simpa only [Γ, Complex.ofReal_one, one_mul, Complex.exp_log ha] using hgerm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_compact_isotopy_realizing_complex_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_compact_isotopy_realizing_complex_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_compact_isotopy_realizing_complex_mul ``Submission.DifferentialGeometry.Analysis.exists_compact_isotopy_realizing_complex_mul

end DifferentialGeometry.Analysis
