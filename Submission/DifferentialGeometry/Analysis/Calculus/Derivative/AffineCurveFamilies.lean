import Submission.DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Families
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Function
open scoped _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {T K F : Type*} [TopologicalSpace T] [TopologicalSpace K]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem deriv_affine_curve {f g : ℝ → F} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (a t : ℝ) :
    deriv (fun x => f x + a • (g x - f x)) t =
      deriv f t + a • (deriv g t - deriv f t) := by
  exact ((hf t).hasDerivAt.add (((hg t).hasDerivAt.sub (hf t).hasDerivAt).const_smul a)).deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.deriv_affine_curve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.deriv_affine_curve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.deriv_affine_curve ``Submission.DifferentialGeometry.Analysis.deriv_affine_curve



theorem continuous_deriv_affine_family {f g : K × ℝ → F} {a : T → ℝ}
    (hf : ∀ k, Differentiable ℝ (fun t => f (k, t)))
    (hg : ∀ k, Differentiable ℝ (fun t => g (k, t))) (ha : Continuous a)
    (hdf : Continuous (fun p : K × ℝ => deriv (fun t => f (p.1, t)) p.2))
    (hdg : Continuous (fun p : K × ℝ => deriv (fun t => g (p.1, t)) p.2)) :
    Continuous (fun p : (T × K) × ℝ =>
      deriv (fun t => f (p.1.2, t) + a p.1.1 • (g (p.1.2, t) - f (p.1.2, t))) p.2) := by
  simp_rw [deriv_affine_curve (hf _) (hg _)]
  have hproj : Continuous (fun p : (T × K) × ℝ => (p.1.2, p.2)) :=
    (continuous_snd.comp continuous_fst).prodMk continuous_snd
  exact (hdf.comp hproj).add ((ha.comp (continuous_fst.comp continuous_fst)).smul
    ((hdg.comp hproj).sub (hdf.comp hproj)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuous_deriv_affine_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuous_deriv_affine_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuous_deriv_affine_family ``Submission.DifferentialGeometry.Analysis.continuous_deriv_affine_family

end DifferentialGeometry.Analysis
