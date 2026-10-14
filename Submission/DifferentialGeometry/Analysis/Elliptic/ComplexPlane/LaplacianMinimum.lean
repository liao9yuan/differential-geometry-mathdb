import Submission.DifferentialGeometry.Analysis.Elliptic.Euclidean.MaximumPrinciple
import Mathlib.Analysis.Complex.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



open _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis



theorem differential_laplacian_at_nonnegative_zero {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hn : ∀ᶠ q in 𝓝 z, 0 ≤ f q) (hz : f z = 0) :
    fderiv ℝ f z = 0 ∧ 0 ≤ Laplacian.laplacian f z := by
  have hm : IsLocalMin f z := by
    change ∀ᶠ q in 𝓝 z, f z ≤ f q
    simpa only [hz] using hn
  exact ⟨hm.fderiv_eq_zero, laplacian_nonneg_of_localMin hf hm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.differential_laplacian_at_nonnegative_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.differential_laplacian_at_nonnegative_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.differential_laplacian_at_nonnegative_zero ``Submission.DifferentialGeometry.Analysis.differential_laplacian_at_nonnegative_zero

end DifferentialGeometry.Analysis
