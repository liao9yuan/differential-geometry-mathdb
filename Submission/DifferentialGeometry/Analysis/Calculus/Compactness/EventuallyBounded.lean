import Submission.DifferentialGeometry.Analysis.Calculus.Compactness.BilinearForm
import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.DerivativeBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Filter _root_.Topology

section MapArzelaAscoli

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_cInf_subseq_on_of_eventually_bdd
    {U : Set E} (hU : IsOpen U) (Φ : ℕ → E → F)
    (hΦ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Φ k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ M : ℝ, ∀ᶠ k in _root_.Filter.atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) Φinf U ∧
        MapCInfConvergenceOnCompacts U (fun k => Φ (φ k)) Φinf :=
  exists_cInf_subseq_on hU Φ hΦ (exists_iteratedFDeriv_bound_of_eventually_bounded hU hΦ hbdd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_cInf_subseq_on_of_eventually_bdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_cInf_subseq_on_of_eventually_bdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_cInf_subseq_on_of_eventually_bdd ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_cInf_subseq_on_of_eventually_bdd

end MapArzelaAscoli

section BilinearFormArzelaAscoli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_smooth_bilinear_form_limit_subsequence_on_of_eventually_bdd
    {U : Set E} (hU : IsOpen U)
    (g : ℕ → E → (E →L[ℝ] E →L[ℝ] ℝ))
    (hg : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (g k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ᶠ k in _root_.Filter.atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (g k) x‖ ≤ C)
    (a b : ℝ)
    (hab : ∀ k : ℕ, ∀ z ∈ U, ∀ v : E,
      a * ‖v‖ ^ 2 ≤ g k z v v ∧ g k z v v ≤ b * ‖v‖ ^ 2) :
    ∃ (φ : ℕ → ℕ) (gInf : E → (E →L[ℝ] E →L[ℝ] ℝ)),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) gInf U ∧
        MapCInfConvergenceOnCompacts U (fun k => g (φ k)) gInf ∧
        ∀ z ∈ U, ∀ v : E,
          a * ‖v‖ ^ 2 ≤ gInf z v v ∧ gInf z v v ≤ b * ‖v‖ ^ 2 :=
  exists_smooth_bilinear_form_limit_subsequence_on hU g hg
    (exists_iteratedFDeriv_bound_of_eventually_bounded hU hg hbdd) a b hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_smooth_bilinear_form_limit_subsequence_on_of_eventually_bdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_smooth_bilinear_form_limit_subsequence_on_of_eventually_bdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_smooth_bilinear_form_limit_subsequence_on_of_eventually_bdd ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_smooth_bilinear_form_limit_subsequence_on_of_eventually_bdd

end BilinearFormArzelaAscoli

end CheegerGromovCompactness
end DifferentialGeometry
