import Submission.DifferentialGeometry.Analysis.Calculus.Compactness.SmoothMap
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Filter _root_.Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def iteratedFDerivBoundsOnCompacts (Φ : ℕ → E → F) : Prop :=
  ∀ r : ℕ, ∀ K : Set E, IsCompact K →
    ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.iteratedFDerivBoundsOnCompacts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.iteratedFDerivBoundsOnCompacts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.iteratedFDerivBoundsOnCompacts ``Submission.DifferentialGeometry.CheegerGromovCompactness.iteratedFDerivBoundsOnCompacts

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem iteratedFDerivBoundsOnCompacts.comp_subseq {Φ : ℕ → E → F} (h : iteratedFDerivBoundsOnCompacts Φ)
    (φ : ℕ → ℕ) : iteratedFDerivBoundsOnCompacts (fun k => Φ (φ k)) := by
  intro r K hK
  obtain ⟨M, hM⟩ := h r K hK
  exact ⟨M, fun k x hx => hM (φ k) x hx⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.iteratedFDerivBoundsOnCompacts
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.iteratedFDerivBoundsOnCompacts.comp_subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.iteratedFDerivBoundsOnCompacts.comp_subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.iteratedFDerivBoundsOnCompacts.comp_subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.iteratedFDerivBoundsOnCompacts.comp_subseq

theorem exists_c_inf_convergent_subsequence
    (Φ : ℕ → E → F) (hΦ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ k))
    (hbdd : iteratedFDerivBoundsOnCompacts Φ) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiff ℝ (⊤ : ℕ∞) Φinf ∧
        MapCInfConvergenceOnCompacts Set.univ (fun k => Φ (φ k)) Φinf :=
  exists_cInf_subseq Φ hΦ hbdd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_c_inf_convergent_subsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_c_inf_convergent_subsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_c_inf_convergent_subsequence ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_c_inf_convergent_subsequence

omit [FiniteDimensional ℝ E] in
theorem comp_eq_id_of_mapCInfConvergenceOnCompacts
    {Φ : ℕ → F → E} {Φinf : F → E} {Ψ : ℕ → E → F} {Ψinf : E → F}
    (hΦ : MapCInfConvergenceOnCompacts Set.univ Φ Φinf) (hΦc : Continuous Φinf)
    (hΨ : MapCInfConvergenceOnCompacts Set.univ Ψ Ψinf)
    (hid : ∀ k x, Φ k (Ψ k x) = x) :
    ∀ x, Φinf (Ψinf x) = x := by
  intro x
  have hΨx : _root_.Filter.Tendsto (fun k => Ψ k x) _root_.Filter.atTop (𝓝 (Ψinf x)) :=
    tendsto_of_cInf hΨ (Set.mem_univ x)
  obtain ⟨K, hKmem, hKcomp, -⟩ := exists_mem_nhds_isCompact_isClosed (Ψinf x)
  have hΦuniform : TendstoUniformlyOn Φ Φinf _root_.Filter.atTop K :=
    tendstoUniformlyOn_of_cPConvergence (hΦ K hKcomp (Set.subset_univ K) 0)
  have hΨxK : _root_.Filter.Tendsto (fun k => Ψ k x) _root_.Filter.atTop (𝓝[K] (Ψinf x)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hΨx (hΨx.eventually_mem hKmem)
  have hcomp : _root_.Filter.Tendsto (fun k => Φ k (Ψ k x)) _root_.Filter.atTop (𝓝 (Φinf (Ψinf x))) :=
    hΦuniform.tendsto_comp hΦc.continuousWithinAt hΨxK
  simp only [hid] at hcomp
  exact (tendsto_nhds_unique tendsto_const_nhds hcomp).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.comp_eq_id_of_mapCInfConvergenceOnCompacts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.comp_eq_id_of_mapCInfConvergenceOnCompacts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.comp_eq_id_of_mapCInfConvergenceOnCompacts ``Submission.DifferentialGeometry.CheegerGromovCompactness.comp_eq_id_of_mapCInfConvergenceOnCompacts

theorem exists_smooth_inverse_limit_subsequence
    (Φ : ℕ → E → F) (Ψ : ℕ → F → E)
    (hΦ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ k)) (hΨ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Ψ k))
    (hbΦ : iteratedFDerivBoundsOnCompacts Φ) (hbΨ : iteratedFDerivBoundsOnCompacts Ψ)
    (hLeft : ∀ k x, Ψ k (Φ k x) = x) (hRight : ∀ k y, Φ k (Ψ k y) = y) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F) (Ψinf : F → E),
      StrictMono φ ∧ ContDiff ℝ (⊤ : ℕ∞) Φinf ∧ ContDiff ℝ (⊤ : ℕ∞) Ψinf ∧
        MapCInfConvergenceOnCompacts Set.univ (fun k => Φ (φ k)) Φinf ∧
        MapCInfConvergenceOnCompacts Set.univ (fun k => Ψ (φ k)) Ψinf ∧
        (∀ x, Ψinf (Φinf x) = x) ∧ (∀ y, Φinf (Ψinf y) = y) := by
  obtain ⟨φ1, Φinf, hφ1, hΦinf, hΦconv⟩ := exists_cInf_subseq Φ hΦ hbΦ
  obtain ⟨φ2, Ψinf, hφ2, hΨinf, hΨconv⟩ :=
    exists_cInf_subseq (fun k => Ψ (φ1 k)) (fun k => hΨ (φ1 k)) (hbΨ.comp_subseq φ1)
  have hΦconv' : MapCInfConvergenceOnCompacts Set.univ (fun k => Φ (φ1 (φ2 k))) Φinf :=
    hΦconv.comp_subseq hφ2
  refine ⟨φ1 ∘ φ2, Φinf, Ψinf, hφ1.comp hφ2, hΦinf, hΨinf, hΦconv', hΨconv, ?_, ?_⟩
  · exact comp_eq_id_of_mapCInfConvergenceOnCompacts hΨconv hΨinf.continuous hΦconv'
      (fun k x => hLeft (φ1 (φ2 k)) x)
  · exact comp_eq_id_of_mapCInfConvergenceOnCompacts hΦconv' hΦinf.continuous hΨconv
      (fun k y => hRight (φ1 (φ2 k)) y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_smooth_inverse_limit_subsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_smooth_inverse_limit_subsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_smooth_inverse_limit_subsequence ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_smooth_inverse_limit_subsequence

end CheegerGromovCompactness
end DifferentialGeometry
