import Mathlib.Dynamics.Flow
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.Flow

theorem exists_transverse_hit_after
    {X : Type*} [TopologicalSpace X] (φ : _root_.Flow ℝ X)
    {σ : ℝ → X} {ε : ℝ} (e : OpenPartialHomeomorph (ℝ × ℝ) X)
    (hsource : e.source = _root_.Set.Ioo (-ε) ε ×ˢ _root_.Set.Ioo (-ε) ε)
    (he : ∀ p, e p = φ p.2 (σ p.1)) {z : X}
    (hvisits : ∀ T : ℝ, ∃ t ≥ T, φ t z ∈ e.target) :
    ∀ T : ℝ, ∃ t ≥ T, ∃ u ∈ _root_.Set.Ioo (-ε) ε, φ t z = σ u := by
  intro T
  obtain ⟨t, ht, htarget⟩ := hvisits (T + ε)
  let p := e.symm (φ t z)
  have hp : p ∈ _root_.Set.Ioo (-ε) ε ×ˢ _root_.Set.Ioo (-ε) ε := by
    rw [← hsource]
    exact e.map_target htarget
  have horbit : φ p.2 (σ p.1) = φ t z := (he p).symm.trans (e.right_inv htarget)
  refine ⟨t - p.2, by linarith [hp.2.2], p.1, hp.1, ?_⟩
  calc
    φ (t - p.2) z = φ (-p.2) (φ t z) := by rw [← φ.map_add]; congr 1; ring
    _ = φ (-p.2) (φ p.2 (σ p.1)) := congrArg (φ (-p.2)) horbit.symm
    _ = σ p.1 := by rw [← φ.map_add, neg_add_cancel, φ.map_zero_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Flow.exists_transverse_hit_after then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Flow.exists_transverse_hit_after"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Flow.exists_transverse_hit_after ``Submission.DifferentialGeometry.Topology.Flow.exists_transverse_hit_after

end DifferentialGeometry.Topology.Flow
