import Submission.DifferentialGeometry.Topology.Flow.ForwardInvariant
import Mathlib.Topology.Order.DenselyOrdered

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.Flow

theorem isForwardInvariant_of_returnArc_and_side
    {X : Type*} [TopologicalSpace X] (φ : _root_.Flow ℝ X)
    {σ : ℝ → X} (hσ : Continuous σ) {U : Set X} {a b T ε : ℝ}
    (hab : a ≠ b) (hε : 0 < ε) (hreturn : φ T (σ a) = σ b)
    (hfrontier : frontier U = (fun t ↦ φ t (σ a)) '' _root_.Set.Icc 0 T ∪ σ '' _root_.Set.uIcc a b)
    (hside : ∀ u ∈ _root_.Set.uIoo a b, ∀ t ∈ _root_.Set.Ioo 0 ε, φ t (σ u) ∈ U) :
    IsForwardInvariant φ (closure U) := by
  have hmaps : _root_.Set.MapsTo (fun p : ℝ × ℝ ↦ φ p.2 (σ p.1))
      (_root_.Set.uIoo a b ×ˢ _root_.Set.Ioo 0 ε) U := fun p hp ↦ hside p.1 hp.1 p.2 hp.2
  have hclosed := hmaps.closure (φ.continuous continuous_snd (hσ.comp continuous_fst))
  rw [closure_prod_eq, closure_uIoo hab, closure_Ioo hε.ne] at hclosed
  have hchord (u : ℝ) (hu : u ∈ _root_.Set.uIcc a b) :
      ∀ t ∈ _root_.Set.Icc 0 ε, φ t (σ u) ∈ closure U :=
    fun t ht ↦ hclosed (show (u, t) ∈ _root_.Set.uIcc a b ×ˢ _root_.Set.Icc 0 ε from ⟨hu, ht⟩)
  apply isForwardInvariant_of_frontier φ isClosed_closure
  intro x hx
  have hxfr := frontier_closure_subset hx
  rw [hfrontier] at hxfr
  rcases hxfr with ⟨s, hs, rfl⟩ | ⟨u, hu, rfl⟩
  · rcases lt_or_eq_of_le hs.2 with hsT | rfl
    · refine ⟨T - s, sub_pos.mpr hsT, fun t ht ↦ ?_⟩
      rw [← φ.map_add]
      apply frontier_subset_closure
      rw [hfrontier]
      exact Or.inl ⟨t + s, ⟨by linarith [ht.1, hs.1], by linarith [ht.2]⟩, rfl⟩
    · refine ⟨ε, hε, fun t ht ↦ ?_⟩
      simpa only [hreturn] using hchord b _root_.Set.right_mem_uIcc t ht
  · exact ⟨ε, hε, hchord u hu⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Flow.isForwardInvariant_of_returnArc_and_side then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Flow.isForwardInvariant_of_returnArc_and_side"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Flow.isForwardInvariant_of_returnArc_and_side ``Submission.DifferentialGeometry.Topology.Flow.isForwardInvariant_of_returnArc_and_side

end DifferentialGeometry.Topology.Flow
