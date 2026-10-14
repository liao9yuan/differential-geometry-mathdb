import Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Real.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem not_isCompact_closure_of_product_upper_tail_subset
    {A : Type*} [TopologicalSpace A] [Nonempty A] {C : Set (A × ℝ)}
    (R : ℝ) (h : _root_.Set.univ ×ˢ _root_.Set.Ioi R ⊆ C) : ¬ IsCompact (closure C) := by
  intro hc
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
    (hc.image continuous_snd).isBounded
  let a : A := Classical.arbitrary A
  let t := _root_.Max.max R r + 1
  have ht : (a, t) ∈ C := h ⟨mem_univ _, by change R < t; dsimp [t]; linarith [le_max_left R r]⟩
  have hb := hr (show t ∈ Prod.snd '' closure C from ⟨(a,t), subset_closure ht, rfl⟩)
  have habs : |t| ≤ r := by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hb
  have htr : r < t := by dsimp [t]; linarith [le_max_right R r]
  exact (not_lt_of_ge ((le_abs_self t).trans habs)) htr

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.not_isCompact_closure_of_product_upper_tail_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.not_isCompact_closure_of_product_upper_tail_subset target :: scope.openDecls } }

private theorem compact_closure_of_avoiding_product_tails
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {C D : Set (A × ℝ)} (hCD : Disjoint C D) (R : ℝ)
    (hlo : _root_.Set.univ ×ˢ _root_.Set.Iio (-R) ⊆ D) (hhi : _root_.Set.univ ×ˢ _root_.Set.Ioi R ⊆ D) :
    IsCompact (closure C) := by
  have hsub : C ⊆ _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R := by
    intro x hx
    refine ⟨mem_univ _, ?_, ?_⟩
    · by_contra h
      exact hCD.le_bot ⟨hx, hlo ⟨mem_univ _, lt_of_not_ge h⟩⟩
    · by_contra h
      exact hCD.le_bot ⟨hx, hhi ⟨mem_univ _, lt_of_not_ge h⟩⟩
  exact (isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc).of_isClosed_subset isClosed_closure
    (closure_minimal hsub (isClosed_univ.prod isClosed_Icc))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.compact_closure_of_avoiding_product_tails
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.compact_closure_of_avoiding_product_tails target :: scope.openDecls } }

theorem ComplementPair.compact_side_or_separates_product_ends
    {A : Type*} [TopologicalSpace A] [CompactSpace A] [ConnectedSpace A]
    {S : Set (A × ℝ)} (p : ComplementPair S) (hS : IsCompact S)
    (hSL : S ⊆ closure p.left) (hSR : S ⊆ closure p.right) :
    Nonempty (SphereSides S) ∨
      ∃ R : ℝ, 0 < R ∧ S ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo (-R) R ∧
        ((_root_.Set.univ ×ˢ _root_.Set.Iio (-R) ⊆ p.left ∧ _root_.Set.univ ×ˢ _root_.Set.Ioi R ⊆ p.right) ∨
         (_root_.Set.univ ×ˢ _root_.Set.Iio (-R) ⊆ p.right ∧ _root_.Set.univ ×ˢ _root_.Set.Ioi R ⊆ p.left)) := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
    (hS.image continuous_snd).isBounded
  let R := _root_.Max.max r 0 + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right r 0]
  have hsub : S ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo (-R) R := by
    intro x hx
    have hb := hr (_root_.Set.mem_image_of_mem Prod.snd hx)
    have habs : |x.2| ≤ r := by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hb
    have hrR : r < R := by dsimp [R]; linarith [le_max_left r 0]
    exact ⟨mem_univ _, by linarith [neg_abs_le x.2], by linarith [le_abs_self x.2]⟩
  have hlo : _root_.Set.univ ×ˢ _root_.Set.Iio (-R) ⊆ Sᶜ := by
    intro x hx hs
    exact (not_lt_of_ge (hsub hs).2.1.le) hx.2
  have hhi : _root_.Set.univ ×ˢ _root_.Set.Ioi R ⊆ Sᶜ := by
    intro x hx hs
    exact (not_lt_of_ge (hsub hs).2.2.le) hx.2
  rcases p.subset_left_or_subset_right
    (isPreconnected_univ.prod isPreconnected_Iio) hlo with hlo | hlo <;>
    rcases p.subset_left_or_subset_right
      (isPreconnected_univ.prod isPreconnected_Ioi) hhi with hhi | hhi
  · exact Or.inl ⟨p.swap.toSphereSides
      (compact_closure_of_avoiding_product_tails p.disjoint.symm R hlo hhi)
      (not_isCompact_closure_of_product_upper_tail_subset R hhi) hSR hSL⟩
  · exact Or.inr ⟨R, hR, hsub, Or.inl ⟨hlo,hhi⟩⟩
  · exact Or.inr ⟨R, hR, hsub, Or.inr ⟨hlo,hhi⟩⟩
  · exact Or.inl ⟨p.toSphereSides
      (compact_closure_of_avoiding_product_tails p.disjoint R hlo hhi)
      (not_isCompact_closure_of_product_upper_tail_subset R hhi) hSL hSR⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.compact_side_or_separates_product_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.compact_side_or_separates_product_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.compact_side_or_separates_product_ends ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.compact_side_or_separates_product_ends

end DifferentialGeometry.Topology.SphereSeparation
