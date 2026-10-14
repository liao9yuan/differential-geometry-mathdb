import Submission.DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Set

namespace DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation

variable {X : Type*} [TopologicalSpace X] {S : Set X}

theorem exists_mem_Ioo_of_continuousOn (d : TwoSidedSeparation S)
    {a b : ℝ} {gamma : ℝ → X} (hab : a ≤ b)
    (hgamma : ContinuousOn gamma (_root_.Set.Icc a b))
    (ha : gamma a ∈ d.negativeSide) (hb : gamma b ∈ d.positiveSide) :
    ∃ t ∈ _root_.Set.Ioo a b, gamma t ∈ S := by
  have hhit : ∃ t ∈ _root_.Set.Icc a b, gamma t ∈ S := by
    by_contra! havoid
    have hsub : gamma '' _root_.Set.Icc a b ⊆ Sᶜ := by
      rintro _ ⟨t, ht, rfl⟩
      exact havoid t ht
    rcases d.subset_positiveSide_or_subset_negativeSide
        (isPreconnected_Icc.image gamma hgamma) hsub with hpos | hneg
    · exact Set.disjoint_left.mp d.disjoint
        (hpos ⟨a, ⟨le_rfl, hab⟩, rfl⟩) ha
    · exact Set.disjoint_left.mp d.disjoint hb
        (hneg ⟨b, ⟨hab, le_rfl⟩, rfl⟩)
  obtain ⟨t, ht, hS⟩ := hhit
  have hta : t ≠ a := by
    intro heq
    exact d.negativeSide_subset_compl ha (heq ▸ hS)
  have htb : t ≠ b := by
    intro heq
    exact d.positiveSide_subset_compl hb (heq ▸ hS)
  exact ⟨t, ⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩, hS⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.exists_mem_Ioo_of_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.exists_mem_Ioo_of_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.exists_mem_Ioo_of_continuousOn ``Submission.DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.exists_mem_Ioo_of_continuousOn

theorem exists_mem_Ioo_of_path (d : TwoSidedSeparation S) {x y : X}
    (gamma : Path x y) (hx : x ∈ d.negativeSide) (hy : y ∈ d.positiveSide) :
    ∃ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ _root_.Set.Ioo 0 1 ∧ gamma t ∈ S := by
  obtain ⟨t, ht, hS⟩ := d.exists_mem_Ioo_of_continuousOn (gamma := gamma.extend)
    zero_le_one gamma.continuous_extend.continuousOn
    (by simpa only [gamma.extend_zero] using hx)
    (by simpa only [gamma.extend_one] using hy)
  refine ⟨⟨t, ht.1.le, ht.2.le⟩, ht, ?_⟩
  exact (gamma.extend_extends' ⟨t, ht.1.le, ht.2.le⟩) ▸ hS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.exists_mem_Ioo_of_path then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.exists_mem_Ioo_of_path"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.exists_mem_Ioo_of_path ``Submission.DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.exists_mem_Ioo_of_path

end DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation
