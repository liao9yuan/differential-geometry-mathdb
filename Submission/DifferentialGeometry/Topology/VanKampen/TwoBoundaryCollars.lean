import Submission.DifferentialGeometry.Topology.VanKampen.BoundaryCollarOrientation
import Submission.DifferentialGeometry.Topology.VanKampen.BoundaryCollarRestriction
import Submission.DifferentialGeometry.Topology.Compactness.FiniteSeparation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

theorem exists_outward_collar_of_two_components
    {B C X : Type*} [TopologicalSpace B] [CompactSpace B] [ConnectedSpace B]
    [TopologicalSpace C] [CompactSpace C] [ConnectedSpace C]
    [TopologicalSpace X] [T2Space X]
    {e : B → X} {f : C → X} (c : TwoSidedCollar e) (d : TwoSidedCollar f)
    {K : Set X} (hregular : closure (interior K) = K)
    (hfront : frontier K = Set.range e ∪ Set.range f)
    (hd : Disjoint (Set.range e) (Set.range f)) :
    ∃ h : TwoSidedCollar (Sum.elim e f),
      ∀ p : (B ⊕ C) × ℝ, h.toFun p ∈ K ↔ p.2 ≤ 0 := by
  obtain ⟨U, V, hU, hV, heU, hfV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact
      (isCompact_range c.continuous_e) (isCompact_range d.continuous_e) hd
  obtain ⟨c', hc'U, _⟩ := c.exists_subcollar_subset_open hU heU
  obtain ⟨d', hd'V, _⟩ := d.exists_subcollar_subset_open hV hfV
  have hc'front := c'.frontier_zero_of_disjoint_rest hfront (hUV.mono hc'U hfV)
  have hd'front := d'.frontier_zero_of_disjoint_rest
    (hfront.trans (_root_.Set.union_comm _ _)) (hUV.symm.mono hd'V heU)
  obtain ⟨c'', hc'', hcside⟩ := c'.exists_outward_collar_of_frontier_zero hregular hc'front
  obtain ⟨d'', hd'', hdside⟩ := d'.exists_outward_collar_of_frontier_zero hregular hd'front
  let hdisj := hUV.mono (hc''.trans hc'U) (hd''.trans hd'V)
  refine ⟨c''.sum d'' hdisj, ?_⟩
  rintro ⟨b | b, t⟩
  · exact hcside (b, t)
  · exact hdside (b, t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_outward_collar_of_two_components then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_outward_collar_of_two_components"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_outward_collar_of_two_components ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_outward_collar_of_two_components

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
