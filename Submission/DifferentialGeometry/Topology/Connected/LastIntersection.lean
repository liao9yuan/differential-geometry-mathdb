import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Connected.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set

namespace DifferentialGeometry.Topology

theorem exists_last_intersection_segment
    {X : Type*} [TopologicalSpace X] {F : Set X} (hF : IsClosed F)
    {a b : ℝ} (hab : a < b) (γ : ℝ → X) (hγ : ContinuousOn γ (_root_.Set.Icc a b))
    (ha : γ a ∈ F) (hb : γ b ∉ F) :
    ∃ c ∈ _root_.Set.Ico a b, γ c ∈ F ∧
      (∀ t ∈ _root_.Set.Ioc c b, γ t ∉ F) ∧
      γ '' _root_.Set.Ioc c b ⊆ connectedComponentIn Fᶜ (γ b) := by
  obtain ⟨C,hC,hpre⟩ := continuousOn_iff_isClosed.mp hγ F hF
  have hcompact : IsCompact (γ ⁻¹' F ∩ _root_.Set.Icc a b) := by
    rw [hpre,_root_.Set.inter_comm]
    exact isCompact_Icc.inter_right hC
  obtain ⟨c,hc,hmax⟩ := hcompact.exists_isMaxOn
    ⟨a,ha,le_rfl,hab.le⟩ continuous_id.continuousOn
  have hcb : c < b := lt_of_le_of_ne hc.2.2 (fun h => hb (h ▸ hc.1))
  have htail : ∀ t ∈ _root_.Set.Ioc c b, γ t ∉ F := by
    intro t ht hFt
    exact (not_lt_of_ge (hmax ⟨hFt,hc.2.1.trans ht.1.le,ht.2⟩)) ht.1
  refine ⟨c,⟨hc.2.1,hcb⟩,hc.1,htail,?_⟩
  have hconnected : IsPreconnected (γ '' _root_.Set.Ioc c b) :=
    isPreconnected_Ioc.image γ (hγ.mono (fun t ht => ⟨hc.2.1.trans ht.1.le,ht.2⟩))
  exact hconnected.subset_connectedComponentIn ⟨b,⟨hcb,le_rfl⟩,rfl⟩
    (by rintro x ⟨t,ht,rfl⟩; exact htail t ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_last_intersection_segment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_last_intersection_segment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_last_intersection_segment ``Submission.DifferentialGeometry.Topology.exists_last_intersection_segment

end DifferentialGeometry.Topology
