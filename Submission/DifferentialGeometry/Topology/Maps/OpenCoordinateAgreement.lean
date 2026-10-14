import Submission.DifferentialGeometry.Topology.Compactness.EventualLocality
import Mathlib.Topology.Sets.Opens

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {E Q α : Type*} [TopologicalSpace E] [LocallyCompactSpace E]
  [TopologicalSpace Q] {M : α → Type*} {l : Filter α}

theorem eventually_mem_of_compact_agreement_in_open_coordinates
    (U : TopologicalSpace.Opens E) (inc : U → Q)
    (hinj : Function.Injective inc) (hinc : Continuous inc)
    (V : Set Q) (hV : IsOpen V)
    (W : U → Set E) (hW : ∀ a, IsOpen (W a)) (hcenter : ∀ a : U, (a : E) ∈ W a)
    (f : U → ∀ k, E → M k) (b : ∀ k, M k) (F : ∀ k, Q → M k)
    (T : ∀ k, Set (M k))
    (hmem : ∀ a (K : Set E), IsCompact K → K ⊆ W a →
      ∀ᶠ k in l, _root_.Set.MapsTo (f a k) K (T k))
    (hagree : ∀ a (L : Set Q), IsCompact L →
      L ⊆ V ∩ (inc '' (Subtype.val ⁻¹' W a)) →
      ∀ᶠ k in l, _root_.Set.EqOn (F k)
        (Function.extend inc (fun z : U => f a k z) (fun _ => b k)) L)
    (K : Set E) (hK : IsCompact K) (hKD : K ⊆ Subtype.val '' (inc ⁻¹' V)) :
    ∀ᶠ k in l, ∀ (z : E) (hz : z ∈ U), z ∈ K → F k (inc ⟨z, hz⟩) ∈ T k := by
  classical
  have hD : IsOpen (Subtype.val '' (inc ⁻¹' V)) :=
    U.isOpen.isOpenMap_subtype_val _ (hV.preimage hinc)
  have htail : ∀ᶠ k in l, ∀ z ∈ K, ∀ hz : z ∈ U, F k (inc ⟨z, hz⟩) ∈ T k := by
    apply hK.eventually_forall_of_locally_eventually_on_compacts
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hKD hx
    refine ⟨(Subtype.val '' (inc ⁻¹' V)) ∩ W a,
      (hD.inter (hW a)).mem_nhds ⟨⟨a, ha, rfl⟩, hcenter a⟩, ?_⟩
    intro L hLD hL
    have hLU : L ⊆ (U : Set E) := by
      intro z hz
      obtain ⟨y, _, hy⟩ := (hLD hz).1
      exact hy ▸ y.property
    have hLsub : IsCompact ((Subtype.val : U → E) ⁻¹' L) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hL (by simpa using hLU)
    have himage : inc '' ((Subtype.val : U → E) ⁻¹' L) ⊆
        V ∩ (inc '' (Subtype.val ⁻¹' W a)) := by
      rintro q ⟨z, hz, rfl⟩
      obtain ⟨y, hy, heq⟩ := (hLD hz).1
      have hyz : y = z := Subtype.ext heq
      exact ⟨hyz ▸ hy, z, (hLD hz).2, rfl⟩
    filter_upwards [hagree a _ (hLsub.image hinc) himage,
      hmem a L hL (fun z hz => (hLD hz).2)] with k hk hm z hz hzU
    rw [hk ⟨⟨z, hzU⟩, hz, rfl⟩, hinj.extend_apply]
    exact hm hz
  exact htail.mono fun k hk z hz hzK => hk z hzK hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.eventually_mem_of_compact_agreement_in_open_coordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.eventually_mem_of_compact_agreement_in_open_coordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.eventually_mem_of_compact_agreement_in_open_coordinates ``Submission.DifferentialGeometry.Topology.eventually_mem_of_compact_agreement_in_open_coordinates

end DifferentialGeometry.Topology

end

end
