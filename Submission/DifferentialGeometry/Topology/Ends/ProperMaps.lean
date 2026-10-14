import Submission.DifferentialGeometry.Topology.Ends.FiniteEnds
import Mathlib.Topology.Maps.Proper.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set

namespace DifferentialGeometry.Geometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem not_isCompact_closure_of_range_proper_map
    [NoncompactSpace Y] {f : Y → X} (hf : IsProperMap f)
    {S : Set X} (hS : _root_.Set.range f ⊆ S) : ¬ IsCompact (closure S) := by
  intro hcompact
  have hpre : f ⁻¹' closure S = univ := by
    apply _root_.Set.eq_univ_of_forall
    intro y
    exact subset_closure (hS (_root_.Set.mem_range_self y))
  exact noncompact_univ Y (hpre ▸ hf.isCompact_preimage hcompact)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.not_isCompact_closure_of_range_proper_map
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.not_isCompact_closure_of_range_proper_map target :: scope.openDecls } }

theorem hasAtLeastEnds_of_proper_maps
    {k : ℕ} [PreconnectedSpace Y] [NoncompactSpace Y]
    (K : Set X) (hK : IsCompact K) (f : Fin k → Y → X)
    (hf : ∀ i, IsProperMap (f i)) (p : Fin k → Y)
    (havoid : ∀ i y, f i y ∉ K)
    (hdistinct : Function.Injective (fun i => connectedComponentIn Kᶜ (f i (p i)))) :
    HasAtLeastEnds X k := by
  refine ⟨K, hK, fun i => f i (p i), fun i => havoid i (p i), hdistinct, ?_⟩
  intro i
  apply not_isCompact_closure_of_range_proper_map (hf i)
  exact (isPreconnected_range (hf i).continuous).subset_connectedComponentIn
    (_root_.Set.mem_range_self (p i)) (by rintro _ ⟨y, rfl⟩; exact havoid i y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_of_proper_maps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_of_proper_maps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_of_proper_maps ``Submission.DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_of_proper_maps

theorem hasAtLeastEnds_two_of_proper_maps_into_separated_sets
    [PreconnectedSpace Y] [NoncompactSpace Y]
    {K B E : Set X} (hK : IsCompact K) (hB : IsOpen B) (hE : IsOpen E)
    (hdisjoint : Disjoint B E) (hcover : B ∪ E = Kᶜ)
    (f g : Y → X) (hf : IsProperMap f) (hg : IsProperMap g) (p q : Y)
    (hfst : _root_.Set.range f ⊆ B) (hsnd : _root_.Set.range g ⊆ E) :
    HasAtLeastEnds X 2 := by
  have hBK : B ⊆ Kᶜ := by rw [← hcover]; exact _root_.Set.subset_union_left
  have hEK : E ⊆ Kᶜ := by rw [← hcover]; exact _root_.Set.subset_union_right
  have hp : f p ∈ B := hfst (_root_.Set.mem_range_self p)
  have hq : g q ∈ E := hsnd (_root_.Set.mem_range_self q)
  have hcompE : connectedComponentIn Kᶜ (g q) ⊆ E :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union hE hB hdisjoint.symm
      (((_root_.Set.union_comm E B).trans hcover).symm ▸ connectedComponentIn_subset Kᶜ (g q))
      ⟨g q, mem_connectedComponentIn (hEK hq), hq⟩
  have hne : connectedComponentIn Kᶜ (f p) ≠ connectedComponentIn Kᶜ (g q) := by
    intro heq
    exact disjoint_left.mp hdisjoint hp
      (hcompE (heq ▸ mem_connectedComponentIn (hBK hp)))
  let a : Fin 2 → Y → X := fun i => if i = 0 then f else g
  let b : Fin 2 → Y := fun i => if i = 0 then p else q
  refine hasAtLeastEnds_of_proper_maps K hK a ?_ b ?_ ?_
  · intro i
    by_cases hi : i = 0
    · simpa only [a, hi, if_true] using hf
    · simpa only [a, hi, if_false] using hg
  · intro i y
    by_cases hi : i = 0
    · simpa only [a, hi, if_true, _root_.Set.mem_compl_iff] using hBK (hfst (_root_.Set.mem_range_self y))
    · simpa only [a, hi, if_false, _root_.Set.mem_compl_iff] using hEK (hsnd (_root_.Set.mem_range_self y))
  · intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · exact hi.trans hj.symm
      · exact (hne (by simpa only [a, b, hi, hj, if_true, if_false] using hij)).elim
    · by_cases hj : j = 0
      · exact (hne (by simpa only [a, b, hi, hj, if_true, if_false] using hij.symm)).elim
      · exact (Fin.eq_one_of_ne_zero i hi).trans (Fin.eq_one_of_ne_zero j hj).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_two_of_proper_maps_into_separated_sets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_two_of_proper_maps_into_separated_sets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_two_of_proper_maps_into_separated_sets ``Submission.DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_two_of_proper_maps_into_separated_sets

end DifferentialGeometry.Geometry.Topology
