import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Geometry.Manifold.ChartedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
namespace DifferentialGeometry.Topology.Covering

theorem t2Space_of_isCoveringMap {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [T2Space B] {p : E → B} (hp : IsCoveringMap p) : T2Space E := by
  constructor
  intro x y hxy
  by_cases hbase : p x = p y
  · exact hp.isSeparatedMap x y hbase hxy
  · obtain ⟨U, V, hU, hV, hx, hy, hd⟩ := t2_separation hbase
    exact ⟨p ⁻¹' U, p ⁻¹' V, hU.preimage hp.continuous, hV.preimage hp.continuous,
      hx, hy, hd.preimage p⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Covering.t2Space_of_isCoveringMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Covering.t2Space_of_isCoveringMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Covering.t2Space_of_isCoveringMap ``Submission.DifferentialGeometry.Topology.Covering.t2Space_of_isCoveringMap

theorem secondCountableTopology_totalSpace {J B F : Type*} [TopologicalSpace B]
    [TopologicalSpace F] [SecondCountableTopology B] [SecondCountableTopology F]
    (Z : FiberBundleCore J B F) : SecondCountableTopology Z.TotalSpace := by
  obtain ⟨c, hc, hcover⟩ := isLindelof_univ.elim_countable_subcover Z.baseSet Z.isOpen_baseSet
    (show (_root_.Set.univ : Set B) ⊆ ⋃ i, Z.baseSet i from
      fun b _ => mem_iUnion.mpr ⟨Z.indexAt b, Z.mem_baseSet_at b⟩)
  let : Countable c := hc.to_subtype
  let : ∀ i : c, SecondCountableTopology (Z.localTriv i.val).source :=
    fun i => (Z.localTriv i.val).toOpenPartialHomeomorph.secondCountableTopology_source
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (fun i : c => (Z.localTriv i.val).open_source)
  apply _root_.Set.eq_univ_of_forall
  intro z
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (_root_.Set.mem_univ z.1))
  obtain ⟨hic, hz⟩ := mem_iUnion.mp hi
  exact mem_iUnion.mpr ⟨⟨i, hic⟩, hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Covering.secondCountableTopology_totalSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Covering.secondCountableTopology_totalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Covering.secondCountableTopology_totalSpace ``Submission.DifferentialGeometry.Topology.Covering.secondCountableTopology_totalSpace

end DifferentialGeometry.Topology.Covering
