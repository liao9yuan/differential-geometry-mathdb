import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Maps.Proper.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission







noncomputable section

open _root_.Set _root_.Function
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {Y : Type*}


def openCollapse (U : Set Y) (y : Y) : OnePoint U :=
  by
    classical
    exact if h : y ∈ U then (⟨y, h⟩ : U) else OnePoint.infty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.openCollapse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.openCollapse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.openCollapse ``Submission.DifferentialGeometry.Topology.openCollapse

theorem openCollapse_of_mem (U : Set Y) (y : U) : openCollapse U y = (y : OnePoint U) := by
  simp only [openCollapse, dif_pos y.property]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.openCollapse_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.openCollapse_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.openCollapse_of_mem ``Submission.DifferentialGeometry.Topology.openCollapse_of_mem

theorem openCollapse_of_notMem (U : Set Y) {y : Y} (hy : y ∉ U) :
    openCollapse U y = OnePoint.infty := by
  simp only [openCollapse, dif_neg hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.openCollapse_of_notMem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.openCollapse_of_notMem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.openCollapse_of_notMem ``Submission.DifferentialGeometry.Topology.openCollapse_of_notMem



theorem continuous_openCollapse [TopologicalSpace Y] [T2Space Y] (U : Set Y) (hU : IsOpen U) :
    Continuous (openCollapse U) := by
  classical
  rw [continuous_def]
  intro V hV
  by_cases hinf : OnePoint.infty ∈ V
  · have hc : IsCompact ((fun u : U => (u : OnePoint U)) ⁻¹' V)ᶜ :=
      ((OnePoint.isOpen_iff_of_mem' hinf).mp hV).1
    have heq : (openCollapse U ⁻¹' V)ᶜ =
        Subtype.val '' ((fun u : U => (u : OnePoint U)) ⁻¹' V)ᶜ := by
      ext y
      by_cases hy : y ∈ U
      · simp only [_root_.Set.mem_compl_iff, _root_.Set.mem_preimage, openCollapse, dif_pos hy, _root_.Set.mem_image]
        constructor
        · intro h
          exact ⟨⟨y, hy⟩, h, rfl⟩
        · rintro ⟨u, hu, rfl⟩
          exact hu
      · simp only [_root_.Set.mem_compl_iff, _root_.Set.mem_preimage, openCollapse, dif_neg hy, hinf, not_true_eq_false,
          _root_.Set.mem_image]
        refine ⟨False.elim, ?_⟩
        rintro ⟨u, _, hu⟩
        exact hy (hu ▸ u.property)
    rw [← isClosed_compl_iff, heq]
    exact (hc.image continuous_subtype_val).isClosed
  · have heq : openCollapse U ⁻¹' V =
        Subtype.val '' ((fun u : U => (u : OnePoint U)) ⁻¹' V) := by
      ext y
      by_cases hy : y ∈ U
      · simp only [_root_.Set.mem_preimage, openCollapse, dif_pos hy, _root_.Set.mem_image]
        constructor
        · intro h
          exact ⟨⟨y, hy⟩, h, rfl⟩
        · rintro ⟨u, hu, rfl⟩
          exact hu
      · simp only [_root_.Set.mem_preimage, openCollapse, dif_neg hy, hinf, _root_.Set.mem_image]
        refine ⟨False.elim, ?_⟩
        rintro ⟨u, _, hu⟩
        exact hy (hu ▸ u.property)
    rw [heq]
    exact hU.isOpenMap_subtype_val _ ((OnePoint.isOpen_iff_of_notMem hinf).mp hV)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_openCollapse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_openCollapse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_openCollapse ``Submission.DifferentialGeometry.Topology.continuous_openCollapse


theorem openCollapse_surjective (U : Set Y) (hU : Uᶜ.Nonempty) : _root_.Function.Surjective (openCollapse U) := by
  intro z
  induction z using OnePoint.rec with
  | infty =>
    obtain ⟨y, hy⟩ := hU
    exact ⟨y, openCollapse_of_notMem U hy⟩
  | coe y => exact ⟨y, openCollapse_of_mem U y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.openCollapse_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.openCollapse_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.openCollapse_surjective ``Submission.DifferentialGeometry.Topology.openCollapse_surjective



theorem openCollapse_prod_quotient [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (U : Set Y) (hU : IsOpen U) (hne : Uᶜ.Nonempty)
    (K : Type*) [TopologicalSpace K] :
    _root_.Topology.IsQuotientMap (Prod.map (id : K → K) (openCollapse U)) := by
  let := hU.locallyCompactSpace
  have hp : IsProperMap (Prod.map (id : K → K) (openCollapse U)) :=
    isProperMap_id.prodMap (continuous_openCollapse U hU).isProperMap
  exact hp.isClosedMap.isQuotientMap hp.continuous
    ((_root_.Function.surjective_id : _root_.Function.Surjective (id : K → K)).prodMap (openCollapse_surjective U hne))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.openCollapse_prod_quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.openCollapse_prod_quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.openCollapse_prod_quotient ``Submission.DifferentialGeometry.Topology.openCollapse_prod_quotient

end DifferentialGeometry.Topology
