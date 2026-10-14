import Submission.DifferentialGeometry.Topology.Manifold.ImmersionImageNhds
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapGluing
import Mathlib.Topology.Connected.LocallyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

universe u

private abbrev TubeDomain : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Icc (-2 : ℝ) 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.TubeDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.TubeDomain target :: scope.openDecls } }

namespace SphericalTubeSystem

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

theorem isPreconnected_range_tube (a : T.Index) : IsPreconnected (_root_.Set.range (T.tube a)) := by
  have hicc : PreconnectedSpace ↥(Set.Icc (-2 : ℝ) 2) :=
    isPreconnected_iff_preconnectedSpace.mp (isPreconnected_Icc (a := (-2 : ℝ)) (b := 2))
  have hpre : IsPreconnected (_root_.Set.univ : Set TubeDomain) := by
    simpa only [_root_.Set.univ_prod_univ] using isPreconnected_univ.prod _root_.PreconnectedSpace.isPreconnected_univ
  simpa only [_root_.Set.image_univ] using hpre.image _ (T.tube a).continuous.continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.isPreconnected_range_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.isPreconnected_range_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.isPreconnected_range_tube ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.isPreconnected_range_tube

theorem isClosed_range_tube (a : T.Index) : IsClosed (_root_.Set.range (T.tube a)) :=
  (isCompact_range (T.tube a).continuous).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.isClosed_range_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.isClosed_range_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.isClosed_range_tube ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.isClosed_range_tube

theorem removedBand_subset_range (a : T.Index) : T.removedBand a ⊆ _root_.Set.range (T.tube a) :=
  _root_.Set.image_subset_range _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.removedBand_subset_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.removedBand_subset_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.removedBand_subset_range ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.removedBand_subset_range

theorem closure_removedBand_subset_range (a : T.Index) :
    closure (T.removedBand a) ⊆ _root_.Set.range (T.tube a) :=
  closure_minimal (T.removedBand_subset_range a) (T.isClosed_range_tube a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.closure_removedBand_subset_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.closure_removedBand_subset_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.closure_removedBand_subset_range ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.closure_removedBand_subset_range

theorem mem_boundarySphere_of_mem_closure_removedBand {a : T.Index} {y : M.Carrier}
    (hy : y ∈ closure (T.removedBand a)) (hc : y ∈ T.core) :
    y ∈ _root_.Set.range (T.boundarySphere (a, _root_.Bool.false)) ∨ y ∈ _root_.Set.range (T.boundarySphere (a, _root_.Bool.true)) := by
  have hcont : Continuous fun z : TubeDomain => (z.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hlev : closure {z : TubeDomain | (-1 : ℝ) < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1} ⊆
      {z : TubeDomain | (-1 : ℝ) ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 1} := by
    have hset : {z : TubeDomain | (-1 : ℝ) < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1} =
        (fun z : TubeDomain => (z.2 : ℝ)) ⁻¹' _root_.Set.Ioo (-1 : ℝ) 1 := rfl
    rw [hset]
    refine (closure_minimal (_root_.Set.preimage_mono subset_closure)
      (isClosed_closure.preimage hcont)).trans ?_
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    intro z hz
    exact hz
  have hsub : closure (T.removedBand a) ⊆
      T.tube a '' {z : TubeDomain | (-1 : ℝ) ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 1} := by
    have h1 : closure (T.removedBand a) ⊆ T.tube a ''
        closure {z : TubeDomain | (-1 : ℝ) < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1} := by
      change closure (T.tube a ''
        {z : TubeDomain | (-1 : ℝ) < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1}) ⊆ _
      refine closure_minimal (_root_.Set.image_mono subset_closure) ?_
      have hK : IsCompact (closure {z : TubeDomain | (-1 : ℝ) < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1}) :=
        (isCompact_univ (X := TubeDomain)).of_isClosed_subset isClosed_closure (_root_.Set.subset_univ _)
      exact (hK.image (T.tube a).continuous).isClosed
    exact h1.trans (_root_.Set.image_mono hlev)
  obtain ⟨z, hz, hzy⟩ := hsub hy
  have hzcore : T.tube a z ∈ T.core := hzy ▸ hc
  have hnot : ¬((-1 : ℝ) < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1) := by
    rintro ⟨h1, h2⟩
    exact hzcore (mem_iUnion.mpr ⟨a, ⟨z, ⟨h1, h2⟩, rfl⟩⟩)
  have hlev' : (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1 := by
    rcases eq_or_lt_of_le hz.1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr (le_antisymm hz.2 (le_of_not_gt fun h' => hnot ⟨h, h'⟩))
  rcases hlev' with h | h
  · refine Or.inl ⟨z.1, ?_⟩
    have hzeq : (z.1, SphericalTubeSystem.boundaryLevel _root_.Bool.false) = z :=
      Prod.ext rfl (Subtype.ext h.symm)
    change T.tube a (z.1, SphericalTubeSystem.boundaryLevel _root_.Bool.false) = y
    rw [hzeq]
    exact hzy
  · refine Or.inr ⟨z.1, ?_⟩
    have hzeq : (z.1, SphericalTubeSystem.boundaryLevel _root_.Bool.true) = z :=
      Prod.ext rfl (Subtype.ext h.symm)
    change T.tube a (z.1, SphericalTubeSystem.boundaryLevel _root_.Bool.true) = y
    rw [hzeq]
    exact hzy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.mem_boundarySphere_of_mem_closure_removedBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.mem_boundarySphere_of_mem_closure_removedBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.mem_boundarySphere_of_mem_closure_removedBand ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.mem_boundarySphere_of_mem_closure_removedBand

theorem removedBand_isOpen (a : T.Index) : IsOpen (T.removedBand a) := by
  let _ : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨z, hz, rfl⟩
  apply immersion_image_mem_nhds ((T.smooth a).isImmersion.isImmersionAt z)
  · simp [EuclideanSpace, Module.finrank_prod]
  · change z ∈ ((𝓡 2).prod (𝓡∂ 1)).interior
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Icc (-2 : ℝ) 2)
    rw [ModelWithCorners.interior_prod]
    exact ⟨BoundarylessManifold.isInteriorPoint,
      Icc_isInteriorPoint_interior ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
  · exact ((isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)).mem_nhds hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.removedBand_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.removedBand_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.removedBand_isOpen ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.removedBand_isOpen

end SphericalTubeSystem

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

local instance instLocallyConnectedCore : LocallyConnectedSpace E.tubes.core :=
  E.capping.coreCharts.locallyConnectedSpace (EuclideanHalfSpace 3) E.tubes.core

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedCore ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedCore

theorem cutEndFactor_coe_eq_associatedFactor (C : ConnectedComponents M.Carrier)
    (a : E.cutIndices C) (side : Bool)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (E.cutEndFactor C a side z : ConnectedClosedOrientedManifold.{u} 3) =
      E.associatedFactor (E.tubes.coreBoundarySphere (a.1, side) z) :=
  E.cappedFactor_eq_of_mem C (E.cutCoreComponent C a side z)
    (E.tubes.coreBoundarySphere (a.1, side) z) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutEndFactor_coe_eq_associatedFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutEndFactor_coe_eq_associatedFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutEndFactor_coe_eq_associatedFactor ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutEndFactor_coe_eq_associatedFactor

theorem associatedFactor_eq_of_mk_eq (x y : E.tubes.core)
    (h : ConnectedComponents.mk x = ConnectedComponents.mk y) :
    E.associatedFactor x = E.associatedFactor y := by
  have hy : y ∈ connectedComponent x := ConnectedComponents.coe_eq_coe'.mp h.symm
  have hsub := (isPreconnected_connectedComponent (x := x)).image _
    E.capping.coreInclusion.continuous.continuousOn |>.subset_connectedComponent
    ⟨x, mem_connectedComponent, rfl⟩
  have hmk : ConnectedComponents.mk (E.capping.coreInclusion x) =
      ConnectedComponents.mk (E.capping.coreInclusion y) :=
    (ConnectedComponents.coe_eq_coe'.mpr (hsub ⟨y, hy, rfl⟩)).symm
  exact E.associatedFactor_eq_of_mk_coreInclusion_eq x y hmk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_mk_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_mk_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_mk_eq ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_mk_eq

theorem exists_mem_removedBand_of_notMem_core {y : M.Carrier} (h : y ∉ E.tubes.core) :
    ∃ a : E.tubes.Index, y ∈ E.tubes.removedBand a := by
  by_contra hc
  refine h (by rw [SphericalTubeSystem.core]; intro hmem; exact hc (mem_iUnion.mp hmem))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_mem_removedBand_of_notMem_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_mem_removedBand_of_notMem_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_mem_removedBand_of_notMem_core ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_mem_removedBand_of_notMem_core

theorem range_tube_subset_of_mem_removedBand (C : ConnectedComponents M.Carrier)
    {a : E.tubes.Index} {y : M.Carrier} (hy : y ∈ E.tubes.removedBand a)
    (hyC : y ∈ ClosedOrientedManifold.componentSet M C) :
    range (E.tubes.tube a) ⊆ ClosedOrientedManifold.componentSet M C := by
  have hyC' : ConnectedComponents.mk y = C :=
    (ClosedOrientedManifold.mem_componentSet M C y).mp hyC
  have hycore : y ∈ _root_.Set.range (E.tubes.tube a) :=
    E.tubes.removedBand_subset_range a hy
  intro x hx
  rw [ClosedOrientedManifold.mem_componentSet]
  exact (ConnectedComponents.coe_eq_coe'.mpr
    ((E.tubes.isPreconnected_range_tube a).subset_connectedComponent hycore hx)).trans hyC'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.range_tube_subset_of_mem_removedBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.range_tube_subset_of_mem_removedBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.range_tube_subset_of_mem_removedBand ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.range_tube_subset_of_mem_removedBand

theorem mem_cutIndices_of_mem_removedBand (C : ConnectedComponents M.Carrier)
    {a : E.tubes.Index} {y : M.Carrier} (hy : y ∈ E.tubes.removedBand a)
    (hyC : y ∈ ClosedOrientedManifold.componentSet M C) :
    a ∈ E.cutIndices C := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, fun z =>
    E.range_tube_subset_of_mem_removedBand C hy hyC ⟨z, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.mem_cutIndices_of_mem_removedBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.mem_cutIndices_of_mem_removedBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.mem_cutIndices_of_mem_removedBand ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.mem_cutIndices_of_mem_removedBand

theorem exists_nhds_associatedFactor_eq (x : E.tubes.core) :
    ∃ O : Set M.Carrier, O ∈ 𝓝 (x : M.Carrier) ∧
      ∀ y ∈ O, ∀ (hyc : y ∈ E.tubes.core),
        E.associatedFactor ⟨y, hyc⟩ = E.associatedFactor x := by
  have hopen : IsOpen {z : E.tubes.core |
      ConnectedComponents.mk z = ConnectedComponents.mk x} := by
    have hset : {z : E.tubes.core | ConnectedComponents.mk z = ConnectedComponents.mk x} =
        connectedComponent x := by
      ext z
      exact ConnectedComponents.coe_eq_coe'
    rw [hset]
    exact isOpen_connectedComponent
  obtain ⟨O, hOopen, hOsub⟩ := isOpen_induced_iff.mp hopen
  have hxO : (x : M.Carrier) ∈ O := by
    have hx : x ∈ Subtype.val ⁻¹' O := by rw [hOsub]; exact rfl
    exact hx
  refine ⟨O, hOopen.mem_nhds hxO, ?_⟩
  intro y hy hyc
  refine E.associatedFactor_eq_of_mk_eq _ _ ?_
  have hy' : (⟨y, hyc⟩ : E.tubes.core) ∈ Subtype.val ⁻¹' O := hy
  rw [hOsub] at hy'
  exact hy'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_nhds_associatedFactor_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_nhds_associatedFactor_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_nhds_associatedFactor_eq ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_nhds_associatedFactor_eq

theorem reachable_cutEndFactor_false_true (C : ConnectedComponents M.Carrier)
    (a : E.cutIndices C) :
    (E.cutIncidenceGraph C).Reachable
      (E.cutEndFactor C a _root_.Bool.false sphereBasePoint)
      (E.cutEndFactor C a _root_.Bool.true sphereBasePoint) := by
  by_cases h : E.cutEndFactor C a _root_.Bool.false sphereBasePoint =
      E.cutEndFactor C a _root_.Bool.true sphereBasePoint
  · rw [h]
  · exact SimpleGraph.Adj.reachable
      ((E.cutIncidenceGraph_adj C _ _).mpr ⟨h, ⟨a, rfl⟩⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.reachable_cutEndFactor_false_true then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.reachable_cutEndFactor_false_true"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.reachable_cutEndFactor_false_true ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.reachable_cutEndFactor_false_true

end SphericalCutCapTransition

private abbrev ComponentCarrier (M : ClosedOrientedManifold.{u} 3)
    (C : ConnectedComponents M.Carrier) : Type u :=
  ↥(ClosedOrientedManifold.componentSet M C)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ComponentCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ComponentCarrier target :: scope.openDecls } }

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)
  (C : ConnectedComponents M.Carrier)

theorem notMem_core_of_mem_removedBand {a : E.tubes.Index} {z : M.Carrier}
    (h : z ∈ E.tubes.removedBand a) : z ∉ E.tubes.core :=
  fun hc => hc (mem_iUnion.mpr ⟨a, h⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.notMem_core_of_mem_removedBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.notMem_core_of_mem_removedBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.notMem_core_of_mem_removedBand ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.notMem_core_of_mem_removedBand

theorem eq_of_mem_removedBand {a a' : E.tubes.Index} {z : M.Carrier}
    (h : z ∈ E.tubes.removedBand a) (h' : z ∈ E.tubes.removedBand a') : a = a' := by
  by_contra hne
  exact Set.disjoint_left.mp (E.tubes.disjoint hne)
    (E.tubes.removedBand_subset_range a h) (E.tubes.removedBand_subset_range a' h')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.eq_of_mem_removedBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.eq_of_mem_removedBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.eq_of_mem_removedBand ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.eq_of_mem_removedBand

theorem isPreconnected_range_coreBoundarySphere (a : E.tubes.Index) (s : Bool) :
    IsPreconnected (_root_.Set.range (E.tubes.coreBoundarySphere (a, s))) := by
  have hpre : IsPreconnected (_root_.Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
    _root_.PreconnectedSpace.isPreconnected_univ
  simpa only [_root_.Set.image_univ] using
    hpre.image _ (E.tubes.coreBoundarySphere (a, s)).continuous.continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isPreconnected_range_coreBoundarySphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isPreconnected_range_coreBoundarySphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isPreconnected_range_coreBoundarySphere ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isPreconnected_range_coreBoundarySphere

theorem reachable_cutEndFactor_false_of (a : E.cutIndices C) (s : Bool)
    (z z' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (E.cutIncidenceGraph C).Reachable (E.cutEndFactor C a s z)
      (E.cutEndFactor C a _root_.Bool.false z') := by
  rw [E.cutEndFactor_eq C a s z sphereBasePoint,
    E.cutEndFactor_eq C a _root_.Bool.false z' sphereBasePoint]
  by_cases hs : s = _root_.Bool.false
  · subst hs
    exact SimpleGraph.Reachable.rfl
  · have hs' : s = true := by cases s <;> simp_all
    subst hs'
    exact (E.reachable_cutEndFactor_false_true C a).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.reachable_cutEndFactor_false_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.reachable_cutEndFactor_false_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.reachable_cutEndFactor_false_of ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.reachable_cutEndFactor_false_of

private noncomputable def pointVertex (y : ComponentCarrier M C) : ↥(E.associatedFactors C) := by
  classical
  exact
    if h : (y : M.Carrier) ∈ E.tubes.core then
      ⟨E.associatedFactor ⟨(y : M.Carrier), h⟩,
        ⟨⟨(y : M.Carrier), h⟩,
          (ClosedOrientedManifold.mem_componentSet M C _).mp y.2, rfl⟩⟩
    else
      E.cutEndFactor C
        ⟨Classical.choose (E.exists_mem_removedBand_of_notMem_core h),
          E.mem_cutIndices_of_mem_removedBand C
            (Classical.choose_spec (E.exists_mem_removedBand_of_notMem_core h)) y.2⟩
        _root_.Bool.false sphereBasePoint

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.pointVertex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.pointVertex target :: scope.openDecls } }

private theorem pointVertex_of_mem_core {y : ComponentCarrier M C}
    (h : (y : M.Carrier) ∈ E.tubes.core) :
    E.pointVertex C y = ⟨E.associatedFactor ⟨(y : M.Carrier), h⟩,
      ⟨⟨(y : M.Carrier), h⟩, (ClosedOrientedManifold.mem_componentSet M C _).mp y.2, rfl⟩⟩ := by
  rw [pointVertex]
  exact dif_pos h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.pointVertex_of_mem_core
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.pointVertex_of_mem_core target :: scope.openDecls } }

private theorem pointVertex_of_notMem_core {y : ComponentCarrier M C}
    (h : (y : M.Carrier) ∉ E.tubes.core) :
    E.pointVertex C y = E.cutEndFactor C
      ⟨Classical.choose (E.exists_mem_removedBand_of_notMem_core h),
        E.mem_cutIndices_of_mem_removedBand C
          (Classical.choose_spec (E.exists_mem_removedBand_of_notMem_core h)) y.2⟩
      false sphereBasePoint := by
  rw [pointVertex]
  exact dif_neg h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.pointVertex_of_notMem_core
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.pointVertex_of_notMem_core target :: scope.openDecls } }

private theorem pointVertex_eq_of_mem_removedBand {y : ComponentCarrier M C} {a : E.tubes.Index}
    (hy : (y : M.Carrier) ∈ E.tubes.removedBand a) (hmem : a ∈ E.cutIndices C) :
    E.pointVertex C y = E.cutEndFactor C ⟨a, hmem⟩ _root_.Bool.false sphereBasePoint := by
  have hnot : (y : M.Carrier) ∉ E.tubes.core := E.notMem_core_of_mem_removedBand hy
  rw [E.pointVertex_of_notMem_core C hnot]
  have hspec := Classical.choose_spec (E.exists_mem_removedBand_of_notMem_core hnot)
  have hchosen : Classical.choose (E.exists_mem_removedBand_of_notMem_core hnot) = a :=
    E.eq_of_mem_removedBand hspec hy
  exact congrArg (fun b : E.cutIndices C => E.cutEndFactor C b _root_.Bool.false sphereBasePoint)
    (Subtype.ext hchosen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.pointVertex_eq_of_mem_removedBand
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.pointVertex_eq_of_mem_removedBand target :: scope.openDecls } }

private theorem pointVertex_eq_cutEndFactor_of_boundarySphere {y : ComponentCarrier M C}
    {a : E.tubes.Index} (s : Bool)
    (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hw : E.tubes.boundarySphere (a, s) w = (y : M.Carrier))
    (hy : (y : M.Carrier) ∈ E.tubes.core) (hmem : a ∈ E.cutIndices C) :
    E.pointVertex C y = E.cutEndFactor C ⟨a, hmem⟩ s sphereBasePoint := by
  have hyrange : (⟨(y : M.Carrier), hy⟩ : E.tubes.core) ∈
      range (E.tubes.coreBoundarySphere (a, s)) :=
    ⟨w, Subtype.ext hw⟩
  have hpre : IsPreconnected (_root_.Set.range (E.tubes.coreBoundarySphere (a, s))) :=
    E.isPreconnected_range_coreBoundarySphere a s
  have hmk : ConnectedComponents.mk (E.tubes.coreBoundarySphere (a, s) sphereBasePoint) =
      ConnectedComponents.mk (⟨(y : M.Carrier), hy⟩ : E.tubes.core) :=
    (ConnectedComponents.coe_eq_coe'.mpr
      (hpre.subset_connectedComponent ⟨sphereBasePoint, rfl⟩ hyrange)).symm
  have hfac := E.associatedFactor_eq_of_mk_eq _ _ hmk
  rw [E.pointVertex_of_mem_core C hy]
  exact Subtype.ext
    ((E.cutEndFactor_coe_eq_associatedFactor C ⟨a, hmem⟩ s sphereBasePoint).trans hfac).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.pointVertex_eq_cutEndFactor_of_boundarySphere
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.pointVertex_eq_cutEndFactor_of_boundarySphere target :: scope.openDecls } }

private theorem exists_nhds_pointVertex_reachable
    (hopen : ∀ a : E.tubes.Index, IsOpen (E.tubes.removedBand a))
    (y : ComponentCarrier M C) :
    ∃ O : Set (ComponentCarrier M C), O ∈ 𝓝 y ∧ ∀ z ∈ O,
      (E.cutIncidenceGraph C).Reachable (E.pointVertex C y) (E.pointVertex C z) := by
  classical
  by_cases hycore : (y : M.Carrier) ∈ E.tubes.core
  · obtain ⟨Oc, hOc_nhds, hOc_fac⟩ :=
      E.exists_nhds_associatedFactor_eq ⟨(y : M.Carrier), hycore⟩
    have hbad_closed : IsClosed (⋃ a ∈ {a : E.tubes.Index |
        (y : M.Carrier) ∉ closure (E.tubes.removedBand a)},
        closure (E.tubes.removedBand a)) :=
      (Set.toFinite _).isClosed_biUnion fun a _ => isClosed_closure
    have hy_bad : (y : M.Carrier) ∉ (⋃ a ∈ {a : E.tubes.Index |
        (y : M.Carrier) ∉ closure (E.tubes.removedBand a)},
        closure (E.tubes.removedBand a)) := by
      intro h
      simp only [_root_.Set.mem_iUnion] at h
      obtain ⟨a, ha, hya⟩ := h
      exact ha hya
    have hO_nhds : Oc ∩ (⋃ a ∈ {a : E.tubes.Index |
        (y : M.Carrier) ∉ closure (E.tubes.removedBand a)},
        closure (E.tubes.removedBand a))ᶜ ∈ 𝓝 (y : M.Carrier) :=
      Filter.inter_mem hOc_nhds (hbad_closed.isOpen_compl.mem_nhds hy_bad)
    refine ⟨Subtype.val ⁻¹' (Oc ∩ (⋃ a ∈ {a : E.tubes.Index |
        (y : M.Carrier) ∉ closure (E.tubes.removedBand a)},
        closure (E.tubes.removedBand a))ᶜ), ?_, ?_⟩
    · exact continuous_subtype_val.continuousAt.preimage_mem_nhds hO_nhds
    · intro z hz
      have hzO : (z : M.Carrier) ∈ Oc ∧ (z : M.Carrier) ∉ (⋃ a ∈ {a : E.tubes.Index |
          (y : M.Carrier) ∉ closure (E.tubes.removedBand a)},
          closure (E.tubes.removedBand a)) := hz
      by_cases hzcore : (z : M.Carrier) ∈ E.tubes.core
      · rw [E.pointVertex_of_mem_core C hycore, E.pointVertex_of_mem_core C hzcore]
        have hfac := hOc_fac (z : M.Carrier) hzO.1 hzcore
        have hveq : (⟨E.associatedFactor ⟨(y : M.Carrier), hycore⟩,
            ⟨⟨(y : M.Carrier), hycore⟩,
              (ClosedOrientedManifold.mem_componentSet M C _).mp y.2, rfl⟩⟩ :
              ↥(E.associatedFactors C)) =
            ⟨E.associatedFactor ⟨(z : M.Carrier), hzcore⟩,
              ⟨⟨(z : M.Carrier), hzcore⟩,
                (ClosedOrientedManifold.mem_componentSet M C _).mp z.2, rfl⟩⟩ :=
          Subtype.ext hfac.symm
        rw [hveq]
      · obtain ⟨a, ha⟩ := E.exists_mem_removedBand_of_notMem_core hzcore
        have hy_cl : (y : M.Carrier) ∈ closure (E.tubes.removedBand a) := by
          by_contra hyNot
          refine hzO.2 (mem_iUnion.mpr ⟨a, ?_⟩)
          exact mem_iUnion.mpr ⟨hyNot, subset_closure ha⟩
        have hmem : a ∈ E.cutIndices C := E.mem_cutIndices_of_mem_removedBand C ha z.2
        have hz_eq : E.pointVertex C z = E.cutEndFactor C ⟨a, hmem⟩ _root_.Bool.false sphereBasePoint :=
          E.pointVertex_eq_of_mem_removedBand C ha hmem
        rcases E.tubes.mem_boundarySphere_of_mem_closure_removedBand hy_cl hycore with
          ⟨w, hw⟩ | ⟨w, hw⟩
        · have hy_eq : E.pointVertex C y = E.cutEndFactor C ⟨a, hmem⟩ _root_.Bool.false sphereBasePoint :=
            E.pointVertex_eq_cutEndFactor_of_boundarySphere C _root_.Bool.false w hw hycore hmem
          rw [hy_eq, hz_eq]
        · have hy_eq : E.pointVertex C y = E.cutEndFactor C ⟨a, hmem⟩ _root_.Bool.true sphereBasePoint :=
            E.pointVertex_eq_cutEndFactor_of_boundarySphere C _root_.Bool.true w hw hycore hmem
          rw [hy_eq, hz_eq]
          exact E.reachable_cutEndFactor_false_of C ⟨a, hmem⟩ _root_.Bool.true sphereBasePoint sphereBasePoint
  · obtain ⟨a, ha⟩ := E.exists_mem_removedBand_of_notMem_core hycore
    have hmem : a ∈ E.cutIndices C := E.mem_cutIndices_of_mem_removedBand C ha y.2
    refine ⟨Subtype.val ⁻¹' E.tubes.removedBand a, ?_, ?_⟩
    · exact continuous_subtype_val.continuousAt.preimage_mem_nhds
        ((hopen a).mem_nhds ha)
    · intro z hz
      rw [E.pointVertex_eq_of_mem_removedBand C ha hmem,
        E.pointVertex_eq_of_mem_removedBand C hz hmem]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_nhds_pointVertex_reachable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_nhds_pointVertex_reachable target :: scope.openDecls } }

theorem exists_core_mem_componentSet (C : ConnectedComponents M.Carrier) :
    ∃ x : E.tubes.core, (x : M.Carrier) ∈ ClosedOrientedManifold.componentSet M C := by
  classical
  obtain ⟨y, hyC⟩ := ClosedOrientedManifold.componentSet_nonempty M C
  by_cases hcore : y ∈ E.tubes.core
  · exact ⟨⟨y, hcore⟩, hyC⟩
  · obtain ⟨a, ha⟩ := E.exists_mem_removedBand_of_notMem_core hcore
    have hsub := E.range_tube_subset_of_mem_removedBand C ha hyC
    refine ⟨⟨E.tubes.tube a (sphereBasePoint, ⟨3 / 2, by norm_num⟩), ?_⟩, hsub ⟨_, rfl⟩⟩
    rw [SphericalTubeSystem.core]
    intro hmem
    simp only [_root_.Set.mem_iUnion] at hmem
    obtain ⟨b, hb⟩ := hmem
    by_cases hba : b = a
    · rw [hba] at hb
      obtain ⟨w, hw, hwp⟩ := hb
      let _ : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
      have hw' : w = (sphereBasePoint, ⟨3 / 2, by norm_num⟩) :=
        (E.tubes.smooth a).isEmbedding.injective hwp
      have hlevel : ((w.2 : ℝ)) = 3 / 2 := by
        have := congrArg (fun q : TubeDomain => (q.2 : ℝ)) hw'
        simpa using this
      linarith [hw.1, hw.2, hlevel]
    · have h1 : E.tubes.tube a (sphereBasePoint, ⟨3 / 2, by norm_num⟩) ∈
          range (E.tubes.tube b) :=
        E.tubes.removedBand_subset_range b hb
      exact Set.disjoint_left.mp (E.tubes.disjoint hba) h1 ⟨_, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_core_mem_componentSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_core_mem_componentSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_core_mem_componentSet ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_core_mem_componentSet

private theorem exists_pointVertex_eq (w : ↥(E.associatedFactors C)) :
    ∃ y : ComponentCarrier M C, E.pointVertex C y = w := by
  obtain ⟨x, hx, hxw⟩ := w.2
  exact ⟨⟨(x : M.Carrier), (ClosedOrientedManifold.mem_componentSet M C _).mpr hx⟩,
    (E.pointVertex_of_mem_core C x.2).trans (Subtype.ext hxw)⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_pointVertex_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_pointVertex_eq target :: scope.openDecls } }

theorem cutIncidenceGraph_connected_of_removedBand_isOpen
    (hopen : ∀ a : E.tubes.Index, IsOpen (E.tubes.removedBand a))
    (C : ConnectedComponents M.Carrier) :
    (E.cutIncidenceGraph C).Connected := by
  classical
  obtain ⟨x₀, hx₀⟩ := E.exists_core_mem_componentSet C
  set y₀ : ComponentCarrier M C := ⟨(x₀ : M.Carrier), hx₀⟩ with hy₀def
  set v₀ : ↥(E.associatedFactors C) := E.pointVertex C y₀ with hv₀def
  have hlocal : ∀ y : ComponentCarrier M C,
      ∃ O : Set (ComponentCarrier M C), O ∈ 𝓝 y ∧ ∀ z ∈ O,
        (E.cutIncidenceGraph C).Reachable (E.pointVertex C y) (E.pointVertex C z) :=
    fun y => E.exists_nhds_pointVertex_reachable C hopen y
  have hS_open : IsOpen {y : ComponentCarrier M C |
      (E.cutIncidenceGraph C).Reachable v₀ (E.pointVertex C y)} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨O, hO, hOloc⟩ := hlocal y
    exact Filter.mem_of_superset hO fun z hz => hy.trans (hOloc z hz)
  have hSc_open : IsOpen {y : ComponentCarrier M C |
      ¬ (E.cutIncidenceGraph C).Reachable v₀ (E.pointVertex C y)} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨O, hO, hOloc⟩ := hlocal y
    refine Filter.mem_of_superset hO fun z hz hzS => hy ?_
    exact hzS.trans (hOloc z hz).symm
  have hpreSpace : PreconnectedSpace (ComponentCarrier M C) :=
    isPreconnected_iff_preconnectedSpace.mp
      (ClosedOrientedManifold.isConnected_componentSet M C).isPreconnected
  have hmem : ∀ y : ComponentCarrier M C,
      (E.cutIncidenceGraph C).Reachable v₀ (E.pointVertex C y) := by
    intro y
    rcases (_root_.PreconnectedSpace.isPreconnected_univ (α := ComponentCarrier M C)).subset_or_subset hS_open
      hSc_open disjoint_compl_right (fun z _ => by
        by_cases h : (E.cutIncidenceGraph C).Reachable v₀ (E.pointVertex C z)
        · exact Or.inl h
        · exact Or.inr h) with h | h
    · exact h (_root_.Set.mem_univ y)
    · exact absurd (h (_root_.Set.mem_univ y₀)) (by intro hc; exact hc SimpleGraph.Reachable.rfl)
  refine SimpleGraph.Connected.mk (preconnected := fun u v => ?_) (nonempty := ⟨v₀⟩)
  obtain ⟨yu, hyu⟩ := E.exists_pointVertex_eq (w := u)
  obtain ⟨yv, hyv⟩ := E.exists_pointVertex_eq (w := v)
  rw [← hyu, ← hyv]
  exact (hmem yu).symm.trans (hmem yv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph_connected_of_removedBand_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph_connected_of_removedBand_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph_connected_of_removedBand_isOpen ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph_connected_of_removedBand_isOpen

theorem cutIncidenceGraph_connected (C : ConnectedComponents M.Carrier) :
    (E.cutIncidenceGraph C).Connected :=
  E.cutIncidenceGraph_connected_of_removedBand_isOpen (fun a => E.tubes.removedBand_isOpen a) C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph_connected ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutIncidenceGraph_connected

theorem CompleteEnumeration.length_eq {C : ConnectedComponents M.Carrier}
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hL : E.CompleteEnumeration C L) (hK : E.CompleteEnumeration C K) :
    L.length = K.length := by
  have h1 := E.ncard_associatedFactors_eq_length hL
  have h2 := E.ncard_associatedFactors_eq_length hK
  omega

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.CompleteEnumeration
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.CompleteEnumeration.length_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.CompleteEnumeration.length_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.CompleteEnumeration.length_eq ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.CompleteEnumeration.length_eq

theorem associatedFactors_nonempty (C : ConnectedComponents M.Carrier) :
    (E.associatedFactors C).Nonempty := by
  obtain ⟨x, hx⟩ := E.exists_core_mem_componentSet C
  exact ⟨E.associatedFactor x, x, hx, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors_nonempty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors_nonempty

theorem one_le_length_of_completeEnumeration {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)} (hL : E.CompleteEnumeration C L) :
    1 ≤ L.length := by
  have h := E.ncard_associatedFactors_eq_length hL
  have hpos : 0 < (E.associatedFactors C).ncard :=
    Set.ncard_pos (E.associatedFactors_finite C) |>.mpr (E.associatedFactors_nonempty C)
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.one_le_length_of_completeEnumeration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.one_le_length_of_completeEnumeration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.one_le_length_of_completeEnumeration ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.one_le_length_of_completeEnumeration

theorem cutIndices_eq_empty_iff (C : ConnectedComponents M.Carrier) :
    E.cutIndices C = ∅ ↔
      ∀ a : E.tubes.Index, ¬ ∃ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
        Set.Icc (-2 : ℝ) 2, E.tubes.tube a z ∈
          ClosedOrientedManifold.componentSet M C := by
  constructor
  · intro h a hz
    exact absurd (h ▸ (E.mem_cutIndices_iff_exists_tube_mem_componentSet C a).mpr hz)
      (Finset.notMem_empty a)
  · intro h
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨a, ha⟩
    exact h a ((E.mem_cutIndices_iff_exists_tube_mem_componentSet C a).mp ha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIndices_eq_empty_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutIndices_eq_empty_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIndices_eq_empty_iff ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutIndices_eq_empty_iff

theorem componentSet_subset_core_of_cutIndices_eq_empty (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) :
    ClosedOrientedManifold.componentSet M C ⊆ E.tubes.core := by
  intro y hy
  by_contra hnot
  obtain ⟨a, ha⟩ := E.exists_mem_removedBand_of_notMem_core hnot
  exact Finset.notMem_empty a (hC ▸ E.mem_cutIndices_of_mem_removedBand C ha hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentSet_subset_core_of_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentSet_subset_core_of_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentSet_subset_core_of_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentSet_subset_core_of_cutIndices_eq_empty

theorem associatedFactor_eq_of_mem_componentSet_of_cutIndices_eq_empty
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    {x x' : E.tubes.core} (hx : ConnectedComponents.mk x.1 = C)
    (hx' : ConnectedComponents.mk x'.1 = C) :
    E.associatedFactor x = E.associatedFactor x' := by
  have hsub := E.componentSet_subset_core_of_cutIndices_eq_empty C hC
  have hlc : IsLocallyConstant fun w : (M.component C).Carrier =>
      E.associatedFactor ⟨w.1, hsub w.2⟩ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro w
    obtain ⟨O, hO, hOloc⟩ := E.exists_nhds_associatedFactor_eq ⟨w.1, hsub w.2⟩
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds hO] with w' hw'
    exact hOloc w'.1 hw' (hsub w'.2)
  have key := hlc.apply_eq_of_preconnectedSpace
    (⟨x.1, hx⟩ : (M.component C).Carrier) (⟨x'.1, hx'⟩ : (M.component C).Carrier)
  have hx_eq : x = ⟨x.1, hsub hx⟩ := Subtype.ext rfl
  have hx'_eq : x' = ⟨x'.1, hsub hx'⟩ := Subtype.ext rfl
  rw [hx_eq, hx'_eq]
  exact key

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_mem_componentSet_of_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_mem_componentSet_of_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_mem_componentSet_of_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_mem_componentSet_of_cutIndices_eq_empty

theorem exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅) :
    ∃ N : ConnectedClosedOrientedManifold.{u} 3, E.associatedFactors C = {N} := by
  obtain ⟨x₀, hx₀⟩ := E.exists_core_mem_componentSet C
  refine ⟨E.associatedFactor x₀, ?_⟩
  ext N
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_singleton_iff]
    exact E.associatedFactor_eq_of_mem_componentSet_of_cutIndices_eq_empty C hC hx hx₀
  · intro hN
    rw [Set.mem_singleton_iff] at hN
    exact ⟨x₀, hx₀, hN.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty

theorem eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty
    {C : ConnectedComponents M.Carrier} {L : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hL : E.CompleteEnumeration C L) (hC : E.cutIndices C = ∅) :
    ∃ N : ConnectedClosedOrientedManifold.{u} 3, L = [N] := by
  obtain ⟨N, hN⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C hC
  refine ⟨N, ?_⟩
  have hlen : L.length = 1 := by
    rw [← E.ncard_associatedFactors_eq_length hL, hN, Set.ncard_singleton]
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  have hmem : a ∈ L := by rw [ha]; exact List.mem_singleton.mpr rfl
  have haN : a = N := by
    have h := hL.2.1 a hmem
    rw [hN, Set.mem_singleton_iff] at h
    exact h
  rw [ha, haN]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty

def NoTubeRealization : Prop :=
  ∀ (C : ConnectedComponents M.Carrier) (N : ConnectedClosedOrientedManifold.{u} 3),
    E.cutIndices C = ∅ → E.associatedFactors C = {N} →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold N.toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.NoTubeRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.NoTubeRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.NoTubeRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.NoTubeRealization

theorem localReconstruction_of_noTubeRealization (hr : E.NoTubeRealization)
    (hC : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.localReconstruction := by
  intro C L hL
  obtain ⟨N, hN⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C (hC C)
  obtain ⟨ρ⟩ := hr C N (hC C) hN
  obtain ⟨N', hL'⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty hL (hC C)
  have hNN' : N' = N := by
    have hmem : N' ∈ L := by rw [hL']; exact List.mem_singleton.mpr rfl
    have h := hL.2.1 N' hmem
    rw [hN, Set.mem_singleton_iff] at h
    exact h
  refine ⟨0, [], rfl, by simp, ?_, ?_⟩
  · rw [hL']; simp [hC C]
  rw [hL', hNN']
  exact ⟨ρ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_noTubeRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_noTubeRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_noTubeRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_noTubeRealization

theorem localReconstruction_of_isEmpty_index [IsEmpty E.tubes.Index]
    (hr : E.NoTubeRealization) : E.localReconstruction :=
  E.localReconstruction_of_noTubeRealization hr fun _ =>
    Finset.not_nonempty_iff_eq_empty.mp fun h => h.elim fun a _ => isEmptyElim a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction_of_isEmpty_index

theorem componentConnectedSumDecomposition_of_noTubeRealization (hr : E.NoTubeRealization)
    (hC : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_of_localReconstruction
    (E.localReconstruction_of_noTubeRealization hr hC)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_noTubeRealization

theorem componentConnectedSumDecomposition_of_isEmpty_index [IsEmpty E.tubes.Index]
    (hr : E.NoTubeRealization) : E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_of_localReconstruction
    (E.localReconstruction_of_isEmpty_index hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_isEmpty_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_isEmpty_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_isEmpty_index ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentConnectedSumDecomposition_of_isEmpty_index

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem cutIncidenceGraph_connected
    (i : Fin T.eventCount) (C : ConnectedComponents (T.stage i.castSucc).Carrier) :
    ((T.transition i).cutIncidenceGraph C).Connected :=
  (T.transition i).cutIncidenceGraph_connected C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.cutIncidenceGraph_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.cutIncidenceGraph_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.cutIncidenceGraph_connected ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.cutIncidenceGraph_connected

end FiniteCutCapTrace

end DifferentialGeometry.Topology
