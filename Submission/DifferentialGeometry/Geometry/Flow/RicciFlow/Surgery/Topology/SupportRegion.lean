import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ComparisonDefs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

noncomputable abbrev supportRegion (G : GeometricCutoffRecord H i parameters)
    (c : ConnectedComponents (H.stage i.succ).Carrier) : Set (G.Parent c).Carrier :=
  Set.range (G.transition.childCoreIntoParent c) ∪ ⋃ b, Set.range (G.collarMap c b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.supportRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.supportRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.supportRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.supportRegion

theorem isCompact_supportRegion (G : GeometricCutoffRecord H i parameters)
    (c : ConnectedComponents (H.stage i.succ).Carrier) :
    IsCompact (supportRegion G c) := by
  refine IsCompact.union ?_ ?_
  · let : CompactSpace (G.transition.ChildCore c) := G.transition.childCore_compactSpace c
    exact isCompact_range (G.transition.childCoreIntoParent c).continuous
  · exact isCompact_iUnion fun b => isCompact_range (G.collarMap c b).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_supportRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_supportRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_supportRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_supportRegion

theorem sphere_connectedSpace : ConnectedSpace (Sphere 2) :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := EuclideanSpace ℝ (Fin 3))
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 zero_le_one)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphere_connectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphere_connectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphere_connectedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphere_connectedSpace

theorem isConnected_supportRegion (G : GeometricCutoffRecord H i parameters)
    (c : ConnectedComponents (H.stage i.succ).Carrier) :
    IsConnected (supportRegion G c) := by
  have hA : IsConnected (Set.range (G.transition.childCoreIntoParent c) :
      Set (G.Parent c).Carrier) := by
    obtain ⟨x₀, hx₀⟩ := ConnectedComponents.surjective_coe (G.transition.childCoreComponent c)
    have hset : ({z : G.transition.trace.tubes.core |
        ConnectedComponents.mk z = G.transition.childCoreComponent c} : Set _) =
        connectedComponent x₀ := by
      ext z
      rw [← hx₀]
      exact ConnectedComponents.coe_eq_coe'
    have hic : IsConnected ({z : G.transition.trace.tubes.core |
        ConnectedComponents.mk z = G.transition.childCoreComponent c} : Set _) :=
      hset ▸ isConnected_connectedComponent
    have hcs : ConnectedSpace (G.transition.ChildCore c) := isConnected_iff_connectedSpace.mp hic
    have huniv : IsConnected (Set.univ : Set (G.transition.ChildCore c)) :=
      connectedSpace_iff_univ.mp hcs
    let f : G.transition.ChildCore c → (G.Parent c).Carrier :=
      ⇑(G.transition.childCoreIntoParent c)
    have hf : Continuous f := (G.transition.childCoreIntoParent c).continuous
    have himg : IsConnected (f '' Set.univ) := huniv.image f hf.continuousOn
    rw [Set.image_univ] at himg
    exact himg
  have hC : ∀ b : G.ChildBoundary c, IsConnected (Set.range (G.collarMap c b)) := by
    intro b
    let : ConnectedSpace (Sphere 2) := sphere_connectedSpace
    let : ConnectedSpace ↑(_root_.Set.Icc (G.comparisonLevel c b) 0) :=
      { toPreconnectedSpace := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
        toNonempty := ⟨⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩⟩ }
    have hdom : IsConnected (Set.univ : Set (Sphere 2 × ↑(_root_.Set.Icc (G.comparisonLevel c b) 0))) :=
      connectedSpace_iff_univ.mp inferInstance
    simpa only [Set.image_univ] using
      hdom.image (G.collarMap c b) (G.collarMap c b).continuous.continuousOn
  have hmeet : ∀ b : G.ChildBoundary c,
      (Set.range (G.collarMap c b) ∩ Set.range (G.transition.childCoreIntoParent c) :
        Set (G.Parent c).Carrier).Nonempty := by
    intro b
    refine ⟨G.collarMap c b (DifferentialGeometry.Topology.sphereTwoNorth,
      ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩), Set.mem_range_self _, ?_⟩
    exact G.collarMap_zero_mem_childCore_range c b DifferentialGeometry.Topology.sphereTwoNorth
  let s : Option (G.ChildBoundary c) → Set (G.Parent c).Carrier := fun o =>
    match o with
    | none => Set.range (G.transition.childCoreIntoParent c)
    | some b => Set.range (G.collarMap c b)
  have hs : ∀ o, IsConnected (s o) := by
    rintro (_ | b)
    · exact hA
    · exact hC b
  have hK : ∀ o o', Relation.ReflTransGen (fun x y => (s x ∩ s y).Nonempty) o o' := by
    intro o o'
    match o, o' with
    | none, _root_.Option.none => exact Relation.ReflTransGen.refl
    | none, _root_.Option.some b =>
        refine Relation.ReflTransGen.tail Relation.ReflTransGen.refl ?_
        change (Set.range (G.transition.childCoreIntoParent c) ∩
          Set.range (G.collarMap c b)).Nonempty
        exact (hmeet b).mono (Set.inter_comm _ _).subset
    | some b, _root_.Option.none =>
        refine Relation.ReflTransGen.tail Relation.ReflTransGen.refl ?_
        change (Set.range (G.collarMap c b) ∩
          Set.range (G.transition.childCoreIntoParent c)).Nonempty
        exact hmeet b
    | some b, _root_.Option.some b' =>
        have h1 : Relation.ReflTransGen (fun x y => (s x ∩ s y).Nonempty) (_root_.Option.some b) none :=
          Relation.ReflTransGen.tail Relation.ReflTransGen.refl (by
            change (Set.range (G.collarMap c b) ∩
              Set.range (G.transition.childCoreIntoParent c)).Nonempty
            exact hmeet b)
        have h2 : Relation.ReflTransGen (fun x y => (s x ∩ s y).Nonempty) _root_.Option.none (_root_.Option.some b') :=
          Relation.ReflTransGen.tail Relation.ReflTransGen.refl (by
            change (Set.range (G.transition.childCoreIntoParent c) ∩
              Set.range (G.collarMap c b')).Nonempty
            exact (hmeet b').mono (Set.inter_comm _ _).subset)
        exact h1.trans h2
  have hmain : IsConnected (⋃ o, s o) := IsConnected.iUnion_of_reflTransGen hs hK
  simpa only [Set.iUnion_option, s, supportRegion] using hmain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isConnected_supportRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isConnected_supportRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isConnected_supportRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isConnected_supportRegion

noncomputable def levelSphere (G : GeometricCutoffRecord H i parameters)
    (c : ConnectedComponents (H.stage i.succ).Carrier) (b : G.ChildBoundary c) :
    C(Sphere 2, (G.Parent c).Carrier) :=
  (G.collarMap c b).comp
    ⟨fun y : Sphere 2 =>
      (y, ⟨G.comparisonLevel c b, le_rfl, (G.comparisonLevel_negative c b).le⟩),
      continuous_id.prodMk continuous_const⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere

theorem levelSphere_apply (G : GeometricCutoffRecord H i parameters)
    (c : ConnectedComponents (H.stage i.succ).Carrier) (b : G.ChildBoundary c) (y : Sphere 2) :
    levelSphere G c b y =
      G.collarMap c b (y, ⟨G.comparisonLevel c b, le_rfl,
        (G.comparisonLevel_negative c b).le⟩) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere_apply

theorem levelSphere_mem_supportRegion (G : GeometricCutoffRecord H i parameters)
    (c : ConnectedComponents (H.stage i.succ).Carrier) (b : G.ChildBoundary c) (y : Sphere 2) :
    levelSphere G c b y ∈ supportRegion G c :=
  Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_range_self _⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere_mem_supportRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere_mem_supportRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere_mem_supportRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere_mem_supportRegion

theorem pairwise_disjoint_levelSphere (G : GeometricCutoffRecord H i parameters)
    (c : ConnectedComponents (H.stage i.succ).Carrier) :
    Pairwise fun b d => Disjoint (Set.range (levelSphere G c b))
      (Set.range (levelSphere G c d)) := by
  intro b d hbd
  refine Set.disjoint_left.mpr fun z hz hz' => ?_
  obtain ⟨y, rfl⟩ := hz
  obtain ⟨y', hy'⟩ := hz'
  exact Set.disjoint_left.mp (G.collarMap_pairwise_disjoint c hbd)
    (Set.mem_range_self _)
    ⟨(y', ⟨G.comparisonLevel c d, le_rfl, (G.comparisonLevel_negative c d).le⟩), hy'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pairwise_disjoint_levelSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pairwise_disjoint_levelSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pairwise_disjoint_levelSphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pairwise_disjoint_levelSphere

theorem levelSphere_mem_range_collarMap (G : GeometricCutoffRecord H i parameters)
    (c : ConnectedComponents (H.stage i.succ).Carrier) (b : G.ChildBoundary c) (y : Sphere 2) :
    levelSphere G c b y ∈ Set.range (G.collarMap c b) :=
  Set.mem_range_self _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere_mem_range_collarMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere_mem_range_collarMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere_mem_range_collarMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.levelSphere_mem_range_collarMap


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
