import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCap
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Function
open scoped _root_.unitInterval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

instance instCompactSpaceThreeBall : CompactSpace ThreeBall :=
  isCompact_iff_compactSpace.mp (_root_.ProperSpace.isCompact_closedBall (0 : ThreeSpace) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instCompactSpaceThreeBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instCompactSpaceThreeBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instCompactSpaceThreeBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instCompactSpaceThreeBall

instance instContractibleSpaceThreeBall : ContractibleSpace ThreeBall :=
  (convex_closedBall (0 : ThreeSpace) 1).contractibleSpace ⟨0, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instContractibleSpaceThreeBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instContractibleSpaceThreeBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instContractibleSpaceThreeBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instContractibleSpaceThreeBall

instance instSimplyConnectedSpaceThreeBall : SimplyConnectedSpace ThreeBall :=
  SimplyConnectedSpace.ofContractible ThreeBall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSimplyConnectedSpaceThreeBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSimplyConnectedSpaceThreeBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSimplyConnectedSpaceThreeBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSimplyConnectedSpaceThreeBall

noncomputable def sphereNorth : Sphere 2 :=
  ⟨EuclideanSpace.single 0 1, by simp [Sphere, PiLp.norm_single]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereNorth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereNorth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereNorth ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereNorth

noncomputable def threeBallNorth : ThreeBall := sphereToThreeBall sphereNorth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallNorth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallNorth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallNorth ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallNorth

noncomputable def ballSegmentMap (y : ThreeBall) : C(I, ThreeBall) where
  toFun t :=
    ⟨(1 - (t : ℝ)) • y.1 + (t : ℝ) • threeBallNorth.1, by
      have h1 : 0 ≤ 1 - (t : ℝ) := by linarith [t.2.2]
      have h2 : 0 ≤ (t : ℝ) := t.2.1
      have h3 : (1 - (t : ℝ)) + (t : ℝ) = 1 := by ring
      exact convex_closedBall (0 : ThreeSpace) 1 y.2 threeBallNorth.2 h1 h2 h3⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballSegmentMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballSegmentMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballSegmentMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballSegmentMap

noncomputable def segmentPath (y : ThreeBall) : Path y threeBallNorth :=
  Path.mk (ballSegmentMap y) (by apply Subtype.ext; simp [ballSegmentMap])
    (by apply Subtype.ext; simp [ballSegmentMap])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.segmentPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.segmentPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.segmentPath ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.segmentPath

namespace Capping

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {T : TubeSystem M}
    (K : Capping T N)

def capInterior (b : T.Boundary) : Set N := Set.range (K.cap b) \ Set.range K.coreInclusion

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior

theorem mem_capInterior_iff {b : T.Boundary} {x : N} :
    x ∈ K.capInterior b ↔ x ∈ Set.range (K.cap b) ∧ x ∉ Set.range K.coreInclusion :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.mem_capInterior_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.mem_capInterior_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.mem_capInterior_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.mem_capInterior_iff

theorem capInterior_subset_range (b : T.Boundary) : K.capInterior b ⊆ Set.range (K.cap b) :=
  Set.sdiff_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior_subset_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior_subset_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior_subset_range ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior_subset_range

theorem capInterior_disjoint_coreInclusion (b : T.Boundary) :
    Disjoint (K.capInterior b) (Set.range K.coreInclusion) := by
  rw [Set.disjoint_left]
  exact fun _ hx hxc => hx.2 hxc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior_disjoint_coreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior_disjoint_coreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior_disjoint_coreInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior_disjoint_coreInclusion

theorem pairwise_disjoint_capInterior : Pairwise (Disjoint on K.capInterior) := by
  intro b b' hbb'
  rw [Function.onFun, Set.disjoint_left]
  exact fun _ hx hy => Set.disjoint_left.mp (K.cap_disjoint hbb') hx.1 hy.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.pairwise_disjoint_capInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.pairwise_disjoint_capInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.pairwise_disjoint_capInterior ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.pairwise_disjoint_capInterior

theorem iUnion_capInterior_disjoint_coreInclusion :
    Disjoint (⋃ b, K.capInterior b) (Set.range K.coreInclusion) := by
  rw [Set.disjoint_left]
  intro x hx hxc
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
  exact (Set.disjoint_left.mp (K.capInterior_disjoint_coreInclusion b)) hb hxc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.iUnion_capInterior_disjoint_coreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.iUnion_capInterior_disjoint_coreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.iUnion_capInterior_disjoint_coreInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.iUnion_capInterior_disjoint_coreInclusion

theorem range_coreInclusion_union_iUnion_capInterior :
    Set.range K.coreInclusion ∪ (⋃ b, K.capInterior b) = univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  have hx : x ∈ Set.range K.coreInclusion ∪ ⋃ b, Set.range (K.cap b) := by
    rw [K.exhaustive]
    exact Set.mem_univ x
  rcases hx with hx | hx
  · exact Or.inl hx
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    by_cases hcore : x ∈ Set.range K.coreInclusion
    · exact Or.inl hcore
    · exact Or.inr (Set.mem_iUnion.mpr ⟨b, hb, hcore⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.range_coreInclusion_union_iUnion_capInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.range_coreInclusion_union_iUnion_capInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.range_coreInclusion_union_iUnion_capInterior ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.range_coreInclusion_union_iUnion_capInterior

theorem capInterior_subset_compl_coreInclusion (b : T.Boundary) :
    K.capInterior b ⊆ (Set.range K.coreInclusion)ᶜ :=
  fun _ hx hxc => hx.2 hxc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior_subset_compl_coreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior_subset_compl_coreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior_subset_compl_coreInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.capInterior_subset_compl_coreInclusion

theorem exists_path_cap_to_coreInclusion (b : T.Boundary) (y : ThreeBall) :
    ∃ (p : N) (_ : p ∈ Set.range K.coreInclusion) (γ : Path (K.cap b y) p),
      ∀ t, (γ t : N) ∈ Set.range (K.cap b) := by
  refine ⟨K.coreInclusion (T.coreBoundarySphere b (K.attaching b sphereNorth)),
    ⟨_, rfl⟩, ?_, ?_⟩
  · exact ((segmentPath y).map (K.cap b).continuous).cast rfl
      (K.boundary_eq b sphereNorth).symm
  · intro t
    exact ⟨segmentPath y t, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.exists_path_cap_to_coreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.exists_path_cap_to_coreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.exists_path_cap_to_coreInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.exists_path_cap_to_coreInclusion

theorem isSimplyConnected_range_cap (b : T.Boundary) :
    IsSimplyConnected (Set.range (K.cap b)) :=
  ((K.capEmbedding b).toHomeomorph.toHomotopyEquiv).symm.simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.isSimplyConnected_range_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.isSimplyConnected_range_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.isSimplyConnected_range_cap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.isSimplyConnected_range_cap

theorem isSimplyConnected_image_componentCarrier (D : ConnectedComponents T.core)
    (hD : SimplyConnectedSpace (ComponentCarrier D)) :
    IsSimplyConnected (K.coreInclusion '' {x : T.core | ConnectedComponents.mk x = D}) :=
  (K.coreEmbedding.isSimplyConnected_image).mpr hD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.isSimplyConnected_image_componentCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.isSimplyConnected_image_componentCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.isSimplyConnected_image_componentCarrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.isSimplyConnected_image_componentCarrier

end Capping

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
