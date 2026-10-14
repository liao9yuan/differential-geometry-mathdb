import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapTransitionSkeleton
import Submission.DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSmoothEmbedding
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreIntrinsicBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section TubeSystemSlots

variable {M : Type u} [TopologicalSpace M]

@[instance_reducible]
def TubeSystem.coreChartedSpace (T : TubeSystem M)
    [ChartedSpace EuclideanHalfSpaceProdModel T.core] :
    ChartedSpace (EuclideanHalfSpace 3) T.core :=
  euclideanHalfSpaceProdChartedSpace T.core

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreChartedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.coreChartedSpace

theorem TubeSystem.isManifold_core_of_euclideanHalfSpaceProd (T : TubeSystem M)
    [ChartedSpace EuclideanHalfSpaceProdModel T.core]
    [IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ T.core] :
    letI := T.coreChartedSpace
    IsManifold (𝓡∂ 3) ∞ T.core :=
  euclideanHalfSpaceProd_isManifold T.core

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isManifold_core_of_euclideanHalfSpaceProd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isManifold_core_of_euclideanHalfSpaceProd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isManifold_core_of_euclideanHalfSpaceProd ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isManifold_core_of_euclideanHalfSpaceProd

theorem TubeSystem.isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd (T : TubeSystem M)
    [ChartedSpace EuclideanHalfSpaceProdModel T.core]
    [IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ T.core] [ChartedSpace ThreeSpace M]
    (h : _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ (Subtype.val : T.core → M)) :
    letI := T.coreChartedSpace
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : T.core → M) :=
  DifferentialGeometry.Manifold.isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd

theorem TubeSystem.boundary_eq_iUnion_coreBoundarySphere_of_euclideanHalfSpaceProd (T : TubeSystem M)
    [ChartedSpace EuclideanHalfSpaceProdModel T.core]
    (h : ((𝓡 2).prod (𝓡∂ 1)).boundary T.core =
      ⋃ b : T.Boundary, Set.range (T.coreBoundarySphere b)) :
    letI := T.coreChartedSpace
    (𝓡∂ 3).boundary T.core = ⋃ b : T.Boundary, Set.range (T.coreBoundarySphere b) :=
  (euclideanHalfSpaceProd_boundary T.core).trans h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundary_eq_iUnion_coreBoundarySphere_of_euclideanHalfSpaceProd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundary_eq_iUnion_coreBoundarySphere_of_euclideanHalfSpaceProd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundary_eq_iUnion_coreBoundarySphere_of_euclideanHalfSpaceProd ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.boundary_eq_iUnion_coreBoundarySphere_of_euclideanHalfSpaceProd

theorem TubeSystem.iUnion_range_coreBoundarySphere_eq_empty (T : TubeSystem M) [IsEmpty T.Index] :
    (⋃ b : T.Boundary, Set.range (T.coreBoundarySphere b)) = ∅ := by
  apply Set.iUnion_eq_empty.mpr
  intro b
  exact isEmptyElim b.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.iUnion_range_coreBoundarySphere_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.iUnion_range_coreBoundarySphere_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.iUnion_range_coreBoundarySphere_eq_empty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.iUnion_range_coreBoundarySphere_eq_empty

end TubeSystemSlots

section CappingSlot

variable {M : Type u} [TopologicalSpace M] {N : Type u} [TopologicalSpace N]

theorem Capping.isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd {T : TubeSystem M}
    (K : Capping T N) [ChartedSpace EuclideanHalfSpaceProdModel T.core]
    [IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ T.core] [ChartedSpace ThreeSpace N]
    (h : _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ K.coreInclusion) :
    letI := euclideanHalfSpaceProdChartedSpace T.core
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ K.coreInclusion :=
  DifferentialGeometry.Manifold.isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd
    K.coreInclusion h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd

end CappingSlot

section CutCoreWorld

open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
variable {ι : Type u} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ ThreeSpace = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))

theorem cutCore_isManifold_of_euclideanHalfSpaceProd
    (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i)) :
    letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
      cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj
    IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
  cutCore_isManifold ThreeModel hdim hδ f hf hdisj hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_isManifold_of_euclideanHalfSpaceProd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_isManifold_of_euclideanHalfSpaceProd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_isManifold_of_euclideanHalfSpaceProd ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_isManifold_of_euclideanHalfSpaceProd

theorem cutCore_isManifold_euclideanHalfSpace
    (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i)) :
    letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
      cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj
    letI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
      cutCore_isManifold ThreeModel hdim hδ f hf hdisj hs
    letI := euclideanHalfSpaceProdChartedSpace (cutCore f)
    IsManifold (𝓡∂ 3) ∞ (cutCore f) :=
  letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
    cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj
  letI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
    cutCore_isManifold ThreeModel hdim hδ f hf hdisj hs
  euclideanHalfSpaceProd_isManifold (cutCore f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_isManifold_euclideanHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_isManifold_euclideanHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_isManifold_euclideanHalfSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_isManifold_euclideanHalfSpace

theorem cutCore_isSmoothEmbedding_subtypeVal_euclideanHalfSpace
    (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i)) :
    letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
      cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj
    letI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
      cutCore_isManifold ThreeModel hdim hδ f hf hdisj hs
    letI := euclideanHalfSpaceProdChartedSpace (cutCore f)
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (Subtype.val : cutCore f → M) :=
  @DifferentialGeometry.Manifold.isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd M _ _
    (cutCore f)
    (cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj)
    (cutCore_isManifold ThreeModel hdim hδ f hf hdisj hs)
    (cutCore_ambientInclusion_isSmoothEmbedding ThreeModel hdim hδ f hf hdisj hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_isSmoothEmbedding_subtypeVal_euclideanHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_isSmoothEmbedding_subtypeVal_euclideanHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_isSmoothEmbedding_subtypeVal_euclideanHalfSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_isSmoothEmbedding_subtypeVal_euclideanHalfSpace

theorem cutCore_boundary_eq_iUnion_cuttingSphereAttachment_euclideanHalfSpace
    (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i)) :
    letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
      cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj
    letI := euclideanHalfSpaceProdChartedSpace (cutCore f)
    (𝓡∂ 3).boundary (cutCore f) =
      ⋃ b : ι × Bool, Set.range (fun y : Sphere 2 =>
        cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩) :=
  letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
    cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj
  letI := euclideanHalfSpaceProdChartedSpace (cutCore f)
  (euclideanHalfSpaceProd_boundary (cutCore f)).trans
    ((cutCore_boundary_eq_cuttingSpheres ThreeModel hdim hδ f hf hdisj hs).trans (by
      ext x
      constructor
      · rintro ⟨⟨b, y⟩, rfl⟩
        exact Set.mem_iUnion.mpr ⟨b, Set.mem_range_self y⟩
      · intro hx
        obtain ⟨b, y, hy⟩ := Set.mem_iUnion.mp hx
        exact ⟨⟨b, y⟩, hy⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_boundary_eq_iUnion_cuttingSphereAttachment_euclideanHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_boundary_eq_iUnion_cuttingSphereAttachment_euclideanHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_boundary_eq_iUnion_cuttingSphereAttachment_euclideanHalfSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cutCore_boundary_eq_iUnion_cuttingSphereAttachment_euclideanHalfSpace

end CutCoreWorld

section StandardNeck

private def sphereTwoPoint : Sphere 2 :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereTwoPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereTwoPoint target :: scope.openDecls } }

theorem standardNeckTubeSystem_iUnion_range_coreBoundarySphere_nonempty :
    (⋃ b : standardNeckTubeSystem.Boundary,
      Set.range (standardNeckTubeSystem.coreBoundarySphere b)).Nonempty :=
  ⟨standardNeckTubeSystem.coreBoundarySphere (PUnit.unit, _root_.Bool.false) sphereTwoPoint,
    Set.mem_iUnion.mpr ⟨(PUnit.unit, _root_.Bool.false), Set.mem_range_self sphereTwoPoint⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_iUnion_range_coreBoundarySphere_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_iUnion_range_coreBoundarySphere_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_iUnion_range_coreBoundarySphere_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_iUnion_range_coreBoundarySphere_nonempty

end StandardNeck

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
