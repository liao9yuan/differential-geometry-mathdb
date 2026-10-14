import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedFiniteCapping
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapDecomposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  {ι : Type} [Fintype ι] {δ : ι → ℝ} {L : ℝ}
  (hL : 0 < L) (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
  (f : ∀ i : ι, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (R : Set (ConnectedComponents (cutCore f)))

local notation "Q" => FiniteCapQuotient hL hδ f
  (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instLocallyPathConnectedSpace_differentialGeometry : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instLocallyPathConnectedSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instLocallyPathConnectedSpace_differentialGeometry target :: scope.openDecls } }
local notation "Ret" => finiteCapRetained hL hδ f hf hdisj R
local notation "Disc" => finiteCapDiscarded hL hδ f hf hdisj R
local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj

noncomputable def CutCapTopology.ofBufferedFiniteCaps
    (hnontrivial : Nonempty ι ∨ Nonempty (DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f Rᶜ)) :
    CutCapTopology M Ret Disc Q where
  tubes := T
  capping := Capping.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj
  presentation := by
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q := finiteCapChartedSpace ThreeModel (by simp) hL hδ f hf hdisj
    exact (finiteCapSelectedDiffeomorph ThreeModel (by simp) hL hδ f hf hdisj R).symm.toHomeomorph
  nontrivial := hnontrivial.imp id ((finiteCapRetained_nonempty_iff_core hL hδ f hf hdisj Rᶜ).mpr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps

theorem CutCapTopology.ofBufferedFiniteCaps_tubes
    (hnontrivial : Nonempty ι ∨ Nonempty (DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f Rᶜ)) :
    (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).tubes = T := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_tubes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_tubes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_tubes ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_tubes

theorem CutCapTopology.ofBufferedFiniteCaps_presentation
    (hnontrivial : Nonempty ι ∨ Nonempty (DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f Rᶜ)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q := finiteCapChartedSpace ThreeModel (by simp) hL hδ f hf hdisj
    (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).presentation =
      (finiteCapSelectedDiffeomorph ThreeModel (by simp) hL hδ f hf hdisj R).symm.toHomeomorph := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_presentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_presentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_presentation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_presentation

theorem CutCapTopology.ofBufferedFiniteCaps_retainedCore
    (hnontrivial : Nonempty ι ∨ Nonempty (DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f Rᶜ)) :
    (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).retainedCore =
      (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj) ⁻¹' DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f R := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q := finiteCapChartedSpace ThreeModel (by simp) hL hδ f hf hdisj
  ext x
  change (∃ q : Ret,
      (finiteCapSelectedDiffeomorph ThreeModel (by simp) hL hδ f hf hdisj R).symm
        (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
          (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj x)) = Sum.inl q) ↔
    bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj x ∈ DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f R
  constructor
  · rintro ⟨q, hq⟩
    have hh := congrArg (finiteCapSelectedDiffeomorph ThreeModel (by simp) hL hδ f hf hdisj R) hq
    rw [Diffeomorph.apply_symm_apply, finiteCapSelectedDiffeomorph_inl] at hh
    have hm : finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj x) ∈ Ret := hh ▸ q.property
    exact hm
  · intro hx
    exact ⟨⟨_, hx⟩, finiteCapSelectedDiffeomorph_symm_retained ThreeModel (by simp)
      hL hδ f hf hdisj R
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj x)) hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_retainedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_retainedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_retainedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_retainedCore


theorem CutCapTopology.ofBufferedFiniteCaps_retainedBoundary_iff
    (hnontrivial : Nonempty ι ∨ Nonempty (DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f Rᶜ))
    (b : ι × Bool) :
    (∀ y : Sphere 2, (TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj).coreBoundarySphere b y ∈
      (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).retainedCore) ↔
      cuttingSphereComponent hδ f hf hdisj b ∈ R := by
  constructor
  · intro hb
    have hh := hb spherePoint
    rw [CutCapTopology.ofBufferedFiniteCaps_retainedCore] at hh
    change bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj
      ((TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj).coreBoundarySphere b spherePoint) ∈
      DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f R at hh
    erw [bufferedCutCoreHomeomorph_boundary hδ hδ1 f hf hdisj b spherePoint] at hh
    exact (cuttingSphere_mem_retainedCore_iff hδ f hf hdisj R b spherePoint).mp hh
  · intro hb y
    rw [CutCapTopology.ofBufferedFiniteCaps_retainedCore]
    change bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj
      ((TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj).coreBoundarySphere b y) ∈
      DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore f R
    erw [bufferedCutCoreHomeomorph_boundary hδ hδ1 f hf hdisj b y]
    exact (cuttingSphere_mem_retainedCore_iff hδ f hf hdisj R b y).mpr hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_retainedBoundary_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_retainedBoundary_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_retainedBoundary_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.ofBufferedFiniteCaps_retainedBoundary_iff

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
