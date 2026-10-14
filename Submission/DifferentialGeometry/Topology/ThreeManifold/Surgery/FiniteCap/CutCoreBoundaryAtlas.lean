import Submission.DifferentialGeometry.Topology.Manifold.HalfSpaceInteriorChart
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreComponents
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CoreE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreE3 target :: scope.openDecls } }
private abbrev CoreE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreE2 target :: scope.openDecls } }
private abbrev CoreIH := ModelProd CoreE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreIH target :: scope.openDecls } }
private abbrev CoreS2 := Metric.sphere (0 : CoreE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreS2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealCoreE3HAddOfNat : Fact (Module.finrank ℝ CoreE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealCoreE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealCoreE3HAddOfNat target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
private abbrev CoreCollar (b : ι × Bool) := CoreS2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreCollar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreCollar target :: scope.openDecls } }

private def coreInteriorCoordinateChart (x : coreInteriorDomain f) : OpenPartialHomeomorph (cutCore f) (CoreE2 × ℝ) := by
  let e : H ≃ₜ CoreE2 × ℝ := I.toHomeomorph.trans
    ((LinearEquiv.ofFinrankEq (R := ℝ) E (CoreE2 × ℝ) (by simpa using hdim)).toContinuousLinearEquiv.toHomeomorph)
  exact ((chartAt H x).transHomeomorph e).lift_openEmbedding (isOpenEmbedding_coreInteriorInclusion f)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.coreInteriorCoordinateChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreInteriorCoordinateChart target :: scope.openDecls } }

omit [T2Space M] [Finite ι] in
private theorem coreInteriorCoordinateChart_mem (x : coreInteriorDomain f) :
    coreInteriorInclusion f x ∈ (coreInteriorCoordinateChart I hdim f x).source :=
  ⟨x, mem_chart_source H x, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.coreInteriorCoordinateChart_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.coreInteriorCoordinateChart_mem target :: scope.openDecls } }

def cutCoreInteriorHalfChart (x : coreInteriorDomain f) : OpenPartialHomeomorph (cutCore f) CoreIH :=
  let e := coreInteriorCoordinateChart I hdim f x
  e.trans ((OpenPartialHomeomorph.refl CoreE2).prod
    (halfSpaceInteriorChart ((e (coreInteriorInclusion f x)).2 - 1)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart

omit [T2Space M] [Finite ι] in
theorem cutCoreInteriorHalfChart_mem (x : coreInteriorDomain f) :
    coreInteriorInclusion f x ∈ (cutCoreInteriorHalfChart I hdim f x).source := by
  refine ⟨coreInteriorCoordinateChart_mem I hdim f x, ?_⟩
  change True ∧ _
  refine ⟨trivial, ?_⟩
  change (coreInteriorCoordinateChart I hdim f x (coreInteriorInclusion f x)).2 - 1 <
    (coreInteriorCoordinateChart I hdim f x (coreInteriorInclusion f x)).2
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart_mem ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart_mem

omit [T2Space M] [Finite ι] in
theorem cutCoreInteriorHalfChart_base_height (x : coreInteriorDomain f) :
    ((cutCoreInteriorHalfChart I hdim f x (coreInteriorInclusion f x)).2).val 0 = 1 := by
  let t := (coreInteriorCoordinateChart I hdim f x (coreInteriorInclusion f x)).2
  change (halfSpaceInteriorChart (t - 1) t).val 0 = 1
  rw [halfSpaceInteriorChart_apply _ _ (by dsimp only [t]; linarith)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart_base_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart_base_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart_base_height ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart_base_height

def cutCoreCollarHalfChart (b : ι × Bool) (q : CoreCollar (precision := precision) b) :
    OpenPartialHomeomorph (cutCore f) CoreIH := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  exact (chartAt CoreIH q).lift_openEmbedding (isOpenEmbedding_cuttingCollarMap hδ f hf hdisj b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart

omit [T2Space M] [Finite ι] in
theorem cutCoreCollarHalfChart_apply (b : ι × Bool) (q r : CoreCollar (precision := precision) b) :
    let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
      halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    cutCoreCollarHalfChart hδ f hf hdisj b q
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b r) = chartAt CoreIH q r := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  dsimp only
  exact OpenPartialHomeomorph.lift_openEmbedding_apply (chartAt CoreIH q)
    (isOpenEmbedding_cuttingCollarMap hδ f hf hdisj b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_apply

omit [T2Space M] [Finite ι] in
theorem cutCoreCollarHalfChart_mem (b : ι × Bool) (q : CoreCollar (precision := precision) b) :
    cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q ∈
      (cutCoreCollarHalfChart hδ f hf hdisj b q).source := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  exact ⟨q, mem_chart_source CoreIH q, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_mem ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_mem

omit [T2Space M] [Finite ι] in
theorem cutCoreCollarHalfChart_height (b : ι × Bool) (q r : CoreCollar (precision := precision) b) :
    ((cutCoreCollarHalfChart hδ f hf hdisj b q
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b r)).2).val 0 = r.2.val := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  rw [cutCoreCollarHalfChart_apply]
  change (extChartAt (𝓡∂ 1) q.2 r.2) 0 = r.2.val
  rw [halfClosedInterval_extChartAt_apply]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_height ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_height

def cutCoreBoundaryAtlas : Set (OpenPartialHomeomorph (cutCore f) CoreIH) :=
  _root_.Set.range (cutCoreInteriorHalfChart I hdim f) ∪
    range (fun q : Σ b : ι × Bool, CoreCollar (precision := precision) b =>
      cutCoreCollarHalfChart hδ f hf hdisj q.1 q.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreBoundaryAtlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreBoundaryAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreBoundaryAtlas ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreBoundaryAtlas

theorem cutCoreBoundaryAtlas_covers (p : cutCore f) :
    ∃ e ∈ cutCoreBoundaryAtlas I hdim hδ f hf hdisj, p ∈ e.source := by
  by_cases hp : p.val ∈ interior (cutCore f)
  · let x : coreInteriorDomain f := ⟨p.val, hp⟩
    exact ⟨cutCoreInteriorHalfChart I hdim f x, Or.inl ⟨x, rfl⟩,
      cutCoreInteriorHalfChart_mem I hdim f x⟩
  · have hfront : p ∈ _root_.Set.range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
      rw [range_cuttingSphereAttachment hδ f hf hdisj]
      exact ⟨subset_closure p.property, hp⟩
    obtain ⟨⟨b, y⟩, he⟩ := hfront
    let q : CoreCollar (precision := precision) b :=
      (y, ⟨0, le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩)
    refine ⟨cutCoreCollarHalfChart hδ f hf hdisj b q, Or.inr ⟨⟨b, q⟩, rfl⟩, ?_⟩
    have hq := cutCoreCollarHalfChart_mem hδ f hf hdisj b q
    have hval : cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q = p :=
      (cuttingCollarMap_zero hδ f (fun i => (hf i).injective) hdisj b y).trans he
    exact hval ▸ hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreBoundaryAtlas_covers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreBoundaryAtlas_covers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreBoundaryAtlas_covers ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreBoundaryAtlas_covers

@[instance_reducible] def cutCoreBoundaryChartedSpace : ChartedSpace CoreIH (cutCore f) where
  atlas := cutCoreBoundaryAtlas I hdim hδ f hf hdisj
  chartAt p := Classical.choose (cutCoreBoundaryAtlas_covers I hdim hδ f hf hdisj p)
  mem_chart_source p := (Classical.choose_spec (cutCoreBoundaryAtlas_covers I hdim hδ f hf hdisj p)).2
  chart_mem_atlas p := (Classical.choose_spec (cutCoreBoundaryAtlas_covers I hdim hδ f hf hdisj p)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreBoundaryChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreBoundaryChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreBoundaryChartedSpace ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreBoundaryChartedSpace
end DifferentialGeometry.Topology.ThreeManifold.Surgery
