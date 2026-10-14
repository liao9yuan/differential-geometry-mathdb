import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapOpenChart
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreInteriorChart
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]

def modelThreeHomeomorph (hdim : Module.finrank ℝ E = 3) : H ≃ₜ E3 :=
  I.toHomeomorph.trans ((LinearEquiv.ofFinrankEq (R := ℝ) E E3 (by simpa using hdim)).toContinuousLinearEquiv.toHomeomorph)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeHomeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.modelThreeHomeomorph

variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCoreThreeChart (x : coreInteriorDomain f) : OpenPartialHomeomorph Q E3 :=
  (finiteCoreOpenChart (H := H) hL hδ f hf hdisj x).transHomeomorph (modelThreeHomeomorph I hdim)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart

theorem finiteCoreThreeChart_source (x : coreInteriorDomain f) :
    (finiteCoreThreeChart I hdim hL hδ f hf hdisj x).source =
      (finiteCoreOpenChart (H := H) hL hδ f hf hdisj x).source := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart_source ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart_source

theorem finiteCoreThreeChart_apply (x p : coreInteriorDomain f) :
    finiteCoreThreeChart I hdim hL hδ f hf hdisj x
      (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj p) =
        modelThreeHomeomorph I hdim (chartAt H x.val p.val) := by
  change modelThreeHomeomorph I hdim
    (finiteCoreOpenChart (H := H) hL hδ f hf hdisj x
      (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj p)) = _
  rw [finiteCoreOpenChart_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart_apply

def finiteCapAtlas : Set (OpenPartialHomeomorph Q E3) :=
  _root_.Set.range (finiteCoreThreeChart I hdim hL hδ f hf hdisj) ∪ _root_.Set.range (finiteCapOpenChart hL hδ f hf hdisj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAtlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAtlas ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAtlas

theorem finiteCapAtlas_covers (q : Q) :
    ∃ e ∈ finiteCapAtlas I hdim hL hδ f hf hdisj, q ∈ e.source := by
  have hq := eq_univ_iff_forall.mp (finiteCapOpenChart_source_cover hL hδ f hf hdisj) q
  rcases hq with hq | hq
  · rw [← finiteCoreOpenChart_source_cover (H := H) hL hδ f hf hdisj] at hq
    obtain ⟨x, hx⟩ := mem_iUnion.mp hq
    exact ⟨finiteCoreThreeChart I hdim hL hδ f hf hdisj x, Or.inl ⟨x, rfl⟩, hx⟩
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hq
    exact ⟨finiteCapOpenChart hL hδ f hf hdisj b, Or.inr ⟨b, rfl⟩, hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAtlas_covers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAtlas_covers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAtlas_covers ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAtlas_covers

@[instance_reducible] def finiteCapChartedSpace : ChartedSpace E3 Q where
  atlas := finiteCapAtlas I hdim hL hδ f hf hdisj
  chartAt q := Classical.choose (finiteCapAtlas_covers I hdim hL hδ f hf hdisj q)
  mem_chart_source q := (Classical.choose_spec (finiteCapAtlas_covers I hdim hL hδ f hf hdisj q)).2
  chart_mem_atlas q := (Classical.choose_spec (finiteCapAtlas_covers I hdim hL hδ f hf hdisj q)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapChartedSpace ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapChartedSpace

theorem finiteCapChartedSpace_atlas :
    @ChartedSpace.atlas E3 _ Q _ (finiteCapChartedSpace I hdim hL hδ f hf hdisj) =
      finiteCapAtlas I hdim hL hδ f hf hdisj := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapChartedSpace_atlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapChartedSpace_atlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapChartedSpace_atlas ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapChartedSpace_atlas

theorem finiteCapQuotient_topological_properties [CompactSpace M] :
    let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    CompactSpace Q ∧ T2Space Q ∧ SecondCountableTopology Q ∧
      LocallyCompactSpace Q ∧ LocallyPathConnectedSpace Q := by
  let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
  exact ⟨inferInstance, finiteCapQuotient_t2Space hL hδ f hf hdisj,
    ChartedSpace.secondCountable_of_sigmaCompact E3 Q,
    ChartedSpace.locallyCompactSpace E3 Q, ChartedSpace.locallyPathConnectedSpace E3 Q⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_topological_properties then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_topological_properties"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_topological_properties ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_topological_properties
end DifferentialGeometry.Topology.ThreeManifold.Surgery
