import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreBoundaryAtlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CollarE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CollarE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CollarE3 target :: scope.openDecls } }
private abbrev CollarE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CollarE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CollarE2 target :: scope.openDecls } }
private abbrev CollarS2 := Metric.sphere (0 : CollarE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CollarS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CollarS2 target :: scope.openDecls } }
private abbrev CollarIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CollarIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CollarIR target :: scope.openDecls } }
private abbrev CollarIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CollarIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CollarIC target :: scope.openDecls } }
private abbrev CollarIH := ModelProd CollarE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CollarIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CollarIH target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealCollarE3HAddOfNat : Fact (Module.finrank ℝ CollarE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealCollarE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealCollarE3HAddOfNat target :: scope.openDecls } }

theorem cuttingCollarCylinderMap_contMDiff {δ : ℝ} (hδ : 0 < δ) (b : Bool) :
    let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ)) :=
      halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
    ContMDiff CollarIR CollarIC ∞ (cuttingCollarCylinderMap hδ b) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ)) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
  let : IsManifold (𝓡∂ 1) ∞ (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ)) :=
    halfClosedInterval_isManifold (cuttingCollarWidth_pos hδ)
  have ht : ContMDiff CollarIR 𝓘(ℝ) ∞
      (fun q : CollarS2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ) => q.2.val) :=
    (isSmoothEmbedding_halfClosedInterval_inclusion (cuttingCollarWidth_pos hδ)).contMDiff.comp contMDiff_snd
  have hr : ContMDiff CollarIR CollarIC ∞
      (fun q : CollarS2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ) =>
        (q.1, cuttingSign b + cuttingSign b * q.2.val)) :=
    contMDiff_fst.prodMk (contMDiff_const.add (contMDiff_const.mul ht))
  dsimp only
  intro q
  exact codRestr_contMDiffAt (I := CollarIR) (J := CollarIC) (V := bufferedCylinder δ)
    (fun p => (cuttingCollarCylinderMap hδ b p).property) hr.contMDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarCylinderMap_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarCylinderMap_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarCylinderMap_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarCylinderMap_contMDiff

theorem cutCoreCollarHalfChart_contMDiff_transition
    {ι M : Type*} [TopologicalSpace M] {precision : ι → ℝ}
    (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j))))
    (b c : ι × Bool)
    (q : CollarS2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)))
    (r : CollarS2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision c.1))) :
    ContMDiffOn CollarIR CollarIR ∞
      ((cutCoreCollarHalfChart hδ f hf hdisj b q).symm.trans (cutCoreCollarHalfChart hδ f hf hdisj c r))
      ((cutCoreCollarHalfChart hδ f hf hdisj b q).symm.trans (cutCoreCollarHalfChart hδ f hf hdisj c r)).source := by
  by_cases hbc : b = c
  · subst c
    let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
      halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    let : IsManifold (𝓡∂ 1) ∞ (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
      halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    simp only [cutCoreCollarHalfChart, OpenPartialHomeomorph.lift_openEmbedding_trans]
    exact (contMDiffOn_chart (I := CollarIR) (x := r)).comp' (contMDiffOn_chart_symm (I := CollarIR) (x := q))
  · intro x hx
    have hb := (cutCoreCollarHalfChart hδ f hf hdisj b q).map_target hx.1
    obtain ⟨u, _, hu⟩ := hb
    obtain ⟨v, _, hv⟩ := hx.2
    exact (disjoint_left.mp (pairwise_disjoint_cuttingCollars hδ f (fun i => (hf i).injective) hdisj hbc)
      ⟨u, hu⟩ ⟨v, hv⟩).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_contMDiff_transition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_contMDiff_transition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_contMDiff_transition ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_contMDiff_transition

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type*} {precision : ι → ℝ} (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hi : ∀ i, Injective (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, ContMDiff CollarIC I ∞ (f i))

include hs in
theorem cuttingCollarAmbient_contMDiff (b : ι × Bool) :
    let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
      halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    ContMDiff CollarIR I ∞ (Subtype.val ∘ cuttingCollarMap hδ f hi hdisj b) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  exact (hs b.1).comp (cuttingCollarCylinderMap_contMDiff (hδ b.1) b.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarAmbient_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarAmbient_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarAmbient_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarAmbient_contMDiff

include hs in
theorem cutCoreCollarHalfChart_symm_ambient_contMDiffOn
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)) (b : ι × Bool)
    (q : CollarS2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :
    ContMDiffOn CollarIR I ∞
      (fun z : CollarIH => ((cutCoreCollarHalfChart hδ f hf hdisj b q).symm z).val)
      (cutCoreCollarHalfChart hδ f hf hdisj b q).target := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : IsManifold (𝓡∂ 1) ∞ (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  exact (cuttingCollarAmbient_contMDiff I hδ f (fun i => (hf i).injective) hdisj hs b).comp_contMDiffOn
    (contMDiffOn_chart_symm (I := CollarIR) (x := q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_symm_ambient_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_symm_ambient_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_symm_ambient_contMDiffOn ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreCollarHalfChart_symm_ambient_contMDiffOn
end DifferentialGeometry.Topology.ThreeManifold.Surgery
