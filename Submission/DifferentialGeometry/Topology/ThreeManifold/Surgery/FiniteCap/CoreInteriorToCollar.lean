import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreCollarToInterior
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCorePositiveCollar
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreInteriorCollar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev ToCollarE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ToCollarE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ToCollarE3 target :: scope.openDecls } }
private abbrev ToCollarE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ToCollarE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ToCollarE2 target :: scope.openDecls } }
private abbrev ToCollarS2 := Metric.sphere (0 : ToCollarE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ToCollarS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ToCollarS2 target :: scope.openDecls } }
private abbrev ToCollarIH := ModelProd ToCollarE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ToCollarIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ToCollarIH target :: scope.openDecls } }
private abbrev ToCollarIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ToCollarIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ToCollarIR target :: scope.openDecls } }
private abbrev ToCollarIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ToCollarIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ToCollarIC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealToCollarE3HAddOfNat : Fact (Module.finrank ℝ ToCollarE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealToCollarE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealToCollarE3HAddOfNat target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))

theorem cutCoreInteriorHalfChart_to_collar_contMDiff
    (hs : ∀ i, IsLocalDiffeomorph ToCollarIC I ∞ (f i)) (b : ι × Bool)
    (q : ToCollarS2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)))
    (x : coreInteriorDomain f) :
    ContMDiffOn ToCollarIR ToCollarIR ∞
      ((cutCoreInteriorHalfChart I hdim f x).symm.trans (cutCoreCollarHalfChart hδ f hf hdisj b q))
      ((cutCoreInteriorHalfChart I hdim f x).symm.trans (cutCoreCollarHalfChart hδ f hf hdisj b q)).source := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : IsManifold (𝓡∂ 1) ∞ (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  let c := cutCoreInteriorHalfChart I hdim f x
  let e := cutCoreCollarHalfChart hδ f hf hdisj b q
  let R : ToCollarIH → M := fun z => (c.symm z).val
  let F := f b.1 ∘ cuttingPositiveCylinderMap (hδ b.1) b.2
  let α := positiveCuttingCollarInclusion (cuttingCollarWidth (precision b.1))
  have hF : IsLocalDiffeomorph ToCollarIC I ∞ F := cuttingPositiveAmbient_isLocalDiffeomorph I hδ f hs b
  have hinj : _root_.Function.Injective F := (hf b.1).injective.comp (cuttingPositiveCylinderMap_injective (hδ b.1) b.2)
  have hα : ContMDiff ToCollarIC ToCollarIR ∞ α :=
    positiveCuttingCollarInclusion_contMDiff (cuttingCollarWidth_pos (hδ b.1))
  have hparam (z : ToCollarIH) (hz : z ∈ (c.symm.trans e).source) :
      ∃ u : positiveCuttingCylinder (cuttingCollarWidth (precision b.1)),
        α u ∈ (chartAt ToCollarIH q).source ∧
        e (c.symm z) = chartAt ToCollarIH q (α u) ∧ F u = R z := by
    obtain ⟨r, hr, he⟩ := hz.2
    change cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b r = c.symm z at he
    have hI : (c.symm z).val ∈ interior (cutCore f) := by
      dsimp only [c]
      rw [cutCoreInteriorHalfChart_symm_original]
      exact ((chartAt H x).symm ((coreInteriorModelDiffeomorph I hdim).symm
        (z.1, z.2.val 0 + ((coreInteriorModelDiffeomorph I hdim (chartAt H x x)).2 - 1)))).property
    have hpos : 0 < r.2.val := by
      apply (cuttingCollar_interior_iff hδ f hf hdisj b r).mp
      exact (congrArg Subtype.val he).symm ▸ hI
    let u : positiveCuttingCylinder (cuttingCollarWidth (precision b.1)) :=
      ⟨(r.1, r.2.val), hpos, r.2.property.2⟩
    have hur : α u = r := rfl
    refine ⟨u, hur.symm ▸ hr, ?_, ?_⟩
    · rw [← he]
      exact (cutCoreCollarHalfChart_apply hδ f hf hdisj b q r).trans (congrArg (chartAt ToCollarIH q) hur.symm)
    · change (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b (α u)).val = (c.symm z).val
      rw [hur]
      exact congrArg Subtype.val he
  intro z hz
  obtain ⟨u, hu, he, hFu⟩ := hparam z hz
  have hR : ContMDiffAt ToCollarIR I ∞ R z :=
    (cutCoreInteriorHalfChart_symm_ambient_contMDiffOn I hdim f x).contMDiffAt
      (c.open_target.mem_nhds hz.1)
  have hlocal : ContMDiffAt I ToCollarIC ∞ (hF u).localInverse (R z) := by
    rw [← hFu]
    exact (hF u).localInverse_contMDiffAt
  have hmem : R z ∈ (hF u).localInverse.source := by
    rw [← hFu]
    exact (hF u).localInverse_mem_source
  have hInv : (hF u).localInverse (R z) = u :=
    hinj (((hF u).localInverse_right_inv hmem).trans hFu.symm)
  have hchart : ContMDiffAt ToCollarIR ToCollarIR ∞ (chartAt ToCollarIH q)
      (α ((hF u).localInverse (R z))) := by
    rw [hInv]
    exact (contMDiffOn_chart (I := ToCollarIR) (n := ∞) (x := q)).contMDiffAt
      ((chartAt ToCollarIH q).open_source.mem_nhds hu)
  let G : ToCollarIH → ToCollarIH := fun y => chartAt ToCollarIH q (α ((hF u).localInverse (R y)))
  have hG : ContMDiffAt ToCollarIR ToCollarIR ∞ G z :=
    hchart.comp z (hα.contMDiffAt.comp z (hlocal.comp z hR))
  have hn : ∀ᶠ y in 𝓝 z, R y ∈ (hF u).localInverse.source :=
    hR.continuousAt.preimage_mem_nhds ((hF u).localInverse_open_source.mem_nhds hmem)
  have heq : (fun y => e (c.symm y)) =ᶠ[𝓝 z] G := by
    filter_upwards [(c.symm.trans e).open_source.mem_nhds hz, hn] with y hy hny
    obtain ⟨v, _, hev, hFv⟩ := hparam y hy
    have hiv : (hF u).localInverse (R y) = v :=
      hinj (((hF u).localInverse_right_inv hny).trans hFv.symm)
    exact hev.trans (congrArg (fun t => chartAt ToCollarIH q (α t)) hiv.symm)
  exact (hG.congr_of_eventuallyEq heq).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart_to_collar_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart_to_collar_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart_to_collar_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreInteriorHalfChart_to_collar_contMDiff
end DifferentialGeometry.Topology.ThreeManifold.Surgery
