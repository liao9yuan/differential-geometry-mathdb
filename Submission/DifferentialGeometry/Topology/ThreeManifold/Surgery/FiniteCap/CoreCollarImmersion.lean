import Submission.DifferentialGeometry.Topology.Manifold.SmoothLiftedCharts
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreInteriorImmersion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.IsManifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev ImmCollarE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarE3 target :: scope.openDecls } }
private abbrev ImmCollarE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarE2 target :: scope.openDecls } }
private abbrev ImmCollarS2 := Metric.sphere (0 : ImmCollarE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarS2 target :: scope.openDecls } }
private abbrev ImmCollarIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarIR target :: scope.openDecls } }
private abbrev ImmCollarIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarIC target :: scope.openDecls } }
private abbrev ImmCollarIH := ModelProd ImmCollarE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarIH target :: scope.openDecls } }
private abbrev ImmCollarH := ModelProd ImmCollarE2 ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ImmCollarH target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealImmCollarE3HAddOfNat : Fact (Module.finrank ℝ ImmCollarE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealImmCollarE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealImmCollarE3HAddOfNat target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph ImmCollarIC I ∞ (f i))

include hs in
theorem cutCore_ambientInclusion_isImmersionAt_collar (b : ι × Bool)
    (q : ImmCollarS2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :
    let : ChartedSpace ImmCollarIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    _root_.Manifold.IsImmersionAtOfComplement Unit ImmCollarIR I ∞ (Subtype.val : cutCore f → M)
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) := by
  let : Nonempty H := ⟨I.symm 0⟩
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : IsManifold (𝓡∂ 1) ∞ (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace ImmCollarIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold ImmCollarIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let κ := cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
  let qb := cuttingCollarCylinderMap (hδ b.1) b.2 q
  let ψ := coreAmbientNormalizingHomeomorph I hdim (-1) (cuttingSign b.2) (cuttingSign_sq b.2)
  let e := (chartAt ImmCollarH qb).transHomeomorph ψ
  let d := e.lift_openEmbedding (hf b.1)
  let c := cutCoreCollarHalfChart hδ f hf hdisj b q
  have he : ContMDiffOn ImmCollarIC I ∞ e e.source :=
    (coreAmbientNormalizingHomeomorph_contMDiff I hdim (-1) (cuttingSign b.2) (cuttingSign_sq b.2)).comp_contMDiffOn
      (contMDiffOn_chart (I := ImmCollarIC) (n := ∞) (x := qb))
  have he' : ContMDiffOn I ImmCollarIC ∞ e.symm e.target :=
    (contMDiffOn_chart_symm (I := ImmCollarIC) (n := ∞) (x := qb)).comp
      (coreAmbientNormalizingHomeomorph_symm_contMDiff I hdim (-1) (cuttingSign b.2) (cuttingSign_sq b.2)).contMDiffOn
      (fun _ hz => hz)
  have hd : d ∈ _root_.IsManifold.maximalAtlas I ∞ M :=
    d.mem_maximalAtlas_of_contMDiffOn
      (contMDiffOn_lift_openEmbedding ImmCollarIC I I (f b.1) (hf b.1) (hs b.1) e he)
      (contMDiffOn_lift_openEmbedding_symm ImmCollarIC I I (f b.1) (hf b.1) (hs b.1).contMDiff e he')
  have hc : c ∈ _root_.IsManifold.maximalAtlas ImmCollarIR ∞ (cutCore f) := _root_.IsManifold.subset_maximalAtlas (Or.inr ⟨⟨b, q⟩, rfl⟩)
  let L := (ContinuousLinearEquiv.prodUnique ℝ (ImmCollarE2 × EuclideanSpace ℝ (Fin 1)) Unit).trans
    (coreBoundaryAmbientLinearEquiv hdim)
  apply IsImmersionAtOfComplement.mk_of_continuousAt continuous_subtype_val.continuousAt L c d
    (cutCoreCollarHalfChart_mem hδ f hf hdisj b q) ⟨qb, mem_chart_source ImmCollarH qb, rfl⟩ hc hd
  intro z hz
  let r := (chartAt ImmCollarIH q).symm (ImmCollarIR.symm z)
  have hright : chartAt ImmCollarIH q r = ImmCollarIR.symm z :=
    (chartAt ImmCollarIH q).right_inv hz.2
  have hfirst : (chartAt (EuclideanSpace ℝ (Fin 2)) q.1 r.1) = (ImmCollarIR.symm z).1 :=
    congrArg (fun v : ImmCollarIH => v.1) hright
  have hheight : r.2.val = (ImmCollarIR.symm z).2.val 0 := by
    have hh := congrArg (fun v : ImmCollarIH => v.2.val 0) hright
    change (extChartAt (𝓡∂ 1) q.2 r.2) 0 = (ImmCollarIR.symm z).2.val 0 at hh
    rw [halfClosedInterval_extChartAt_apply] at hh
    simpa only [sub_zero] using hh
  change I (d ((c.extend ImmCollarIR).symm z).val) = L (z, 0)
  change I (d (f b.1 (cuttingCollarCylinderMap (hδ b.1) b.2 r))) = L (z, 0)
  dsimp only [d]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change I (ψ (chartAt ImmCollarH qb (cuttingCollarCylinderMap (hδ b.1) b.2 r))) = L (z, 0)
  rw [coreAmbientNormalizingHomeomorph_extend]
  change (coreAmbientLinearEquiv hdim).symm
    (chartAt (EuclideanSpace ℝ (Fin 2)) q.1 r.1,
      -1 + cuttingSign b.2 * (cuttingSign b.2 + cuttingSign b.2 * r.2.val)) = L (z, 0)
  have hsigned : -1 + cuttingSign b.2 * (cuttingSign b.2 + cuttingSign b.2 * r.2.val) = r.2.val := by
    calc
      _ = -1 + (cuttingSign b.2) ^ 2 * (1 + r.2.val) := by ring
      _ = r.2.val := by rw [cuttingSign_sq]; ring
  rw [hsigned, hfirst, hheight]
  have hzcoords : ((ImmCollarIR.symm z).1, (ImmCollarIR.symm z).2.val 0) =
      (z.1, z.2 0) :=
    congrArg (fun v : ImmCollarE2 × EuclideanSpace ℝ (Fin 1) => (v.1, v.2 0))
      (ImmCollarIR.right_inv (by rw [← ImmCollarIR.target_eq]; exact hz.1))
  rw [hzcoords]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_isImmersionAt_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_isImmersionAt_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_isImmersionAt_collar ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_isImmersionAt_collar
end DifferentialGeometry.Topology.ThreeManifold.Surgery
