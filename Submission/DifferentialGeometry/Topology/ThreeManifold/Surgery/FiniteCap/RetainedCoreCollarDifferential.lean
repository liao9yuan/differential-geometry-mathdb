import Submission.DifferentialGeometry.Topology.Manifold.HalfClosedIntervalInclusion
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreCollarLocalDiffeomorph
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.SelectedCoreSmoothManifolds
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreMaps
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtype

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
private abbrev RetCollarE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.RetCollarE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.RetCollarE3 target :: scope.openDecls } }
private abbrev RetCollarE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.RetCollarE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.RetCollarE2 target :: scope.openDecls } }
private abbrev RetCollarS2 := Metric.sphere (0 : RetCollarE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.RetCollarS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.RetCollarS2 target :: scope.openDecls } }
private abbrev RetCollarIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.RetCollarIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.RetCollarIR target :: scope.openDecls } }
private abbrev RetCollarIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.RetCollarIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.RetCollarIC target :: scope.openDecls } }
private abbrev RetCollarIH := ModelProd RetCollarE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.RetCollarIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.RetCollarIH target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealRetCollarE3HAddOfNat : Fact (Module.finrank ℝ RetCollarE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealRetCollarE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealRetCollarE3HAddOfNat target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L B : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph RetCollarIC I ∞ (f i))
variable (R : Set (ConnectedComponents (cutCore f)))
variable (b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R})
variable (hB : 0 < B) (hfit : B ≤ cuttingCollarWidth (precision b.val.1))

include hs in
theorem finiteRetainedCollarCoreMap_contMDiff :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) B) := halfClosedIntervalChartedSpace hB
    let : ChartedSpace RetCollarIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    ContMDiff RetCollarIR RetCollarIR ∞ (finiteRetainedCollarCoreMap hL hδ f hf hdisj R b hfit) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) B) := halfClosedIntervalChartedSpace hB
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.val.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.val.1))
  let : ChartedSpace RetCollarIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold RetCollarIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let j : _root_.Set.Ico (0 : ℝ) B → _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.val.1)) :=
    fun q => ⟨q.val, q.property.1, q.property.2.trans_le hfit⟩
  have hj : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ j :=
    contMDiff_halfClosedInterval_inclusion hB (cuttingCollarWidth_pos (hδ b.val.1)) hfit
  have h : ContMDiff RetCollarIR RetCollarIR ∞
      (fun q : RetCollarS2 × _root_.Set.Ico (0 : ℝ) B =>
        cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b.val (q.1, j q.2)) :=
    (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b.val).contMDiff.comp
      (contMDiff_id.prodMap hj)
  exact (ContMDiff.subtypeVal_comp_iff (retainedCoreOpen I hdim hδ f hf hdisj R)
    (finiteRetainedCollarCoreMap hL hδ f hf hdisj R b hfit)).mp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap_contMDiff

include hs in
theorem finiteRetainedCollarCoreMap_mfderiv_bijective
    (q : RetCollarS2 × _root_.Set.Ico (0 : ℝ) B) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) B) := halfClosedIntervalChartedSpace hB
    let : ChartedSpace RetCollarIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    Bijective (mfderiv RetCollarIR RetCollarIR (finiteRetainedCollarCoreMap hL hδ f hf hdisj R b hfit) q) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) B) := halfClosedIntervalChartedSpace hB
  let : IsManifold (𝓡∂ 1) ∞ (_root_.Set.Ico (0 : ℝ) B) := halfClosedInterval_isManifold hB
  let hW := cuttingCollarWidth_pos (hδ b.val.1)
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.val.1))) := halfClosedIntervalChartedSpace hW
  let : IsManifold (𝓡∂ 1) ∞ (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.val.1))) := halfClosedInterval_isManifold hW
  let : ChartedSpace RetCollarIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold RetCollarIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ChartedSpace RetCollarIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let j : _root_.Set.Ico (0 : ℝ) B → _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.val.1)) :=
    fun p => ⟨p.val, p.property.1, p.property.2.trans_le hfit⟩
  let J := Prod.map (id : RetCollarS2 → RetCollarS2) j
  let κ := cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b.val
  let F := finiteRetainedCollarCoreMap hL hδ f hf hdisj R b hfit
  have hj : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ j := contMDiff_halfClosedInterval_inclusion hB hW hfit
  have hJ : ContMDiff RetCollarIR RetCollarIR ∞ J := contMDiff_id.prodMap hj
  have hκ : IsLocalDiffeomorph RetCollarIR RetCollarIR ∞ κ := cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b.val
  have hF : ContMDiff RetCollarIR RetCollarIR ∞ F := finiteRetainedCollarCoreMap_contMDiff I hdim hL hδ f hf hdisj hs R b hB hfit
  have hJbij : _root_.Function.Bijective (mfderiv RetCollarIR RetCollarIR J q) := by
    change _root_.Function.Bijective (mfderiv RetCollarIR RetCollarIR (Prod.map (id : RetCollarS2 → RetCollarS2) j) q)
    rw [mfderiv_prodMap mdifferentiableAt_id (hj.mdifferentiableAt (by simp)), mfderiv_id]
    exact Function.bijective_id.prodMap (mfderiv_halfClosedInterval_inclusion_bijective hB hW hfit q.2)
  have hc := mfderiv_comp q (hκ.contMDiff.mdifferentiableAt (by simp)) (hJ.mdifferentiableAt (by simp))
  have hv := mfderiv_comp q
    ((contMDiff_subtype_val (I := RetCollarIR) (U := retainedCoreOpen I hdim hδ f hf hdisj R) (n := ∞)).mdifferentiableAt (by simp))
    (hF.mdifferentiableAt (by simp))
  have hval : mfderiv RetCollarIR RetCollarIR (Subtype.val : retainedCore f R → cutCore f) (F q) =
      ContinuousLinearMap.id ℝ (RetCollarE2 × EuclideanSpace ℝ (Fin 1)) :=
    DifferentialGeometry.mfderiv_subtype_val (I := RetCollarIR) (retainedCoreOpen I hdim hδ f hf hdisj R) (F q)
  have hv' : mfderiv RetCollarIR RetCollarIR (κ ∘ J) q = mfderiv RetCollarIR RetCollarIR F q :=
    hv.trans (congrArg (fun A : (RetCollarE2 × EuclideanSpace ℝ (Fin 1)) →L[ℝ]
      (RetCollarE2 × EuclideanSpace ℝ (Fin 1)) => A.comp (mfderiv RetCollarIR RetCollarIR F q)) hval)
  have he : mfderiv RetCollarIR RetCollarIR F q =
      (mfderiv RetCollarIR RetCollarIR κ (J q)).comp (mfderiv RetCollarIR RetCollarIR J q) := by
    exact hv'.symm.trans hc
  change _root_.Function.Bijective (mfderiv RetCollarIR RetCollarIR F q)
  rw [he]
  exact ((hκ.mfderivToContinuousLinearEquiv (by simp) (J q)).bijective).comp hJbij

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap_mfderiv_bijective
end DifferentialGeometry.Topology.ThreeManifold.Surgery
