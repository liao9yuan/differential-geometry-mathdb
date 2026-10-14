import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreCappedCollar
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreAmbientCoordinates
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreInteriorSmooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.IsManifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CappedInteriorE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedInteriorE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedInteriorE3 target :: scope.openDecls } }
private abbrev CappedInteriorE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedInteriorE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedInteriorE2 target :: scope.openDecls } }
private abbrev CappedInteriorIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedInteriorIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedInteriorIR target :: scope.openDecls } }
private abbrev CappedInteriorIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedInteriorIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedInteriorIC target :: scope.openDecls } }
private abbrev CappedInteriorIH := ModelProd CappedInteriorE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedInteriorIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedInteriorIH target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph CappedInteriorIC I ∞ (f i))
local notation "CappedInteriorQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

include hs in
theorem finiteCoreInclusion_isImmersionAt_interior (x : coreInteriorDomain f) :
    let : ChartedSpace CappedInteriorIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : ChartedSpace CappedInteriorE3 CappedInteriorQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    _root_.Manifold.IsImmersionAtOfComplement Unit CappedInteriorIR (𝓡 3) ∞
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
      (coreInteriorInclusion f x) := by
  let : ChartedSpace CappedInteriorIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold CappedInteriorIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ChartedSpace CappedInteriorE3 CappedInteriorQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CappedInteriorQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let old := finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj
  let a := (coreInteriorModelDiffeomorph I hdim (chartAt H x x)).2 - 1
  let ψ := coreAmbientNormalizingHomeomorph I hdim a 1 (by norm_num)
  let ψ₀ := coreAmbientNormalizingHomeomorph I hdim 0 1 (by norm_num)
  let A := modelThreeDiffeomorph I hdim
  let Alinear := (LinearEquiv.ofFinrankEq (R := ℝ) E CappedInteriorE3 (by simpa using hdim)).toContinuousLinearEquiv
  let e := (chartAt H x).transHomeomorph ((ψ.symm.trans ψ₀).trans A.toHomeomorph)
  let hi := isOpenEmbedding_finiteCoreInteriorMap hL hδ f hf hdisj
  let d := e.lift_openEmbedding hi
  let c := cutCoreInteriorHalfChart I hdim f x
  have ho : IsLocalDiffeomorph I (𝓡 3) ∞ old := isLocalDiffeomorph_finiteCoreInteriorMap I hdim hL hδ f hf hdisj hs
  have hn : ContMDiff I I ∞ (ψ₀ ∘ ψ.symm) :=
    (coreAmbientNormalizingHomeomorph_contMDiff I hdim 0 1 (by norm_num)).comp
      (coreAmbientNormalizingHomeomorph_symm_contMDiff I hdim a 1 (by norm_num))
  have hn' : ContMDiff I I ∞ (ψ ∘ ψ₀.symm) :=
    (coreAmbientNormalizingHomeomorph_contMDiff I hdim a 1 (by norm_num)).comp
      (coreAmbientNormalizingHomeomorph_symm_contMDiff I hdim 0 1 (by norm_num))
  have he : ContMDiffOn I (𝓡 3) ∞ e e.source :=
    (A.contMDiff.comp hn).comp_contMDiffOn (contMDiffOn_chart (I := I) (n := ∞) (x := x))
  have he' : ContMDiffOn (𝓡 3) I ∞ e.symm e.target :=
    (contMDiffOn_chart_symm (I := I) (n := ∞) (x := x)).comp
      (hn'.comp A.symm.contMDiff).contMDiffOn (fun _ hz => hz)
  have hd : d ∈ _root_.IsManifold.maximalAtlas (𝓡 3) ∞ CappedInteriorQ :=
    d.mem_maximalAtlas_of_contMDiffOn
      (contMDiffOn_lift_openEmbedding I (𝓡 3) (𝓡 3) old hi ho e he)
      (contMDiffOn_lift_openEmbedding_symm I (𝓡 3) (𝓡 3) old hi ho.contMDiff e he')
  have hc : c ∈ _root_.IsManifold.maximalAtlas CappedInteriorIR ∞ (cutCore f) := _root_.IsManifold.subset_maximalAtlas (Or.inl ⟨x, rfl⟩)
  let Lnormal := (ContinuousLinearEquiv.prodUnique ℝ (CappedInteriorE2 × EuclideanSpace ℝ (Fin 1)) Unit).trans
    ((coreBoundaryAmbientLinearEquiv hdim).trans Alinear)
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (isClosedEmbedding_finiteCoreInclusion hL hδ f hf hdisj).continuous.continuousAt
    Lnormal c d (cutCoreInteriorHalfChart_mem I hdim f x)
    ⟨x, mem_chart_source H x, rfl⟩ hc hd
  intro z hz
  have hzold := hz.2
  rw [cutCoreInteriorHalfChart_target_original] at hzold
  have hchart := (chartAt H x).right_inv hzold.2
  change d (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj (c.symm (CappedInteriorIR.symm z))) = Lnormal (z, 0)
  dsimp only [c]
  rw [cutCoreInteriorHalfChart_symm_original]
  change d (old ((chartAt H x).symm ((coreInteriorModelDiffeomorph I hdim).symm
    ((CappedInteriorIR.symm z).1, (CappedInteriorIR.symm z).2.val 0 + a)))) = Lnormal (z, 0)
  dsimp only [d]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change A (ψ₀ (ψ.symm (chartAt H x ((chartAt H x).symm ((coreInteriorModelDiffeomorph I hdim).symm
    ((CappedInteriorIR.symm z).1, (CappedInteriorIR.symm z).2.val 0 + a)))))) = Lnormal (z, 0)
  change chartAt H x ((chartAt H x).symm ((coreInteriorModelDiffeomorph I hdim).symm
    ((CappedInteriorIR.symm z).1, (CappedInteriorIR.symm z).2.val 0 + a))) =
      (coreInteriorModelDiffeomorph I hdim).symm
        ((CappedInteriorIR.symm z).1, (CappedInteriorIR.symm z).2.val 0 + a) at hchart
  rw [hchart]
  have hψ : ψ.symm ((coreInteriorModelDiffeomorph I hdim).symm
      ((CappedInteriorIR.symm z).1, (CappedInteriorIR.symm z).2.val 0 + a)) =
        ((CappedInteriorIR.symm z).1, (CappedInteriorIR.symm z).2.val 0) := by
    apply ψ.injective
    rw [ψ.apply_symm_apply]
    change (coreInteriorModelDiffeomorph I hdim).symm
      ((CappedInteriorIR.symm z).1, (CappedInteriorIR.symm z).2.val 0 + a) =
        (coreInteriorModelDiffeomorph I hdim).symm
          ((CappedInteriorIR.symm z).1, a + 1 * (CappedInteriorIR.symm z).2.val 0)
    simp only [one_mul, add_comm]
  rw [hψ]
  change Alinear (I (ψ₀ ((CappedInteriorIR.symm z).1, (CappedInteriorIR.symm z).2.val 0))) = Lnormal (z, 0)
  rw [coreAmbientNormalizingHomeomorph_extend]
  simp only [one_mul, zero_add]
  have hzcoords : ((CappedInteriorIR.symm z).1, (CappedInteriorIR.symm z).2.val 0) =
      (z.1, z.2 0) :=
    congrArg (fun v : CappedInteriorE2 × EuclideanSpace ℝ (Fin 1) => (v.1, v.2 0))
      (CappedInteriorIR.right_inv (by rw [← CappedInteriorIR.target_eq]; exact hz.1))
  rw [hzcoords]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_isImmersionAt_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_isImmersionAt_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_isImmersionAt_interior ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_isImmersionAt_interior
end DifferentialGeometry.Topology.ThreeManifold.Surgery
