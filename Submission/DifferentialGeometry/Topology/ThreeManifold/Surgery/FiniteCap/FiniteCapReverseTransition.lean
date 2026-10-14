import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.ModelThreeSmooth
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSmoothOverlap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev ReverseE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ReverseE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ReverseE3 target :: scope.openDecls } }
private abbrev ReverseIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.ReverseIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.ReverseIC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealReverseE3HAddOfNat : Fact (Module.finrank ℝ ReverseE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealReverseE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealReverseE3HAddOfNat target :: scope.openDecls } }
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
variable [IsManifold I ∞ M] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))

theorem contDiffOn_coreThree_to_finiteCap
    (hs : ∀ i, IsLocalDiffeomorph ReverseIC I ∞ (f i)) (b : ι × Bool) (p : coreInteriorDomain f) :
    ContDiffOn ℝ ∞
      ((finiteCoreThreeChart I hdim hL hδ f hf hdisj p).symm.trans
        (finiteCapOpenChart hL hδ f hf hdisj b))
      ((finiteCoreThreeChart I hdim hL hδ f hf hdisj p).symm.trans
        (finiteCapOpenChart hL hδ f hf hdisj b)).source := by
  let e := finiteCapOpenChart hL hδ f hf hdisj b
  let c := finiteCoreThreeChart I hdim hL hδ f hf hdisj p
  let A := modelThreeDiffeomorph I hdim
  let old := finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj
  let r : ReverseE3 → coreInteriorDomain f := fun y => (chartAt H p).symm (A.symm y)
  let R : ReverseE3 → M := fun y => (r y).val
  let F := f b.1 ∘ cuttingAnnulusCylinderMap hL (hδ b.1) b.2
  have hF : IsLocalDiffeomorph (𝓡 3) I ∞ F :=
    finiteCapAnnulusAmbient_isLocalDiffeomorph hL hδ f hs b
  have hinj : _root_.Function.Injective F := (hf b.1).injective.comp (cuttingAnnulusCylinderMap_injective hL (hδ b.1) b.2)
  have hinjOld := (isOpenEmbedding_finiteCoreInteriorMap hL hδ f hf hdisj).injective
  have hparam (y : ReverseE3) (hy : y ∈ (c.symm.trans e).source) :
      ∃ a : cuttingAnnulus L (precision b.1), a.val = e (c.symm y) ∧ F a = R y := by
    change y ∈ c.target ∧ c.symm y ∈ e.source at hy
    have hI : c.symm y ∈ finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj := by
      rw [← range_finiteCoreInteriorMap]
      exact ⟨r y, rfl⟩
    have hA : e (c.symm y) ∈ cuttingAnnulus L (precision b.1) := by
      have him : e (c.symm y) ∈ e '' (e.source ∩ finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj) :=
        ⟨c.symm y, ⟨hy.2, hI⟩, rfl⟩
      rw [finiteCapOpenChart_interior_overlap_image hL hδ f hf hdisj b] at him
      exact him
    let a : cuttingAnnulus L (precision b.1) := ⟨e (c.symm y), hA⟩
    refine ⟨a, rfl, ?_⟩
    have he : old (finiteCapAnnulusOldMap hL hδ f hf hdisj b a) = old (r y) :=
      (finiteCapOpenChart_symm_annulus hL hδ f hf hdisj b a).symm.trans (e.left_inv hy.2)
    exact congrArg Subtype.val (hinjOld he)
  intro y hy
  obtain ⟨a, ha, hRa⟩ := hparam y hy
  have ht : A.symm y ∈ (chartAt H p).target := hy.1
  have hr : ContMDiffAt (𝓡 3) I ∞ r y := by
    exact ((contMDiffOn_chart_symm (I := I) (n := ∞)).contMDiffAt
      ((chartAt H p).open_target.mem_nhds ht)).comp y A.symm.contMDiff.contMDiffAt
  have hR : ContMDiffAt (𝓡 3) I ∞ R y :=
    (contMDiff_subtype_val (I := I) (U := coreInteriorDomain f)).contMDiffAt.comp y hr
  have hl : ContMDiffAt I (𝓡 3) ∞ (hF a).localInverse (R y) := by
    rw [← hRa]
    exact (hF a).localInverse_contMDiffAt
  let G : ReverseE3 → ReverseE3 := fun z => ((hF a).localInverse (R z)).val
  have hG : ContMDiffAt (𝓡 3) (𝓡 3) ∞ G y :=
    (contMDiff_subtype_val (I := 𝓡 3) (U := cuttingAnnulus L (precision b.1))).contMDiffAt.comp y (hl.comp y hR)
  have hn : ∀ᶠ z in 𝓝 y, R z ∈ (hF a).localInverse.source := by
    apply hR.continuousAt.preimage_mem_nhds
    rw [← hRa]
    exact (hF a).localInverse_open_source.mem_nhds (hF a).localInverse_mem_source
  have heq : (fun z => e (c.symm z)) =ᶠ[𝓝 y] G := by
    filter_upwards [(c.symm.trans e).open_source.mem_nhds hy, hn] with z hz hnz
    obtain ⟨az, haz, hFaz⟩ := hparam z hz
    have he := hinj (((hF a).localInverse_right_inv hnz).trans hFaz.symm)
    exact haz.symm.trans (congrArg Subtype.val he).symm
  have hT : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun z => e (c.symm z)) y := hG.congr_of_eventuallyEq heq
  exact hT.contDiffAt.contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.contDiffOn_coreThree_to_finiteCap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.contDiffOn_coreThree_to_finiteCap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.contDiffOn_coreThree_to_finiteCap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.contDiffOn_coreThree_to_finiteCap
end DifferentialGeometry.Topology.ThreeManifold.Surgery
