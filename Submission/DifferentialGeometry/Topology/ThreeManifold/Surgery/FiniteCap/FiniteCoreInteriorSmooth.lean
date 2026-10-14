import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSmoothManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.IsManifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev InteriorE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.InteriorE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.InteriorE3 target :: scope.openDecls } }
private abbrev InteriorIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.InteriorIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.InteriorIC target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph InteriorIC I ∞ (f i))
local notation "InteriorQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "oldMap" => finiteCoreInteriorMap hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCoreInteriorOpens : _root_.TopologicalSpace.Opens InteriorQ :=
  ⟨finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj,
    isOpen_finiteCoreInterior hL hδ f hf hdisj⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorOpens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorOpens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorOpens ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorOpens

def finiteCoreInteriorHomeomorph : coreInteriorDomain f ≃ₜ finiteCoreInteriorOpens hL hδ f hf hdisj := by
  let V := finiteCoreInteriorOpens hL hδ f hf hdisj
  have hmem (p : coreInteriorDomain f) : oldMap p ∈ V :=
    ⟨⟨p.val, interior_subset p.property⟩, p.property, rfl⟩
  let F : coreInteriorDomain f → V := fun p => ⟨oldMap p, hmem p⟩
  have hF : _root_.Topology.IsEmbedding F :=
    (isOpenEmbedding_finiteCoreInteriorMap hL hδ f hf hdisj).isEmbedding.codRestrict V hmem
  have hsurj : _root_.Function.Surjective F := by
    intro q
    obtain ⟨p, hp, he⟩ := q.property
    exact ⟨⟨p.val, hp⟩, Subtype.ext he⟩
  exact (Equiv.ofBijective F ⟨hF.injective, hsurj⟩).toHomeomorphOfIsInducing hF.isInducing

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorHomeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorHomeomorph

theorem finiteCoreInteriorHomeomorph_apply (p : coreInteriorDomain f) :
    (finiteCoreInteriorHomeomorph hL hδ f hf hdisj p).val = oldMap p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorHomeomorph_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorHomeomorph_apply

include hs in
theorem contMDiff_finiteCoreInteriorMap :
    let : ChartedSpace InteriorE3 InteriorQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff I (𝓡 3) ∞ oldMap := by
  let : ChartedSpace InteriorE3 InteriorQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ InteriorQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  dsimp only
  intro p
  let A := modelThreeDiffeomorph I hdim
  let c := finiteCoreThreeChart I hdim hL hδ f hf hdisj p
  have hc : c ∈ _root_.IsManifold.maximalAtlas (𝓡 3) ∞ InteriorQ :=
    StructureGroupoid.subset_maximalAtlas _ (show c ∈ @ChartedSpace.atlas InteriorE3 _ InteriorQ _
      (finiteCapChartedSpace I hdim hL hδ f hf hdisj) from Or.inl ⟨p, rfl⟩)
  have heq (r : coreInteriorDomain f) : c (oldMap r) = A (chartAt H p r) :=
    finiteCoreThreeChart_apply I hdim hL hδ f hf hdisj p r
  have hsource (r : coreInteriorDomain f) (hr : r ∈ (chartAt H p).source) : oldMap r ∈ c.source := by
    rw [finiteCoreThreeChart_source, finiteCoreOpenChart_source]
    exact ⟨r, hr, rfl⟩
  have hpin := hsource p (mem_chart_source H p)
  have hi := contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hpin)
  rw [heq] at hi
  have hg := hi.comp p (A.contMDiffAt.comp p (contMDiffAt_of_mem_maximalAtlas
    (_root_.IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) p) (mem_chart_source H p)))
  apply hg.congr_of_eventuallyEq
  filter_upwards [(chartAt H p).open_source.mem_nhds (mem_chart_source H p)] with r hr
  have he := c.left_inv (hsource r hr)
  rw [heq] at he
  exact he.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteCoreInteriorMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteCoreInteriorMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteCoreInteriorMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteCoreInteriorMap

def finiteCoreInteriorDiffeomorph :
    let : ChartedSpace InteriorE3 InteriorQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Diffeomorph I (𝓡 3) (coreInteriorDomain f) (finiteCoreInteriorOpens hL hδ f hf hdisj) ∞ := by
  let : ChartedSpace InteriorE3 InteriorQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ InteriorQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let V := finiteCoreInteriorOpens hL hδ f hf hdisj
  let e := finiteCoreInteriorHomeomorph hL hδ f hf hdisj
  refine { toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · exact (ContMDiff.subtypeVal_comp_iff V e).mp (contMDiff_finiteCoreInteriorMap I hdim hL hδ f hf hdisj hs)
  · intro q
    let p := e.symm q
    let A := modelThreeDiffeomorph I hdim
    let c := finiteCoreThreeChart I hdim hL hδ f hf hdisj p
    have hc : c ∈ _root_.IsManifold.maximalAtlas (𝓡 3) ∞ InteriorQ :=
      StructureGroupoid.subset_maximalAtlas _ (show c ∈ @ChartedSpace.atlas InteriorE3 _ InteriorQ _
        (finiteCapChartedSpace I hdim hL hδ f hf hdisj) from Or.inl ⟨p, rfl⟩)
    have heq (r : coreInteriorDomain f) : c (oldMap r) = A (chartAt H p r) :=
      finiteCoreThreeChart_apply I hdim hL hδ f hf hdisj p r
    have hp : oldMap p = q.val := congrArg Subtype.val (e.apply_symm_apply q)
    have hpin : oldMap p ∈ c.source := by
      rw [finiteCoreThreeChart_source, finiteCoreOpenChart_source]
      exact ⟨p, mem_chart_source H p, rfl⟩
    have hqsource : q.val ∈ c.source := hp ▸ hpin
    have hcoord : A.symm (c q.val) = chartAt H p p := by
      rw [← hp, heq, A.symm_apply_apply]
    have hi := contMDiffAt_symm_of_mem_maximalAtlas (_root_.IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) p)
      (mem_chart_target H p)
    rw [← hcoord] at hi
    have hg := hi.comp q (A.symm.contMDiffAt.comp q
      ((contMDiffAt_of_mem_maximalAtlas hc hqsource).comp q
        (contMDiff_subtype_val (U := V)).contMDiffAt))
    apply hg.congr_of_eventuallyEq
    have hnear : ∀ᶠ z : V in 𝓝 q, z.val ∈ c.source :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hqsource)
    filter_upwards [hnear] with z hz
    rw [finiteCoreThreeChart_source, finiteCoreOpenChart_source] at hz
    obtain ⟨r, hr, he⟩ := hz
    change e.symm z = (chartAt H p).symm (A.symm (c z.val))
    rw [← he, heq, A.symm_apply_apply, (chartAt H p).left_inv hr]
    have her : e r = z := Subtype.ext he
    exact (congrArg e.symm her).symm.trans (e.symm_apply_apply r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorDiffeomorph

theorem finiteCoreInteriorDiffeomorph_apply (p : coreInteriorDomain f) :
    (finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs p).val = oldMap p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorDiffeomorph_apply

theorem finiteCoreInteriorDiffeomorph_symm_original
    (q : finiteCoreInteriorOpens hL hδ f hf hdisj) :
    let : ChartedSpace InteriorE3 InteriorQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    oldMap ((finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs).symm q) = q.val := by
  let : ChartedSpace InteriorE3 InteriorQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact congrArg Subtype.val ((finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs).apply_symm_apply q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorDiffeomorph_symm_original then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorDiffeomorph_symm_original"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorDiffeomorph_symm_original ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorDiffeomorph_symm_original
include hs in
theorem finiteCoreInteriorMap_mfderiv_injective (p : coreInteriorDomain f) :
    let : ChartedSpace InteriorE3 InteriorQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Injective (mfderiv I (𝓡 3) oldMap p) := by
  let : ChartedSpace InteriorE3 InteriorQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let V := finiteCoreInteriorOpens hL hδ f hf hdisj
  let F := finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs
  have hd : mfderiv I (𝓡 3) oldMap p = mfderiv I (𝓡 3) F p := by
    change mfderiv I (𝓡 3) ((Subtype.val : V → InteriorQ) ∘ F) p = _
    rw [mfderiv_comp _
      ((contMDiff_subtype_val (U := V) (n := ∞)).mdifferentiable (by simp) (F p))
      (F.contMDiff.mdifferentiable (by simp) p), DifferentialGeometry.mfderiv_subtype_val]
    rfl
  dsimp only
  rw [hd]
  exact (F.mfderivToContinuousLinearEquiv (by simp) p).injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorMap_mfderiv_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorMap_mfderiv_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorMap_mfderiv_injective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInteriorMap_mfderiv_injective

include hs in
theorem isLocalDiffeomorph_finiteCoreInteriorMap :
    let : ChartedSpace InteriorE3 InteriorQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsLocalDiffeomorph I (𝓡 3) ∞ oldMap := by
  let : ChartedSpace InteriorE3 InteriorQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ InteriorQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  exact DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv oldMap
    (contMDiff_finiteCoreInteriorMap I hdim hL hδ f hf hdisj hs)
    (finiteCoreInteriorMap_mfderiv_injective I hdim hL hδ f hf hdisj hs)
    (by simpa using hdim)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_finiteCoreInteriorMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_finiteCoreInteriorMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_finiteCoreInteriorMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_finiteCoreInteriorMap
end DifferentialGeometry.Topology.ThreeManifold.Surgery
