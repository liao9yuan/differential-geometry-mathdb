import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.PositiveCuttingCoordinates
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapRestrictedSmooth
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtype

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev OverlapE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.OverlapE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.OverlapE3 target :: scope.openDecls } }
private abbrev OverlapIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.OverlapIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.OverlapIC target :: scope.openDecls } }
private theorem annulus_subset_ball (L r : ℝ) : positiveCuttingAnnulus L r ≤ finiteCapRestrictedBall L r :=
  fun _ hx => hx.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.annulus_subset_ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.annulus_subset_ball target :: scope.openDecls } }
private def annulusInclusion (L r : ℝ) : positiveCuttingAnnulus L r → finiteCapRestrictedBall L r :=
  Opens.inclusion (annulus_subset_ball L r)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.annulusInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.annulusInclusion target :: scope.openDecls } }
private theorem annulusInclusion_local (L r : ℝ) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (annulusInclusion L r) := by
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (contMDiff_inclusion (annulus_subset_ball L r)) _ rfl
  intro x
  rw [mfderiv_opens_incl]
  exact fun _ _ he => he

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.annulusInclusion_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.annulusInclusion_local target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph OverlapIC I ∞ (f i))
variable (b : ι × Bool) (r : ℝ) (hfit : r ≤ cuttingCollarWidth (precision b.1))
local notation "OverlapQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "OverlapPatch" => finiteCapRestrictedNeighborhood hL hδ f hf hdisj b r

def finiteCapPositiveMap :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    positiveCuttingCylinder r → OverlapPatch := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact (finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit).symm ∘
    annulusInclusion L r ∘ positiveCuttingDiffeomorph hL r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap

theorem contMDiff_finiteCapPositiveMap :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff OverlapIC (𝓡 3) ∞ (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit) := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact (finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit).symm.contMDiff.comp
    ((contMDiff_inclusion (annulus_subset_ball L r)).comp (positiveCuttingDiffeomorph hL r).contMDiff)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteCapPositiveMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteCapPositiveMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteCapPositiveMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteCapPositiveMap

theorem injective_finiteCapPositiveMap :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Injective (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit) := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  have hj : _root_.Function.Injective (annulusInclusion L r) := fun _ _ he =>
    Subtype.ext (congrArg (fun x : finiteCapRestrictedBall L r => x.val) he)
  exact (finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit).symm.injective.comp
    (hj.comp (positiveCuttingDiffeomorph hL r).injective)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteCapPositiveMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteCapPositiveMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteCapPositiveMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteCapPositiveMap

theorem isLocalDiffeomorph_finiteCapPositiveMap :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsLocalDiffeomorph OverlapIC (𝓡 3) ∞ (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit) := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let P := finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit
  let D := positiveCuttingDiffeomorph hL r
  dsimp only
  intro q
  exact ((D.isLocalDiffeomorph q).comp (𝓡 3) (finiteCapRestrictedBall L r)
    (annulusInclusion_local L r (D q))).comp (𝓡 3) OverlapPatch
      (P.symm.isLocalDiffeomorph (annulusInclusion L r (D q)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_finiteCapPositiveMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_finiteCapPositiveMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_finiteCapPositiveMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isLocalDiffeomorph_finiteCapPositiveMap

theorem finiteCapPositiveMap_mfderiv_surjective (q : positiveCuttingCylinder r) :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Surjective (mfderiv OverlapIC (𝓡 3) (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit) q) := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact ((isLocalDiffeomorph_finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit).mfderivToContinuousLinearEquiv (by simp) q).surjective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap_mfderiv_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap_mfderiv_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap_mfderiv_surjective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap_mfderiv_surjective

theorem finiteCapPositiveMap_original (q : positiveCuttingCylinder r) :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit q).val =
      finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
          (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.trans_le hfit⟩)) := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact finiteCapOpenChart_symm_collar hL hδ f hf hdisj b
    (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.trans_le hfit⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap_original then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap_original"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap_original ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap_original

theorem finiteCapPositiveMap_mem_old (q : positiveCuttingCylinder r) :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit q).val ∈
      finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  rw [finiteCapPositiveMap_original]
  exact (finiteCoreInterior_collar_iff hL hδ f hf hdisj b _).mpr q.property.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap_mem_old then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap_mem_old"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap_mem_old ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapPositiveMap_mem_old

theorem range_finiteCapPositiveMap :
    let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    _root_.Set.range (finiteCapPositiveMap I hdim hL hδ f hf hdisj hs b r hfit) =
      {q : OverlapPatch | q.val ∈ finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj} := by
  let : ChartedSpace OverlapE3 OverlapQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let P := finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit
  let D := positiveCuttingDiffeomorph hL r
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact finiteCapPositiveMap_mem_old I hdim hL hδ f hf hdisj hs b r hfit p
  · intro hq
    have hh : finiteCapOpenChart hL hδ f hf hdisj b q.val ∈
        finiteCapOpenChart hL hδ f hf hdisj b ''
          ((finiteCapOpenChart hL hδ f hf hdisj b).source ∩
            finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj) :=
      ⟨q.val, ⟨q.property.1, hq⟩, rfl⟩
    rw [finiteCapOpenChart_interior_overlap_image] at hh
    let x : positiveCuttingAnnulus L r := ⟨(P q).val, hh.1, (P q).property⟩
    refine ⟨D.symm x, ?_⟩
    apply P.injective
    change P (P.symm (annulusInclusion L r (D (D.symm x)))) = P q
    exact (P.apply_symm_apply _).trans
      (Subtype.ext (congrArg (fun y : positiveCuttingAnnulus L r => y.val) (D.apply_symm_apply x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_finiteCapPositiveMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.range_finiteCapPositiveMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_finiteCapPositiveMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.range_finiteCapPositiveMap
end DifferentialGeometry.Topology.ThreeManifold.Surgery
