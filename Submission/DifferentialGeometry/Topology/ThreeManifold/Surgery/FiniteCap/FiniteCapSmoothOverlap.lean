import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingAnnulusCoordinates
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapAtlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
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
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealOverlapE3HAddOfNat : Fact (Module.finrank ℝ OverlapE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealOverlapE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealOverlapE3HAddOfNat target :: scope.openDecls } }
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))

def finiteCapAnnulusOldMap (b : ι × Bool) : cuttingAnnulus L (precision b.1) → coreInteriorDomain f :=
  fun x => ⟨f b.1 (cuttingAnnulusCylinderMap hL (hδ b.1) b.2 x),
    (cuttingCollar_interior_iff hδ f hf hdisj b (cuttingAnnulusCollar hL x)).mpr
      (by rw [cuttingAnnulusCollar_radius]; exact sub_pos.mpr x.property.1)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAnnulusOldMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAnnulusOldMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAnnulusOldMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAnnulusOldMap

theorem finiteCapAnnulusOldMap_val (b : ι × Bool) (x : cuttingAnnulus L (precision b.1)) :
    (finiteCapAnnulusOldMap hL hδ f hf hdisj b x).val =
      f b.1 (cuttingAnnulusCylinderMap hL (hδ b.1) b.2 x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAnnulusOldMap_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAnnulusOldMap_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAnnulusOldMap_val ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAnnulusOldMap_val

theorem finiteCapOpenChart_symm_annulus (b : ι × Bool) (x : cuttingAnnulus L (precision b.1)) :
    (finiteCapOpenChart hL hδ f hf hdisj b).symm x.val =
      finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj
        (finiteCapAnnulusOldMap hL hδ f hf hdisj b x) := by
  have he := finiteCapOpenChart_symm_collar hL hδ f hf hdisj b (cuttingAnnulusCollar hL x)
  rw [cuttingAnnulusCollar_radial] at he
  exact he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_symm_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_symm_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_symm_annulus ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_symm_annulus

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H M]

theorem contMDiff_finiteCapAnnulusOldMap
    (hs : ∀ i, ContMDiff OverlapIC I ∞ (f i)) (b : ι × Bool) :
    ContMDiff (𝓡 3) I ∞ (finiteCapAnnulusOldMap hL hδ f hf hdisj b) := by
  apply (ContMDiff.subtypeVal_comp_iff (coreInteriorDomain f)
    (finiteCapAnnulusOldMap hL hδ f hf hdisj b)).mp
  exact (hs b.1).comp (contMDiff_cuttingAnnulusCylinderMap hL (hδ b.1) b.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteCapAnnulusOldMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteCapAnnulusOldMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteCapAnnulusOldMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_finiteCapAnnulusOldMap

omit hf hdisj [Finite ι] [T2Space M] in
theorem finiteCapAnnulusAmbient_isLocalDiffeomorph
    (hs : ∀ i, IsLocalDiffeomorph OverlapIC I ∞ (f i)) (b : ι × Bool) :
    IsLocalDiffeomorph (𝓡 3) I ∞ (f b.1 ∘ cuttingAnnulusCylinderMap hL (hδ b.1) b.2) := by
  intro x
  exact (cuttingAnnulusCylinderMap_isLocalDiffeomorph hL (hδ b.1) b.2 x).comp I M
    (hs b.1 (cuttingAnnulusCylinderMap hL (hδ b.1) b.2 x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAnnulusAmbient_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAnnulusAmbient_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAnnulusAmbient_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapAnnulusAmbient_isLocalDiffeomorph

theorem finiteCoreOpenChart_annulus_transition (p : coreInteriorDomain f) (b : ι × Bool)
    (x : cuttingAnnulus L (precision b.1)) :
    finiteCoreOpenChart (H := H) hL hδ f hf hdisj p
      ((finiteCapOpenChart hL hδ f hf hdisj b).symm x.val) =
        chartAt H p.val (f b.1 (cuttingAnnulusCylinderMap hL (hδ b.1) b.2 x)) := by
  rw [finiteCapOpenChart_symm_annulus, finiteCoreOpenChart_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_annulus_transition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_annulus_transition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_annulus_transition ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreOpenChart_annulus_transition

variable [FiniteDimensional ℝ E] [I.Boundaryless]

theorem finiteCoreThreeChart_annulus_transition (hdim : Module.finrank ℝ E = 3)
    (p : coreInteriorDomain f) (b : ι × Bool) (x : cuttingAnnulus L (precision b.1)) :
    finiteCoreThreeChart I hdim hL hδ f hf hdisj p
      ((finiteCapOpenChart hL hδ f hf hdisj b).symm x.val) =
        modelThreeHomeomorph I hdim
          (chartAt H p.val (f b.1 (cuttingAnnulusCylinderMap hL (hδ b.1) b.2 x))) := by
  rw [finiteCapOpenChart_symm_annulus, finiteCoreThreeChart_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart_annulus_transition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart_annulus_transition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart_annulus_transition ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreThreeChart_annulus_transition
end DifferentialGeometry.Topology.ThreeManifold.Surgery
