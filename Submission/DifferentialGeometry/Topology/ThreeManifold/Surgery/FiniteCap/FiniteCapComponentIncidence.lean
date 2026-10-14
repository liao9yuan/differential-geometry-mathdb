import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapConnectedFibers
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapComponentSelection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "IncidenceQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCapConnectedComponentsEquiv : ConnectedComponents IncidenceQ ≃ ConnectedComponents (cutCore f) := by
  let : LocallyPathConnectedSpace (cutCore f) := cutCore_locallyPathConnectedSpace hδ f hf hdisj
  let F := (continuous_finiteCapComponentLabel hL hδ f hf hdisj).connectedComponentsLift
  apply Equiv.ofBijective F
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
    change finiteCapComponentLabel hL hδ f hf hdisj x = finiteCapComponentLabel hL hδ f hf hdisj y at hab
    apply ConnectedComponents.coe_eq_coe.mpr
    rw [connectedComponent_eq_finiteCapComponentLabel_fiber hL hδ f hf hdisj x,
      connectedComponent_eq_finiteCapComponentLabel_fiber hL hδ f hf hdisj y, hab]
  · intro c
    obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
    exact ⟨ConnectedComponents.mk (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p), rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapConnectedComponentsEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapConnectedComponentsEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapConnectedComponentsEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapConnectedComponentsEquiv

theorem finiteCapConnectedComponentsEquiv_apply (q : IncidenceQ) :
    finiteCapConnectedComponentsEquiv hL hδ f hf hdisj (ConnectedComponents.mk q) =
      finiteCapComponentLabel hL hδ f hf hdisj q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapConnectedComponentsEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapConnectedComponentsEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapConnectedComponentsEquiv_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapConnectedComponentsEquiv_apply

theorem finiteCapConnectedComponentsEquiv_symm_core (p : cutCore f) :
    (finiteCapConnectedComponentsEquiv hL hδ f hf hdisj).symm (ConnectedComponents.mk p) =
      ConnectedComponents.mk (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p) := by
  apply (finiteCapConnectedComponentsEquiv hL hδ f hf hdisj).injective
  rw [Equiv.apply_symm_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapConnectedComponentsEquiv_symm_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapConnectedComponentsEquiv_symm_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapConnectedComponentsEquiv_symm_core ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapConnectedComponentsEquiv_symm_core

theorem finiteCap_component_meets_original_core (q : IncidenceQ) :
    ∃ p : cutCore f, finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p ∈ connectedComponent q := by
  obtain ⟨p, hp⟩ := ConnectedComponents.surjective_coe (finiteCapComponentLabel hL hδ f hf hdisj q)
  refine ⟨p, ?_⟩
  rw [connectedComponent_eq_finiteCapComponentLabel_fiber hL hδ f hf hdisj q]
  exact hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCap_component_meets_original_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCap_component_meets_original_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCap_component_meets_original_core ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCap_component_meets_original_core

def finiteCapRetainedCoreInclusion (R : Set (ConnectedComponents (cutCore f))) :
    retainedCore f R → finiteCapRetained hL hδ f hf hdisj R :=
  fun p => ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p.val, p.property⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRetainedCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRetainedCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRetainedCoreInclusion ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRetainedCoreInclusion

theorem finiteCapRetainedCoreInclusion_val (R : Set (ConnectedComponents (cutCore f))) (p : retainedCore f R) :
    (finiteCapRetainedCoreInclusion hL hδ f hf hdisj R p).val =
      finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRetainedCoreInclusion_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRetainedCoreInclusion_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRetainedCoreInclusion_val ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRetainedCoreInclusion_val

theorem finiteCapRetained_component_meets_original_core (R : Set (ConnectedComponents (cutCore f)))
    (q : finiteCapRetained hL hδ f hf hdisj R) :
    ∃ p : retainedCore f R, finiteCapRetainedCoreInclusion hL hδ f hf hdisj R p ∈ connectedComponent q := by
  have him : (Subtype.val : finiteCapRetained hL hδ f hf hdisj R → IncidenceQ) '' connectedComponent q =
      connectedComponent q.val := by
    exact (connectedComponentIn_eq_image (F := (finiteCapRetained hL hδ f hf hdisj R : Set IncidenceQ)) q.property).symm.trans
      ((isClopen_finiteCapRetained_discarded hL hδ f hf hdisj R).1.connectedComponentIn_eq q.property)
  obtain ⟨p, hp⟩ := finiteCap_component_meets_original_core hL hδ f hf hdisj q.val
  rw [← him] at hp
  obtain ⟨r, hr, he⟩ := hp
  have hpr : p ∈ retainedCore f R := by
    have h := r.property
    change r.val ∈ (finiteCapRetained hL hδ f hf hdisj R : Set IncidenceQ) at h
    rw [he] at h
    exact h
  refine ⟨⟨p, hpr⟩, ?_⟩
  have he' : finiteCapRetainedCoreInclusion hL hδ f hf hdisj R ⟨p, hpr⟩ = r := Subtype.ext he.symm
  exact he'.symm ▸ hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRetained_component_meets_original_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRetained_component_meets_original_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRetained_component_meets_original_core ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRetained_component_meets_original_core
end DifferentialGeometry.Topology.ThreeManifold.Surgery
