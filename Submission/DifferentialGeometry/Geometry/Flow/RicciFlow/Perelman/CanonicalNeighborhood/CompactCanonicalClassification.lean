import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactCanonicalCover
import Submission.DifferentialGeometry.Geometry.Neck.CompactCapClassification

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_compact_canonical_poincareStandard_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : ConnectedClosedOrientedManifold.{u} 3) {D : RealTimeInterval}
        (S : SolutionOn (I := I3) (M := M.Carrier) D) (C1 C2 t : ℝ)
        (W : ∀ x : M.Carrier, CanonicalWitness S eps C1 C2 x t),
        (∀ x, (W x).capTubeHasNeckChart eps) → isPoincareStandard M.Carrier := by
  obtain ⟨eta, heta, hclass⟩ := exists_compact_spatial_poincareStandard_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M D S C1 C2 t W hchart
  apply hclass eps heps M (S.base.metric t)
  intro x hx
  rcases (W x).spatial_cap_or_whole_of_not_spatial_neck (hchart x) hx with hp | hr | hc
  · exact Or.inl hp
  · obtain ⟨z, hr⟩ := hr
    exact Or.inr (Or.inl (isPositiveSpaceFormModel_of_roundComponent M hr.some))
  · exact Or.inr (Or.inr hc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_compact_canonical_poincareStandard_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_compact_canonical_poincareStandard_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_compact_canonical_poincareStandard_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_compact_canonical_poincareStandard_tolerance


theorem exists_compact_component_canonical_poincareStandard_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : ClosedOrientedManifold.{u} 3) {D : RealTimeInterval}
        (S : SolutionOn (I := I3) (M := M.Carrier) D)
        (c : ConnectedComponents M.Carrier) (C1 C2 t : ℝ)
        (W : ∀ x : (M.component c).Carrier, CanonicalWitness S eps C1 C2 x.val t),
        (∀ x, (W x).capTubeHasNeckChart eps) →
          isPoincareStandard (M.component c).Carrier := by
  obtain ⟨eta, heta, hclass⟩ := exists_compact_spatial_poincareStandard_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M D S c C1 C2 t W hchart
  let U := M.componentOpen c
  apply hclass eps heps (M.component c) ((S.base.metric t).restrictOpen U)
  intro x hx
  let xU : U := ⟨x.val, x.property⟩
  let _ : CompactSpace U := (M.component c).compact
  let _ : SigmaCompactSpace U := inferInstance
  have hU : (U : Set M.Carrier) = connectedComponent (xU : M.Carrier) := by
    change M.componentSet c = connectedComponent (xU : M.Carrier)
    rw [← xU.property, ClosedOrientedManifold.componentSet_mk]
  rcases (W x).spatial_cap_or_whole_on_connectedComponent_of_not_spatial_neck
      U xU hU (hchart x) hx with hp | hr | hc
  · exact Or.inl hp
  · obtain ⟨z, hr⟩ := hr
    exact Or.inr (Or.inl (isPositiveSpaceFormModel_of_roundComponent (M.component c) hr.some))
  · exact Or.inr (Or.inr hc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_compact_component_canonical_poincareStandard_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_compact_component_canonical_poincareStandard_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_compact_component_canonical_poincareStandard_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_compact_component_canonical_poincareStandard_tolerance

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
