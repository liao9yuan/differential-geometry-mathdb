import Submission.DifferentialGeometry.Topology.ThreeManifold.PuncturedCapIncidence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalCappingBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem image_coreComponent_union_caps_eq_componentSet_of_finite_ball_complement
    {Ω : Set M.Carrier} (hΩ : IsClosed Ω) (outer : T.Boundary)
    (hfront : frontier Ω = _root_.Set.range (T.boundarySphere outer))
    (s : Finset T.Boundary)
    (B : T.Boundary → PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace M.Carrier ∞)
    (hB : ∀ b ∈ s, _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ (B b).source)
    (hinside : ∀ b ∈ s, B b '' _root_.Metric.closedBall (0 : ThreeSpace) 1 ⊆ interior Ω)
    (hdis : (s : Set T.Boundary).Pairwise (fun b c =>
      Disjoint (B b '' _root_.Metric.closedBall (0 : ThreeSpace) 1) (B c '' _root_.Metric.closedBall (0 : ThreeSpace) 1)))
    (hsphere : ∀ b ∈ s, B b '' _root_.Metric.sphere (0 : ThreeSpace) 1 = _root_.Set.range (T.boundarySphere b))
    (x : T.core)
    (hcomponent : Ω \ ⋃ b ∈ s, B b '' _root_.Metric.ball (0 : ThreeSpace) 1 =
      (Subtype.val : T.core → M.Carrier) '' connectedComponent x) :
    (C.coreInclusion '' connectedComponent x ∪ ⋃ b ∈ s, _root_.Set.range (C.cap b)) ∪
      range (C.cap outer) = N.componentSet (ConnectedComponents.mk (C.coreInclusion x)) := by
  classical
  obtain ⟨hcontains, hexact⟩ := T.toTopological.boundary_incidence_of_finite_ball_complement_component
    hΩ outer hfront s B hB hinside hdis hsphere x hcomponent
  have h := C.image_coreComponent_union_caps_eq_connectedComponent x
    (_root_.Insert.insert outer (s : Set T.Boundary))
    (fun b hb q => hcontains b (by simpa only [_root_.Set.mem_insert_iff,Finset.mem_coe] using hb) q)
    (fun b hb => by simpa only [_root_.Set.mem_insert_iff,Finset.mem_coe] using hexact b hb)
  rw [ClosedOrientedManifold.componentSet_mk]
  rw [← h]
  ext y
  simp only [_root_.Set.mem_union,_root_.Set.mem_iUnion,_root_.Set.mem_insert_iff,Finset.mem_coe]
  aesop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.image_coreComponent_union_caps_eq_componentSet_of_finite_ball_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.image_coreComponent_union_caps_eq_componentSet_of_finite_ball_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.image_coreComponent_union_caps_eq_componentSet_of_finite_ball_complement ``Submission.DifferentialGeometry.Topology.SphericalCapping.image_coreComponent_union_caps_eq_componentSet_of_finite_ball_complement

end DifferentialGeometry.Topology.SphericalCapping
