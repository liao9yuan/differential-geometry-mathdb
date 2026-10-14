import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckReflection
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckPositiveTopology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [T2Space (TangentBundle I N)] [SigmaCompactSpace N]
  [ConnectedSpace N] [NoncompactSpace N]

namespace SpatialNeckWitness

theorem exists_oriented_compact_end_sides
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) h) :
    ∃ W' : SpatialNeckWitness h yStar p epsilon,
      (W' = W ∨ W' = W.reflect) ∧ W'.centralSphere = W.centralSphere ∧
      W'.core = W.core ∧ W'.image = W.image ∧
      ∃ B U : Set N,
        IsConnected B ∧ IsConnected U ∧ IsOpen B ∧ IsOpen U ∧ Disjoint B U ∧
        B ∪ U = W.centralSphereᶜ ∧
        IsCompact (closure B) ∧ ¬ IsCompact (closure U) ∧
        closure B = B ∪ W.centralSphere ∧ interior (closure B) = B ∧
        frontier (closure B) = W.centralSphere ∧ frontier U = W.centralSphere ∧
        (∀ x : spatialNeckBuffer epsilon, x.val.2 < 0 → W'.embedding x ∈ B) ∧
        (∀ x : spatialNeckBuffer epsilon, 0 < x.val.2 → W'.embedding x ∈ U) := by
  obtain ⟨B, U, hB, hU, hBop, hUop, hBU, hcover, hBc, hUnc, hcl, hint, hfr, hUfr,
    hsides⟩ := W.compact_end_sides hsec
  rcases hsides with ⟨hn, hp⟩ | ⟨hn, hp⟩
  · exact ⟨W, Or.inl rfl, rfl, rfl, rfl, B, U, hB, hU, hBop, hUop, hBU,
      hcover, hBc, hUnc, hcl, hint, hfr, hUfr, hn, hp⟩
  · refine ⟨W.reflect, Or.inr rfl, W.reflect_centralSphere, W.reflect_core,
      W.reflect_image, B, U, hB, hU, hBop, hUop, hBU, hcover, hBc, hUnc,
      hcl, hint, hfr, hUfr, ?_, ?_⟩
    · intro x hx
      rw [W.reflect_embedding]
      apply hp
      rw [spatialNeckReflection_val]
      exact neg_pos.mpr hx
    · intro x hx
      rw [W.reflect_embedding]
      apply hn
      rw [spatialNeckReflection_val]
      exact neg_neg_of_pos hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_oriented_compact_end_sides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_oriented_compact_end_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_oriented_compact_end_sides ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_oriented_compact_end_sides

omit [T2Space (TangentBundle I N)] in
theorem exists_oriented_compact_end_sides_of_homotopic_disjoint
    [LocallyConnectedSpace N]
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)
    (r : C(N, N)) (hr : ContinuousMap.Homotopic r (ContinuousMap.id N))
    (hdisjoint : Disjoint (_root_.Set.range r) W.centralSphere)
    (hends : ¬ DifferentialGeometry.Geometry.Topology.HasAtLeastEnds N 2) :
    ∃ W' : SpatialNeckWitness h yStar p epsilon,
      (W' = W ∨ W' = W.reflect) ∧ W'.centralSphere = W.centralSphere ∧
      W'.core = W.core ∧ W'.image = W.image ∧
      ∃ B U : Set N,
        IsConnected B ∧ IsConnected U ∧ IsOpen B ∧ IsOpen U ∧ Disjoint B U ∧
        B ∪ U = W.centralSphereᶜ ∧
        IsCompact (closure B) ∧ ¬ IsCompact (closure U) ∧
        closure B = B ∪ W.centralSphere ∧ interior (closure B) = B ∧
        frontier (closure B) = W.centralSphere ∧ frontier U = W.centralSphere ∧
        (∀ x : spatialNeckBuffer epsilon, x.val.2 < 0 → W'.embedding x ∈ B) ∧
        (∀ x : spatialNeckBuffer epsilon, 0 < x.val.2 → W'.embedding x ∈ U) := by
  obtain ⟨B, U, hB, hU, hBop, hUop, hBU, hcover, hBc, hUnc, hcl, hint, hfr, hUfr,
    hsides⟩ := W.compact_end_sides_of_homotopic_disjoint r hr hdisjoint hends
  rcases hsides with ⟨hn, hp⟩ | ⟨hn, hp⟩
  · exact ⟨W, Or.inl rfl, rfl, rfl, rfl, B, U, hB, hU, hBop, hUop, hBU,
      hcover, hBc, hUnc, hcl, hint, hfr, hUfr, hn, hp⟩
  · refine ⟨W.reflect, Or.inr rfl, W.reflect_centralSphere, W.reflect_core,
      W.reflect_image, B, U, hB, hU, hBop, hUop, hBU, hcover, hBc, hUnc,
      hcl, hint, hfr, hUfr, ?_, ?_⟩
    · intro x hx
      rw [W.reflect_embedding]
      apply hp
      rw [spatialNeckReflection_val]
      exact neg_pos.mpr hx
    · intro x hx
      rw [W.reflect_embedding]
      apply hn
      rw [spatialNeckReflection_val]
      exact neg_neg_of_pos hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_oriented_compact_end_sides_of_homotopic_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_oriented_compact_end_sides_of_homotopic_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_oriented_compact_end_sides_of_homotopic_disjoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_oriented_compact_end_sides_of_homotopic_disjoint

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
