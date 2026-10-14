import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckTopology
import Submission.DifferentialGeometry.Geometry.Comparison.Soul.PositiveSoulDiffeomorph
import Submission.DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [T2Space (TangentBundle I N)] [SigmaCompactSpace N]
  [ConnectedSpace N] [NoncompactSpace N]

private local instance spatialPositiveC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialPositiveC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialPositiveC1 target :: scope.openDecls } }

namespace SpatialNeckWitness

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem compact_end_sides
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) h) :
    ∃ B U : Set N,
      IsConnected B ∧ IsConnected U ∧ IsOpen B ∧ IsOpen U ∧ Disjoint B U ∧
      B ∪ U = W.centralSphereᶜ ∧
      IsCompact (closure B) ∧ ¬ IsCompact (closure U) ∧
      closure B = B ∪ W.centralSphere ∧ interior (closure B) = B ∧
      frontier (closure B) = W.centralSphere ∧ frontier U = W.centralSphere ∧
      (((∀ x : spatialNeckBuffer epsilon, x.val.2 < 0 → W.embedding x ∈ B) ∧
        (∀ x : spatialNeckBuffer epsilon, 0 < x.val.2 → W.embedding x ∈ U)) ∨
       ((∀ x : spatialNeckBuffer epsilon, x.val.2 < 0 → W.embedding x ∈ U) ∧
        (∀ x : spatialNeckBuffer epsilon, 0 < x.val.2 → W.embedding x ∈ B))) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [W.dimension_three]; norm_num⟩
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace I N
  let _ : T3Space N := inferInstance
  let _ : _root_.Bundle.RiemannianBundle (fun x : N => TangentSpace I x) := ⟨h.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x) :=
    ⟨⟨h.inner, h.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace N := EMetricSpace.ofRiemannianMetric I N
  let _ : CompleteSpace N := W.complete.complete
  have hEnorm : IsMetricNorm (I := I) (M := N) h := fun x v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) h x v
  let _ : MetricSpace N := riemMetricSpace (I := I) (M := N)
  let _ : ProperSpace N := properSpace_riemMetric (I := I) W.complete.complete h hEnorm
  let _ : IsRiemannianManifold I N := ⟨fun x y => by
    rw [edist_dist, riemMetric_dist_eq (I := I)]
    exact ENNReal.ofReal_toReal (Exponential.riemannianEDist_ne_top (I := I) x y)⟩
  obtain ⟨_S, _s, _hs, _hne, _hcompact, _hconv, _hboundary, _hdim, e, _he⟩ :=
    DifferentialGeometry.Geometry.Topology.exists_point_soul_diffeomorph h hEnorm hsec p
  exact W.compact_end_sides_of_homeomorph e.toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.compact_end_sides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.compact_end_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.compact_end_sides ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.compact_end_sides

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
