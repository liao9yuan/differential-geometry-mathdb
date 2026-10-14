import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckModel
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckSides
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOutwardSubsequence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian (IsMetricNorm)
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)
open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation (axialZero)
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions (SpatialNeckSphere SpatialNeckWitness SpatialNeckSideData StrongNeckWitness
  spatialNeckBuffer spatialNeckCentralDomain spatialNeckControlEpsilon)

private local instance neckSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSphereDimension target :: scope.openDecls } }

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {M : Type u} [MetricSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun q : M => TangentSpace I3 q)]
  [IsRiemannianManifold I3 M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {h : SmoothRiemannianMetric I3 M}
  {marks : ℕ → SpatialNeckSphere} {centers : ℕ → M} {eps eta t : ℝ}

theorem exists_strongNeck_compactSide_contains_compact_of_disjoint_escaping_family
    (spatial : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) eta)
    (sides : ∀ i : ℕ, SpatialNeckSideData (spatial i))
    (strong : ∀ i : ℕ, StrongNeckWitness S (marks i) (centers i) t eps)
    (hsphere : ∀ i : ℕ,
      (strong i).embedding '' spatialNeckCentralDomain eps = (spatial i).centralSphere)
    (hEnorm : IsMetricNorm (I := I3) h)
    (heta : eta ≤ spatialNeckControlEpsilon) (heps : eps < 1 / 11)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I3) h)
    {c : ℝ≥0 → M} (hc : Isometry c)
    (hcores : Pairwise (fun i j : ℕ => Disjoint (spatial i).core (spatial j).core))
    (hescape : _root_.Filter.Tendsto centers _root_.Filter.atTop (_root_.Filter.cocompact M))
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞) (K : Set M) (hK : IsCompact K) :
    ∃ (i : ℕ) (nk : StrongNeck S eps (centers i) t),
      K ⊆ (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide ∧
      nk.map.source = spatialNeckBuffer eps ∧
      nk.map.target = _root_.Set.range (strong i).embedding ∧
      nk.center = marks i ∧
      (∀ z : spatialNeckBuffer eps, nk.map z.val = (strong i).embedding z) ∧
      nk.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) = (spatial i).centralSphere := by
  let _ : IsContinuousRiemannianBundle ThreeSpace (fun q : M => TangentSpace I3 q) :=
    hEnorm.isContinuousRiemannianBundle
  obtain ⟨phi, _, _, hexhaust⟩ :=
    KappaSolutions.exists_outward_spatialNeck_exhaustion spatial sides
      hEnorm heta hsec hc hcores hescape
  obtain ⟨n, hn⟩ := (hexhaust K hK).exists
  obtain ⟨nk, hsource, htarget, hcenter, hmap, hcentral⟩ :=
    (strong (phi n)).exists_strongNeck heps
  have hsphereNk : nk.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) =
      (spatial (phi n)).centralSphere := hcentral.trans (hsphere (phi n))
  have hside :=
    (nk.bicollar_zero_sides_eq_of_centralSphere_eq ψ (sides (phi n)) hsphereNk).1
  refine ⟨phi n, nk, ?_, hsource, htarget, hcenter, hmap, hsphereNk⟩
  rw [hside]
  exact hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_strongNeck_compactSide_contains_compact_of_disjoint_escaping_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_strongNeck_compactSide_contains_compact_of_disjoint_escaping_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_strongNeck_compactSide_contains_compact_of_disjoint_escaping_family ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_strongNeck_compactSide_contains_compact_of_disjoint_escaping_family

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
