import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactAncientTopology
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.CompactGlobalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalAlternativeTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem nonempty_positiveComponent_of_compact_nonround_pointed_limit
    (X : ℕ → PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    {kappa : ℕ → ℝ} (hX : ∀ i, IsAncientKappaSolution (kappa i) (X i))
    (hnotround : ∀ i, ¬ IsShrinkingSphericalSpaceFormFlow (X i))
    (orient : ∀ i, TangentOrientationSection (X i).M)
    (L : PointedRiemannianManifold.{u, 0, 0} I3) [CompactSpace L.M]
    {phi : ℕ → ℕ} (Phi : PointedRiemannianConvergenceMaps ⟨fun i => (X i).atTime 0⟩ L phi) :
    Nonempty (PositiveComponent (_root_.Set.univ : Set L.M)) := by
  obtain ⟨N, hN⟩ := compactLimit_eventually_globalizes Phi (inferInstance : CompactSpace L.M)
    (fun i => (hX (phi i)).connected)
  obtain ⟨_hsrc, _htgt, e, _he, _hei, _hbase, hcompact⟩ := hN N le_rfl
  let _ : CompactSpace (X (phi N)).M := hcompact
  obtain ⟨data⟩ := nonempty_positiveComponent_of_compact_nonround_ancientKappa
    (X (phi N)) (hX (phi N)) (hnotround (phi N)) (orient (phi N))
  obtain ⟨data'⟩ := positiveComponent_transport_of_partialDiffeomorph data e.symm.toPartialDiffeomorph (_root_.Set.subset_univ _)
  have himage : e.symm.toPartialDiffeomorph '' (_root_.Set.univ : Set ((X (phi N)).atTime 0).M) = univ := by
    change e.symm '' (_root_.Set.univ : Set ((X (phi N)).atTime 0).M) = _root_.Set.univ
    rw [_root_.Set.image_univ]
    exact e.symm.surjective.range_eq
  exact ⟨himage ▸ data'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_compact_nonround_pointed_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_compact_nonround_pointed_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_compact_nonround_pointed_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_positiveComponent_of_compact_nonround_pointed_limit

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
