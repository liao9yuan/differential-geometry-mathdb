import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalDomain
import Submission.DifferentialGeometry.Topology.Connected.OpenPartialHomeomorph
import Mathlib.Topology.Connected.LocallyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

omit [SigmaCompactSpace M] in
theorem WindowedModelWitness.image_canonical_domain_eq_connectedComponent_of_isOpen
    {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hbuffer : 2 * C1 ≤ modelRadius delta)
    (hopenU : IsOpen K.domain.carrier) :
    W.embedding '' K.domain.carrier = connectedComponent x := by
  have hh := W.embedding.toOpenPartialHomeomorph.image_eq_connectedComponent_of_isCompact
    K.domain.compact K.domain.connected.isPreconnected hopenU
    (W.canonical_domain_subset_source K hbuffer) (interior_subset K.center_inside)
  change W.embedding '' K.domain.carrier = connectedComponent (W.embedding W.model.basepoint) at hh
  rwa [W.base_map] at hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.image_canonical_domain_eq_connectedComponent_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.image_canonical_domain_eq_connectedComponent_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.image_canonical_domain_eq_connectedComponent_of_isOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.image_canonical_domain_eq_connectedComponent_of_isOpen

omit [SigmaCompactSpace M] in
theorem WindowedModelWitness.image_canonical_domain_eq_connectedComponent
    {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hbuffer : 2 * C1 ≤ modelRadius delta)
    (hwhole : K.domain.carrier = connectedComponent W.model.basepoint) :
    W.embedding '' K.domain.carrier = connectedComponent x := by
  let : LocallyConnectedSpace W.model.M :=
    ChartedSpace.locallyConnectedSpace ThreeSpace W.model.M
  exact W.image_canonical_domain_eq_connectedComponent_of_isOpen K hbuffer
    (hwhole ▸ isOpen_connectedComponent)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.image_canonical_domain_eq_connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.image_canonical_domain_eq_connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.image_canonical_domain_eq_connectedComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.image_canonical_domain_eq_connectedComponent

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
