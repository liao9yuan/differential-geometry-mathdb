import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessTransport
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ}
  {U : TopologicalSpace.Opens M}

def SpatialNeck.ofRestrictOpen {z : U} (nk : SpatialNeck (g.restrictOpen U) eps z) :
    SpatialNeck g eps z.val :=
  nk.pushforward (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I3 U ⟨z⟩)
    (fun y _ v w => by
      change g.inner y.val (mfderiv I3 I3 (Subtype.val : U → M) y v)
        (mfderiv I3 I3 (Subtype.val : U → M) y w) = g.inner y.val v w
      rw [DifferentialGeometry.mfderiv_subtype_val_apply,
        DifferentialGeometry.mfderiv_subtype_val_apply])
    (fun _ _ => _root_.Set.mem_univ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.ofRestrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.ofRestrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.ofRestrictOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.ofRestrictOpen

theorem SpatialNeck.ofRestrictOpen_map {z : U} (nk : SpatialNeck (g.restrictOpen U) eps z)
    (y : Cylinder) : nk.ofRestrictOpen.map y = (nk.map y).val :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.ofRestrictOpen_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.ofRestrictOpen_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.ofRestrictOpen_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.ofRestrictOpen_map

theorem SpatialNeck.ofRestrictOpen_center {z : U} (nk : SpatialNeck (g.restrictOpen U) eps z) :
    nk.ofRestrictOpen.center = nk.center :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.ofRestrictOpen_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.ofRestrictOpen_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.ofRestrictOpen_center ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.ofRestrictOpen_center

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
