import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}


structure SpatialNeck (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (x : M) where
  eps_pos : 0 < eps
  eps_small : eps < 1 / 11
  Q_pos : 0 < metricScalarAt g x
  cylinder : CylinderReference
  map : PartialDiffeomorph IC I3 Cylinder M ∞
  center : Sphere 2
  center_eq : map (center, 0) = x
  domain : Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹ ⊆ map.source
  comparison : MetricComparisonOn (fun _ => cylinder.metric 0)
    (fun _ => scaleMetric (metricScalarAt g x) Q_pos g) map
    (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹) {0} (⌈eps⁻¹⌉₊) eps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

def SpatialNeck.scaleMetric (nk : SpatialNeck g eps p) (c : ℝ) (hc : 0 < c) :
    SpatialNeck (DifferentialGeometry.scaleMetric c hc g) eps p := by
  have hscalar : 0 < metricScalarAt (DifferentialGeometry.scaleMetric c hc g) p := by
    rw [metricScalarAt_scaleMetric]
    exact mul_pos (inv_pos.mpr hc) nk.Q_pos
  refine {
    eps_pos := nk.eps_pos
    eps_small := nk.eps_small
    Q_pos := hscalar
    cylinder := nk.cylinder
    map := nk.map
    center := nk.center
    center_eq := nk.center_eq
    domain := nk.domain
    comparison := ?_ }
  have hnorm : DifferentialGeometry.scaleMetric
      (metricScalarAt (DifferentialGeometry.scaleMetric c hc g) p) hscalar
      (DifferentialGeometry.scaleMetric c hc g) =
      DifferentialGeometry.scaleMetric (metricScalarAt g p) nk.Q_pos g := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [scaleMetric_inner, scaleMetric_inner, scaleMetric_inner, metricScalarAt_scaleMetric]
    field_simp
  rw [hnorm]
  exact nk.comparison

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric

@[simp] theorem SpatialNeck.scaleMetric_map (nk : SpatialNeck g eps p) (c : ℝ) (hc : 0 < c) :
    (nk.scaleMetric c hc).map = nk.map := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric_map

@[simp] theorem SpatialNeck.scaleMetric_center (nk : SpatialNeck g eps p) (c : ℝ) (hc : 0 < c) :
    (nk.scaleMetric c hc).center = nk.center := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric_center ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric_center

@[simp] theorem SpatialNeck.scaleMetric_cylinder (nk : SpatialNeck g eps p) (c : ℝ) (hc : 0 < c) :
    (nk.scaleMetric c hc).cylinder = nk.cylinder := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric_cylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.scaleMetric_cylinder

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
