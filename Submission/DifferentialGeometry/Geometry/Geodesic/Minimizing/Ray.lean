import Submission.DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Topology _root_.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

section IsMinimizingRayDef

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
def IsMinimizingRay
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (gamma : ℝ → M) : Prop :=
  gamma 0 = p ∧
    IsGeodesicOn (I := I) g gamma (Set.Ici 0) ∧
    ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t →
      _root_.Manifold.riemannianEDist I (gamma s) (gamma t) = ENNReal.ofReal (t - s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay ``Submission.DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay

end IsMinimizingRayDef

namespace IsMinimizingRay

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem start_eq
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {p : M} {gamma : ℝ → M}
    (hgamma : IsMinimizingRay (I := I) g p gamma) :
    gamma 0 = p :=
  hgamma.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay.start_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay.start_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay.start_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay.start_eq

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem isGeodesicOn
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {p : M} {gamma : ℝ → M}
    (hgamma : IsMinimizingRay (I := I) g p gamma) :
    IsGeodesicOn (I := I) g gamma (Set.Ici 0) :=
  hgamma.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay.isGeodesicOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay.isGeodesicOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay.isGeodesicOn ``Submission.DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay.isGeodesicOn

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem edist_eq
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {p : M} {gamma : ℝ → M}
    (hgamma : IsMinimizingRay (I := I) g p gamma)
    ⦃s t : ℝ⦄ (hs : 0 ≤ s) (hst : s ≤ t) :
    riemannianEDist I (gamma s) (gamma t) = ENNReal.ofReal (t - s) :=
  hgamma.2.2 hs hst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay.edist_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay.edist_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay.edist_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.IsMinimizingRay.edist_eq

end IsMinimizingRay

end Riemannian
end Geometry
end DifferentialGeometry

end
