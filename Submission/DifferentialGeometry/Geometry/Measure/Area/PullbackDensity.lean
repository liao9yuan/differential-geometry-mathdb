import Submission.DifferentialGeometry.Geometry.Measure.Area.ManifoldMeasurable
import Submission.DifferentialGeometry.Bundle.TangentMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Filter _root_.Set
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def pullbackAreaDensity (g : SmoothRiemannianMetric I M) (r : F → M)
    (y : F) (A : ℂ →L[ℝ] F) : ℝ :=
  tangentTwoJacobian g (mfderiv 𝓘(ℝ, F) I r y (A 1))
    (mfderiv 𝓘(ℝ, F) I r y (A Complex.I))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.pullbackAreaDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.pullbackAreaDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.pullbackAreaDensity ``Submission.DifferentialGeometry.Geometry.pullbackAreaDensity

theorem continuousOn_pullbackAreaDensity (g : SmoothRiemannianMetric I M)
    {r : F → M} {U : Set F} (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, F) I 1 r U) :
    ContinuousOn (fun q : F × (ℂ →L[ℝ] F) => pullbackAreaDensity g r q.1 q.2)
      (Prod.fst ⁻¹' U) :=
  continuousOn_tangentTwoJacobian g (hr.continuousOn_mfderiv_apply hU 1)
    (hr.continuousOn_mfderiv_apply hU Complex.I)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.continuousOn_pullbackAreaDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.continuousOn_pullbackAreaDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.continuousOn_pullbackAreaDensity ``Submission.DifferentialGeometry.Geometry.continuousOn_pullbackAreaDensity

theorem riemannianAreaDensity_comp_eq_pullbackAreaDensity (g : SmoothRiemannianMetric I M)
    {r : F → M} {v : ℂ → F} {z : ℂ} (hr : MDifferentiableAt 𝓘(ℝ, F) I r (v z))
    (hv : DifferentiableAt ℝ v z) :
    riemannianAreaDensity g (r ∘ v) z = pullbackAreaDensity g r (v z) (fderiv ℝ v z) := by
  unfold riemannianAreaDensity pullbackAreaDensity
  rw [mfderiv_comp z hr (mdifferentiableAt_iff_differentiableAt.mpr hv), mfderiv_eq_fderiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianAreaDensity_comp_eq_pullbackAreaDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianAreaDensity_comp_eq_pullbackAreaDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianAreaDensity_comp_eq_pullbackAreaDensity ``Submission.DifferentialGeometry.Geometry.riemannianAreaDensity_comp_eq_pullbackAreaDensity

end DifferentialGeometry.Geometry
