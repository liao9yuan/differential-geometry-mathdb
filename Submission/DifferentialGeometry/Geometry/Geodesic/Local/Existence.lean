import Submission.DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_isMIntegralCurveAt_geodesicVectorFieldChart
    (g : SmoothRiemannianMetric I M) [I.Boundaryless] [CompleteSpace E]
    (p : M) (v : TangentSpace I p) :
    ∃ f : ℝ → TangentBundle I M,
      f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) 0 := by
  classical
  have hp_source : p ∈ (chartAt H p).source := mem_chart_source H p
  have hsmooth : ContMDiffAt I.tangent I.tangent.tangent ∞
      (fun q : TangentBundle I M =>
        (⟨q, geodesicVectorFieldChart (I := I) g p q⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (⟨p, v⟩ : TangentBundle I M) :=
    geodesicVectorFieldChart_contMDiffAt (I := I) g p
      (p₀ := (⟨p, v⟩ : TangentBundle I M)) hp_source
  have hsmooth1 : ContMDiffAt I.tangent I.tangent.tangent 1
      (fun q : TangentBundle I M =>
        (⟨q, geodesicVectorFieldChart (I := I) g p q⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (⟨p, v⟩ : TangentBundle I M) :=
    hsmooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  exact
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := geodesicVectorFieldChart (I := I) g p)
      (t₀ := (0 : ℝ)) (x₀ := (⟨p, v⟩ : TangentBundle I M)) hsmooth1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_isMIntegralCurveAt_geodesicVectorFieldChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_isMIntegralCurveAt_geodesicVectorFieldChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_isMIntegralCurveAt_geodesicVectorFieldChart ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_isMIntegralCurveAt_geodesicVectorFieldChart

def projectCurve (f : ℝ → TangentBundle I M) : ℝ → M := fun t => (f t).proj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.projectCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.projectCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.projectCurve ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.projectCurve

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
@[simp] lemma projectCurve_apply (f : ℝ → TangentBundle I M) (t : ℝ) :
    projectCurve (I := I) f t = (f t).proj := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.projectCurve_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.projectCurve_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.projectCurve_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.projectCurve_apply

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma projectCurve_zero_of_lift {f : ℝ → TangentBundle I M} {p : M} {v : E}
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M)) :
    projectCurve (I := I) f 0 = p := by
  simp [projectCurve, hf0]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.projectCurve_zero_of_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.projectCurve_zero_of_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.projectCurve_zero_of_lift ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.projectCurve_zero_of_lift

section ChartedPicardLindelof

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_geodesic_with_initial_velocity_at
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ∃ γ : ℝ → M, ∃ f : ℝ → TangentBundle I M,
      f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
      γ = projectCurve (I := I) f ∧
      γ 0 = p ∧
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) 0 ∧
      IsGeodesicAt (I := I) g γ 0 := by
  obtain ⟨f, hf0, hf⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) g p v
  refine ⟨projectCurve (I := I) f, f, hf0, rfl,
    projectCurve_zero_of_lift (I := I) hf0, hf, ?_⟩
  refine ⟨p, f, fun t => rfl, ?_, hf⟩
  have h0 : (f 0).proj = p := projectCurve_zero_of_lift (I := I) hf0
  rw [h0]; exact mem_chart_source H p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_geodesic_with_initial_velocity_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_geodesic_with_initial_velocity_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_geodesic_with_initial_velocity_at ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_geodesic_with_initial_velocity_at

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem hasMFDerivAt_lift_zero
    {g : SmoothRiemannianMetric I M} {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g
      (Bundle.TotalSpace.proj (f 0))) 0) :
    HasMFDerivAt 𝓘(ℝ) I.tangent f 0
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (geodesicVectorFieldChart (I := I) g
          (Bundle.TotalSpace.proj (f 0)) (f 0)))) :=
  hf.hasMFDerivAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.hasMFDerivAt_lift_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.hasMFDerivAt_lift_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.hasMFDerivAt_lift_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.hasMFDerivAt_lift_zero

end ChartedPicardLindelof

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
