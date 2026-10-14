import Submission.DifferentialGeometry.Analysis.ODE.Flow.Uniqueness
import Submission.DifferentialGeometry.Geometry.Geodesic.Flow.VectorField

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem isMIntegralCurveOn_geodesicVectorFieldChart_iff
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {K : Set ℝ}
    (hsrc : ∀ t ∈ K, (f t).proj ∈ (chartAt H α).source) :
    IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) K ↔
      IsMIntegralCurveOn f (geodesicVectorField (I := I) g) K := by
  constructor <;> intro hf t ht
  · simpa only [geodesicVectorFieldChart_eq_geodesicVectorField
      (I := I) g α (hsrc t ht)] using hf t ht
  · simpa only [geodesicVectorFieldChart_eq_geodesicVectorField
      (I := I) g α (hsrc t ht)] using hf t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.isMIntegralCurveOn_geodesicVectorFieldChart_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.isMIntegralCurveOn_geodesicVectorFieldChart_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.isMIntegralCurveOn_geodesicVectorFieldChart_iff ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.isMIntegralCurveOn_geodesicVectorFieldChart_iff

theorem isMIntegralCurveAt_geodesicVectorFieldChart_iff
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hsrc : (f t).proj ∈ (chartAt H α).source) :
    IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t ↔
      IsMIntegralCurveAt f (geodesicVectorField (I := I) g) t := by
  constructor <;> intro hf
  all_goals
    have hcont := (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp
      hf.continuousAt
    have hN : (fun u => (f u).proj) ⁻¹' (chartAt H α).source ∈ 𝓝 t :=
      hcont.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hsrc)
    obtain ⟨K, hK, hfK⟩ := isMIntegralCurveAt_iff.mp hf
    refine isMIntegralCurveAt_iff.mpr ⟨K ∩ (fun u => (f u).proj) ⁻¹'
      (chartAt H α).source, _root_.Filter.inter_mem hK hN, ?_⟩
  · exact (isMIntegralCurveOn_geodesicVectorFieldChart_iff g α
      (fun _ hu => hu.2)).mp (hfK.mono _root_.Set.inter_subset_left)
  · exact (isMIntegralCurveOn_geodesicVectorFieldChart_iff g α
      (fun _ hu => hu.2)).mpr (hfK.mono _root_.Set.inter_subset_left)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.isMIntegralCurveAt_geodesicVectorFieldChart_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.isMIntegralCurveAt_geodesicVectorFieldChart_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.isMIntegralCurveAt_geodesicVectorFieldChart_iff ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.isMIntegralCurveAt_geodesicVectorFieldChart_iff

theorem integralCurve_eqOn [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M)
    {f₁ f₂ : ℝ → TangentBundle I M} {K : Set ℝ} {t₀ : ℝ}
    (hK : IsOpen K) (hconn : IsPreconnected K) (ht₀ : t₀ ∈ K)
    (hf₁ : IsMIntegralCurveOn f₁ (geodesicVectorField (I := I) g) K)
    (hf₂ : IsMIntegralCurveOn f₂ (geodesicVectorField (I := I) g) K)
    (heq : f₁ t₀ = f₂ t₀) : _root_.Set.EqOn f₁ f₂ K :=
  isMIntegralCurveOn_eqOn_of_contMDiff_boundaryless hK hconn ht₀
    ((contMDiff_geodesicVectorField g).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)) hf₁ hf₂ heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.integralCurve_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.integralCurve_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.integralCurve_eqOn ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.integralCurve_eqOn

end DifferentialGeometry.Geometry.Riemannian.Geodesic
