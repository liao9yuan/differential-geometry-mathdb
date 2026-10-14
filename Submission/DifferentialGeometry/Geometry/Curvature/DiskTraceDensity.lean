import Submission.DifferentialGeometry.Geometry.Curvature.DiskTraceCurvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




def diskMapTraceBoundaryDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (γ : ℝ → M) (φ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  let z := circleMap 0 1 θ
  g.inner (U z) (riemannianCurveCurvature g γ (φ θ) : E) (diskMapInwardConormal g U z) *
    Real.sqrt (diskMapConformalCoefficient g U z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapTraceBoundaryDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapTraceBoundaryDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapTraceBoundaryDensity ``Submission.DifferentialGeometry.Geometry.diskMapTraceBoundaryDensity



theorem diskMapTraceBoundaryDensity_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (γ : ℝ → M) (φ : ℝ → ℝ)
    {θ : ℝ} (hz : diskMapConformalCoefficient g U (circleMap 0 1 θ) = 0) :
    diskMapTraceBoundaryDensity g U γ φ θ = 0 := by
  simp [diskMapTraceBoundaryDensity, hz]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapTraceBoundaryDensity_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapTraceBoundaryDensity_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapTraceBoundaryDensity_eq_zero ``Submission.DifferentialGeometry.Geometry.diskMapTraceBoundaryDensity_eq_zero

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem contDiff_diskMapTraceBoundaryDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (htrace : U ∘ circleMap 0 1 = γ ∘ φ) :
    ContDiff ℝ ∞ (diskMapTraceBoundaryDensity g U γ φ) := by
  let c := circleMap 0 1
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ c := (contDiff_circleMap 0 1).contMDiff
  have hz (θ : ℝ) : c θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [c, Metric.mem_closedBall, dist_zero_right]
  have hbase := contMDiff_diskMapBoundary hs hU hDs
  have hH : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun θ => TotalSpace.mk' E (E := TangentSpace 𝓘(ℝ, E)) (U (c θ))
        (riemannianCurveCurvature g γ (φ θ) : E)) := by
    convert (contMDiff_riemannianCurveCurvature g hγ hi).comp hφ.contMDiff using 1
    funext θ
    congr 1
    exact congrFun htrace θ
  have hR : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun θ => TotalSpace.mk' E (U (c θ)) (diskMapPartial (E := E) U (c θ) (c θ))) := by
    apply contMDiffOn_univ.mp
    exact (contMDiffOn_source_tangentMap hs hU (by simp)).comp
      (hc.prodMk hc).contMDiffOn (fun θ _ => ⟨hDs (hz θ), _root_.Set.mem_univ _⟩)
  have hpair : ContDiff ℝ ∞ (fun θ => g.inner (U (c θ))
      (riemannianCurveCurvature g γ (φ θ) : E) (diskMapPartial U (c θ) (c θ))) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    have hp : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
        (fun r => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (U (c r))
          (g.inner (U (c r)) (riemannianCurveCurvature g γ (φ r) : E)
            (diskMapPartial U (c r) (c r)))) θ := by
      apply ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
      · exact g.contMDiff.contMDiffAt.comp θ hbase.contMDiffAt
      · exact hH.contMDiffAt
      · exact hR.contMDiffAt
    exact (contMDiffAt_totalSpace.mp hp).2.contDiffAt
  convert hpair.neg using 1
  funext θ
  exact (hconf _ (hz θ)).inwardConormal_flux _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contDiff_diskMapTraceBoundaryDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contDiff_diskMapTraceBoundaryDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contDiff_diskMapTraceBoundaryDensity ``Submission.DifferentialGeometry.Geometry.contDiff_diskMapTraceBoundaryDensity



theorem intervalIntegrable_diskMapTraceBoundaryDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (htrace : U ∘ circleMap 0 1 = γ ∘ φ) (a b : ℝ) :
    IntervalIntegrable (diskMapTraceBoundaryDensity g U γ φ) _root_.MeasureTheory.MeasureSpace.volume a b :=
  (contDiff_diskMapTraceBoundaryDensity g hs hU hDs hconf hγ hi hφ htrace).continuous.intervalIntegrable a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.intervalIntegrable_diskMapTraceBoundaryDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.intervalIntegrable_diskMapTraceBoundaryDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.intervalIntegrable_diskMapTraceBoundaryDensity ``Submission.DifferentialGeometry.Geometry.intervalIntegrable_diskMapTraceBoundaryDensity

end DifferentialGeometry.Geometry
