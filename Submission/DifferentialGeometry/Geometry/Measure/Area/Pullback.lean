import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]



theorem riemannianAreaDensity_pullback
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) {U : ℂ → M} {z : ℂ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) :
    riemannianAreaDensity (Diffeomorph.pullbackMetric g Φ) U z =
      riemannianAreaDensity g (Φ ∘ U) z := by
  have hd := mfderiv_comp z (Φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hU
  simp only [riemannianAreaDensity, tangentTwoJacobian, Diffeomorph.pullbackMetric_inner,
    hd]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianAreaDensity_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianAreaDensity_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianAreaDensity_pullback ``Submission.DifferentialGeometry.Geometry.riemannianAreaDensity_pullback



theorem SmoothDiskExtension.area_pullback
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) :
    riemannianDiskArea (Diffeomorph.pullbackMetric g Φ) u =
      riemannianDiskArea g ((⟨Φ, Φ.contMDiff.continuous⟩ : C(M, M)).comp u) := by
  obtain ⟨heq, s, hs, hDs, hU⟩ := hu
  rw [riemannianDiskArea_eq_of_extension (Diffeomorph.pullbackMetric g Φ) u U heq,
    riemannianDiskArea_eq_of_extension g ((⟨Φ, Φ.contMDiff.continuous⟩ : C(M, M)).comp u) (Φ ∘ U)
      (fun z => congrArg Φ (heq z))]
  apply _root_.MeasureTheory.setIntegral_congr_fun measurableSet_closedBall
  intro z hz
  exact riemannianAreaDensity_pullback g Φ
    (((hU z (hDs hz)).contMDiffAt (hs.mem_nhds (hDs hz))).mdifferentiableAt (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.area_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.area_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.area_pullback ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.area_pullback

end DifferentialGeometry.Geometry
