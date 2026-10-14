import Submission.DifferentialGeometry.Geometry.Measure.Area.LocalReparametrization
import Submission.DifferentialGeometry.Geometry.Measure.Area.CylinderArea
import Submission.DifferentialGeometry.Topology.LoopSpace.AnnulusSectors
import Submission.DifferentialGeometry.Topology.LoopSpace.AttachAnnulus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]




theorem attachDiskAnnulus_sector_area (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : ℂ → M) (H : ℝ × loopCircle → M) {K : ℝ≥0}
    (hA : ∀ z w, riemannianEDistOf g (attachDiskAnnulus u H z) (attachDiskAnnulus u H w) ≤
      (K : ℝ≥0∞) * _root_.EDist.edist z w) {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a + 1 / 2 ≤ 1) :
    riemannianArea g (attachDiskAnnulus u H) (annulusPolarMap '' annulusSector a) =
      riemannianArea g (cylinderLift H) (annulusSector a) := by
  obtain ⟨C, hC⟩ := exists_annulusPolarMap_lipschitz
  have hφ := hC.mono (annulusSector_subset_square ha₀ ha₁)
  have hL : ∀ z ∈ annulusSector a, ∀ w ∈ annulusSector a,
      edist z w ≤ (8 : ℝ≥0∞) * _root_.EDist.edist (annulusPolarMap z) (annulusPolarMap w) := by
    intro z hz w hw
    have h := annulusPolarMap_inverse_dist_le (_root_.Set.Ioo_subset_Icc_self hz.1)
      (_root_.Set.Ioo_subset_Icc_self hw.1) (_root_.Set.Ioo_subset_Icc_self hz.2) (_root_.Set.Ioo_subset_Icc_self hw.2)
    simpa only [edist_dist, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
      ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal h
  have hcv := riemannianArea_precomp_on g (L := 8) hA (isOpen_annulusSector a) hφ hL
  rw [← hcv]
  apply riemannianArea_congr_on_open g (isOpen_annulusSector a)
  intro z hz
  change attachDiskAnnulus u H (annulusPolarMap z) = H (z.re, (z.im : loopCircle))
  rw [attachDiskAnnulus, if_neg (by
    rw [norm_annulusPolarMap (_root_.Set.Ioo_subset_Icc_self hz.1)]
    linarith [hz.1.1]), polarAnnulusCoordinates_annulusPolarMap (_root_.Set.Ioo_subset_Icc_self hz.1)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.attachDiskAnnulus_sector_area then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.attachDiskAnnulus_sector_area"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.attachDiskAnnulus_sector_area ``Submission.DifferentialGeometry.Geometry.attachDiskAnnulus_sector_area

end DifferentialGeometry.Geometry
