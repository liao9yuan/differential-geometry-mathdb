import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Reparametrization.Interior
import Submission.DifferentialGeometry.Analysis.Complex.RiemannMapping.InverseBoundary
import Submission.DifferentialGeometry.Topology.LoopSpace.DiskBoundaryHomeomorphism
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Locality
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.WeakJordanHomeomorphism
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.RadialStationarity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.ContDiff _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem SmoothDiskExtension.exists_competitor_energy_lt_area_add
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    {q : C(closedDisk, M)} {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (htrace : DiskWeakJordanTrace γ q) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : C(closedDisk, M), v ∈ weaklyMonotoneDiskCompetitors g γ ∧
      riemannianDiskEnergy g v < riemannianDiskArea g q + ε := by
  obtain ⟨r, W, e, f, ψ, hr, _, _, _, hes, _, heW, he, hei, hfs, hft, hf, _, _,
    hψs, hψt, _, _, _, _, hψieq, _, hEn⟩ :=
    hQ.exists_interior_reparametrization_energy_lt_area g hε
  have hfsource : f.source = e '' Metric.ball (0 : ℂ) 1 := by rw [heW]; exact hfs
  obtain ⟨C, D, H, _, hHiLip, _, _, hHi⟩ :=
    Complex.exists_bilipschitz_riemann_map_comp_extension_of_buffered_disk
      e f hr hes he hei hfsource hft hf
  have hHiψ (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      (H.symm ⟨z, Metric.ball_subset_closedBall hz⟩ : ℂ) = ψ.symm z := by
    rw [hHi z hz, hψieq]
  obtain ⟨δ, hδ⟩ := exists_circle_homeomorph_of_disk_homeomorph_extension
    H.symm ψ.symm hψt hψs hHiψ
  let φ : C(closedDisk, closedDisk) := ⟨H.symm, H.symm.continuous⟩
  have hq : q ∈ weaklyMonotoneDiskCompetitors g γ := ⟨htrace, hQ.lipschitz g⟩
  have hcomp := (mem_weaklyMonotoneDiskCompetitors_comp_of_boundary_reparametrization
    g hq φ hHiLip ⟨δ, δ.continuous⟩ (isWeaklyMonotoneOnce_homeomorph δ) hδ).1
  refine ⟨q.comp φ, hcomp, ?_⟩
  rw [riemannianDiskEnergy_comp_eq_of_extensions g hQ.1 φ hHiψ]
  exact hEn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_competitor_energy_lt_area_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.exists_competitor_energy_lt_area_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_competitor_energy_lt_area_add ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.exists_competitor_energy_lt_area_add

theorem SmoothDiskExtension.disk_energy_inf_le_area
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    {q : C(closedDisk, M)} {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (htrace : DiskWeakJordanTrace γ q) :
    _root_.InfSet.sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) ≤ riemannianDiskArea g q := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨v, hv, hEn⟩ := hQ.exists_competitor_energy_lt_area_add g htrace hε
  have hbound : BddBelow ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    exact riemannianDiskEnergy_nonneg g w
  exact (csInf_le hbound (_root_.Set.mem_image_of_mem _ hv)).trans hEn.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.disk_energy_inf_le_area then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.disk_energy_inf_le_area"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.disk_energy_inf_le_area ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.disk_energy_inf_le_area

end DifferentialGeometry.Geometry

end

end
