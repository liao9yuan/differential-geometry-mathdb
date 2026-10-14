import Submission.DifferentialGeometry.Geometry.Measure.Area.PullbackDensity
import Submission.DifferentialGeometry.Geometry.Measure.Area.Manifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tendsto_riemannianArea_comp_of_fderiv_tendsto
    (g : SmoothRiemannianMetric I M) {r : F → M} {U K : Set F}
    (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, F) I 1 r U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    {D : Set ℂ} (hD : MeasurableSet D) (hDfinite : _root_.MeasureTheory.MeasureSpace.volume D ≠ ⊤)
    {u : ℕ → ℂ → F} {v : ℂ → F} {B : ℝ}
    (hu : ∀ n z, z ∈ D → ContDiffAt ℝ 1 (u n) z)
    (hv : ∀ᵐ z ∂volume.restrict D, DifferentiableAt ℝ v z)
    (huK : ∀ n, _root_.Set.MapsTo (u n) D K)
    (hB : ∀ n z, z ∈ D → ‖fderiv ℝ (u n) z‖ ≤ B)
    (hval : ∀ᵐ z ∂volume.restrict D, _root_.Filter.Tendsto (fun n => u n z) _root_.Filter.atTop (𝓝 (v z)))
    (hder : ∀ᵐ z ∂volume.restrict D,
      _root_.Filter.Tendsto (fun n => fderiv ℝ (u n) z) _root_.Filter.atTop (𝓝 (fderiv ℝ v z))) :
    _root_.Filter.Tendsto (fun n => riemannianArea g (r ∘ u n) D) _root_.Filter.atTop
      (𝓝 (riemannianArea g (r ∘ v) D)) := by
  let J : F × (ℂ →L[ℝ] F) → ℝ := fun q => pullbackAreaDensity g r q.1 q.2
  have hJ : ContinuousOn J (Prod.fst ⁻¹' U) := continuousOn_pullbackAreaDensity g hU hr
  have hcompact : IsCompact (K ×ˢ _root_.Metric.closedBall (0 : ℂ →L[ℝ] F) B) :=
    hK.prod (_root_.ProperSpace.isCompact_closedBall 0 B)
  obtain ⟨A, hA⟩ := hcompact.bddAbove_image
    (hJ.norm.mono (fun q hq => hKU hq.1))
  have heq (n : ℕ) (z : ℂ) (hz : z ∈ D) :
      riemannianAreaDensity g (r ∘ u n) z = J (u n z, fderiv ℝ (u n) z) := by
    apply riemannianAreaDensity_comp_eq_pullbackAreaDensity
    · exact ((hr _ (hKU (huK n hz))).mdifferentiableWithinAt (by simp)).mdifferentiableAt
        (hU.mem_nhds (hKU (huK n hz)))
    · exact (hu n z hz).differentiableAt (by simp)
  have hmeas (n : ℕ) : _root_.MeasureTheory.AEStronglyMeasurable (riemannianAreaDensity g (r ∘ u n))
      (volume.restrict D) := by
    have hc : ContinuousOn (fun z => J (u n z, fderiv ℝ (u n) z)) D :=
      hJ.comp (fun z hz => ((hu n z hz).continuousAt.prodMk
        ((hu n z hz).continuousAt_fderiv (by simp))).continuousWithinAt)
        (fun z hz => hKU (huK n hz))
    exact (hc.aestronglyMeasurable hD).congr
      (_root_.MeasureTheory.ae_restrict_of_forall_mem hD (fun z hz => (heq n z hz).symm))
  have hbound (n : ℕ) : ∀ᵐ z ∂volume.restrict D,
      ‖riemannianAreaDensity g (r ∘ u n) z‖ ≤ A := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hD] with z hz
    rw [heq n z hz]
    exact hA (_root_.Set.mem_image_of_mem _ ⟨huK n hz, mem_closedBall_zero_iff.mpr (hB n z hz)⟩)
  have hlim : ∀ᵐ z ∂volume.restrict D,
      _root_.Filter.Tendsto (fun n => riemannianAreaDensity g (r ∘ u n) z) _root_.Filter.atTop
        (𝓝 (riemannianAreaDensity g (r ∘ v) z)) := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hD, hval, hder, hv] with z hz hvalz hd hvz
    have hvU : v z ∈ U := hKU (hK.isClosed.mem_of_tendsto hvalz
      (Eventually.of_forall (fun n => huK n hz)))
    have hJz : ContinuousAt J (v z, fderiv ℝ v z) :=
      hJ.continuousAt ((hU.preimage continuous_fst).mem_nhds hvU)
    have hlimit := hJz.tendsto.comp (hvalz.prodMk_nhds hd)
    have hveq : riemannianAreaDensity g (r ∘ v) z = J (v z, fderiv ℝ v z) := by
      apply riemannianAreaDensity_comp_eq_pullbackAreaDensity
      · exact ((hr _ hvU).mdifferentiableWithinAt (by simp)).mdifferentiableAt
          (hU.mem_nhds hvU)
      · exact hvz
    rw [hveq]
    exact hlimit.congr (fun n => (heq n z hz).symm)
  exact _root_.MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ : ℂ => A) hmeas
    (_root_.MeasureTheory.integrableOn_const hDfinite) hbound hlim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.tendsto_riemannianArea_comp_of_fderiv_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.tendsto_riemannianArea_comp_of_fderiv_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.tendsto_riemannianArea_comp_of_fderiv_tendsto ``Submission.DifferentialGeometry.Geometry.tendsto_riemannianArea_comp_of_fderiv_tendsto

end DifferentialGeometry.Geometry
