import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.ComponentCompactness
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Normalization
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.ChartDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.Filter _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_normalized_minimizing_component_ae_limit_chart_energy_density
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hg : RiemannianMetricComplete g)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (γ : freeLoop M) (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    let b := _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
      weaklyMonotoneDiskCompetitors g γ)
    ∃ u : ℕ → C(closedDisk, M), (∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ) ∧
      Antitone (fun n => riemannianDiskEnergy g (u n)) ∧
      _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop (𝓝 b) ∧
      ∃ (τ : ℕ → C(loopCircle, loopCircle))
        (htrace : ∀ n, diskTrace (u n) = γ.comp (τ n)),
        (∀ n, IsWeaklyMonotoneOnce (τ n)) ∧
        (∀ n, τ n 0 = 0) ∧
        (∀ n, τ n ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle)) ∧
        (∀ n, τ n ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle)) ∧
          let C := connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)
          let gC : SmoothRiemannianMetric 𝓘(ℝ, E) C := g.restrictOpen C
          let uC : ℕ → C(closedDisk, C) := fun n => diskInLoopComponent γ (τ n) (u n) (htrace n)
          let : MeasurableSpace C := borel C
          ∃ (φ : ℕ → ℕ) (v : ℂ → C), StrictMono φ ∧
            AEMeasurable v (volume.restrict (_root_.Metric.ball (0 : ℂ) 1)) ∧
            (∀ n z, ((diskExtension (uC n) z : C) : M) = diskExtension (u n) z) ∧
            (∀ n z, diskMapEnergyDensity gC (diskExtension (uC n)) z =
              diskMapEnergyDensity g (diskExtension (u n)) z) ∧
            (∀ n, diskTrace (uC (φ n)) = (loopInComponent γ).comp (τ (φ n))) ∧
            (∀ᵐ z ∂volume.restrict (_root_.Metric.ball (0 : ℂ) 1),
              _root_.Filter.Tendsto (fun n => diskExtension (uC (φ n)) z) _root_.Filter.atTop (𝓝 (v z))) ∧
            (∀ᵐ z ∂volume.restrict (_root_.Metric.ball (0 : ℂ) 1),
              _root_.Filter.Tendsto (fun n => diskExtension (u (φ n)) z) _root_.Filter.atTop (𝓝 (v z : M))) ∧
            ∃ (ι : Type u), Countable ι ∧ ∃ (center : ι → C)
              (χ : ∀ i, SmoothBumpFunction 𝓘(ℝ, E) (center i))
              (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) C _root_.Set.univ),
              (∀ i, HasCompactSupport (ρ i : C → ℝ)) ∧
              (∀ i, tsupport (ρ i : C → ℝ) ⊆
                interior {p | χ i p = 1} ∩ (extChartAt 𝓘(ℝ, E) (center i)).source) ∧
              let Φ (i : ι) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E C ∞ :=
                (extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ (center i)).symm
              let P (i : ι) (p : C) : EuclideanSpace ℝ (Fin m) := L (χ i p • (Φ i).symm p)
              let e := Complex.orthonormalBasisOneI.repr.symm
              ∃ hw : ∀ i, ∀ k : Fin m,
                  DeGiorgi.MemW1pWitness 2 (fun x => P i (v (e x)) k) (_root_.Metric.ball 0 1),
                let D := chartPartitionEnergyDensity gC L Φ (fun i => χ i)
                  ρ.toPartitionOfUnity (fun x => v (e x)) hw
                (∀ x, 0 ≤ D x) ∧ _root_.MeasureTheory.Integrable D (volume.restrict (_root_.Metric.ball 0 1)) ∧
                  (∫ x in _root_.Metric.ball 0 1, D x) ≤ b := by
  classical
  have hnonempty : (weaklyMonotoneDiskCompetitors g γ).Nonempty :=
    hfinite.mono (spanningDiskCompetitors_subset_weaklyMonotoneDiskCompetitors g γ)
  obtain ⟨u, τ, hu, hτ, htrace, h0, h1, h2, hanti, hlim⟩ :=
    exists_three_point_normalized_disk_energy_minimizing_sequence g γ hnonempty
      (p := (1 / 3 : ℝ)) (q := (2 / 3 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨u, hu, hanti, hlim, τ, htrace, hτ, h0, h1, h2, ?_⟩
  exact exists_component_ae_limit_chart_energy_density_le g hg L γ u τ htrace
    (fun n => (hu n).2) hlim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_normalized_minimizing_component_ae_limit_chart_energy_density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_normalized_minimizing_component_ae_limit_chart_energy_density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_normalized_minimizing_component_ae_limit_chart_energy_density ``Submission.DifferentialGeometry.Geometry.exists_normalized_minimizing_component_ae_limit_chart_energy_density

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.Filter _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_normalized_minimizing_component_ae_limit_energy_bound
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hg : RiemannianMetricComplete g)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (γ : freeLoop M) (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    let b := _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
      weaklyMonotoneDiskCompetitors g γ)
    ∃ u : ℕ → C(closedDisk, M), (∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ) ∧
      Antitone (fun n => riemannianDiskEnergy g (u n)) ∧
      _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop (𝓝 b) ∧
      ∃ (τ : ℕ → C(loopCircle, loopCircle))
        (htrace : ∀ n, diskTrace (u n) = γ.comp (τ n)),
        (∀ n, IsWeaklyMonotoneOnce (τ n)) ∧
        (∀ n, τ n 0 = 0) ∧
        (∀ n, τ n ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle)) ∧
        (∀ n, τ n ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle)) ∧
          let C := connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)
          let gC : SmoothRiemannianMetric 𝓘(ℝ, E) C := g.restrictOpen C
          let uC : ℕ → C(closedDisk, C) := fun n => diskInLoopComponent γ (τ n) (u n) (htrace n)
          let : MeasurableSpace C := borel C
          ∃ (φ : ℕ → ℕ) (v : ℂ → C), StrictMono φ ∧
            AEMeasurable v (volume.restrict (_root_.Metric.ball (0 : ℂ) 1)) ∧
            (∀ n z, ((diskExtension (uC n) z : C) : M) = diskExtension (u n) z) ∧
            (∀ n z, diskMapEnergyDensity gC (diskExtension (uC n)) z =
              diskMapEnergyDensity g (diskExtension (u n)) z) ∧
            (∀ n, diskTrace (uC (φ n)) = (loopInComponent γ).comp (τ (φ n))) ∧
            (∀ᵐ z ∂volume.restrict (_root_.Metric.ball (0 : ℂ) 1),
              _root_.Filter.Tendsto (fun n => diskExtension (uC (φ n)) z) _root_.Filter.atTop (𝓝 (v z))) ∧
            (∀ᵐ z ∂volume.restrict (_root_.Metric.ball (0 : ℂ) 1),
              _root_.Filter.Tendsto (fun n => diskExtension (u (φ n)) z) _root_.Filter.atTop (𝓝 (v z : M))) ∧
            ∀ q : C(closedDisk, C),
              ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension q) (_root_.Metric.ball 0 1) →
              v =ᵐ[volume.restrict (_root_.Metric.ball (0 : ℂ) 1)] diskExtension q →
              _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g (diskExtension (Subtype.val ∘ q)))
                  (_root_.Metric.closedBall (0 : ℂ) 1) ∧
                riemannianDiskEnergy g (Subtype.val ∘ q) ≤ b := by
  classical
  obtain ⟨u, hu, hanti, hlim, τ, htrace, hτ, h0, h1, h2, φ, v, hφ, hvm,
      hcoe, hdensity, htraceC, haeC, haeM, ι, hι, center, χ, ρ,
      _, hρsupport, hw, _, hD, hbound⟩ :=
    exists_normalized_minimizing_component_ae_limit_chart_energy_density g hg L γ hfinite
  let : Countable ι := hι
  refine ⟨u, hu, hanti, hlim, τ, htrace, hτ, h0, h1, h2, φ, v, hφ, hvm,
    hcoe, hdensity, htraceC, haeC, haeM, ?_⟩
  intro q hq hvq
  exact riemannianDiskEnergy_le_inf_of_component_chartPartitionEnergyDensity
    g (connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)) L
    (fun i => (extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ (center i)).symm)
    (fun i => χ i) ρ.toPartitionOfUnity hρsupport v hw q hq hvq hD γ hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_normalized_minimizing_component_ae_limit_energy_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_normalized_minimizing_component_ae_limit_energy_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_normalized_minimizing_component_ae_limit_energy_bound ``Submission.DifferentialGeometry.Geometry.exists_normalized_minimizing_component_ae_limit_energy_bound

end DifferentialGeometry.Geometry

end

end
