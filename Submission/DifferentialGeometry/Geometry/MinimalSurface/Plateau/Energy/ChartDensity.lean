import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.ChartEnergy.Identification
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import Submission.DifferentialGeometry.Analysis.Integration.Measure.EuclideanPlane
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.OpenTarget

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {m : ℕ} {ι : Type*} [Countable ι]

theorem integrable_diskMapEnergyDensity_and_energy_eq_chartPartitionEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : ι → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) (χ : ι → M → ℝ)
    (ρ : PartitionOfUnity ι M _root_.Set.univ)
    (hρ : ∀ i, tsupport (ρ i : M → ℝ) ⊆ interior {p | χ i p = 1} ∩ (Φ i).target)
    (v : EuclideanSpace ℝ (Fin 2) → M)
    (hw : ∀ i, ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ i (v x) • (Φ i).symm (v x)) k) (Metric.ball 0 1))
    (q : C(closedDisk, M))
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension q) (Metric.ball 0 1))
    (hvq : v =ᵐ[volume.restrict (Metric.ball 0 1)]
      (diskExtension q ∘ Complex.orthonormalBasisOneI.repr.symm))
    (hD : _root_.MeasureTheory.Integrable (chartPartitionEnergyDensity g L Φ χ ρ v hw)
      (volume.restrict (Metric.ball 0 1))) :
    _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g (diskExtension q))
        (Metric.closedBall (0 : ℂ) 1) ∧
      riemannianDiskEnergy g q =
        ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
          chartPartitionEnergyDensity g L Φ χ ρ v hw x := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  let U : EuclideanSpace ℝ (Fin 2) → M := diskExtension q ∘ e
  let D := chartPartitionEnergyDensity g L Φ χ ρ v hw
  have heBall {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ Metric.ball 0 1) :
      e x ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, e.norm_map] using hx
  have hU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E) 1 U
      (Metric.ball 0 1) :=
    hq.comp e.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffOn (fun _ hx => heBall hx)
  have hident := chartPartitionEnergyDensity_ae_eq_of_contMDiffOn
    g L Φ χ ρ hρ Metric.isOpen_ball hU hvq hw
  have hactual : D =ᵐ[volume.restrict (Metric.ball 0 1)]
      (fun x => diskMapEnergyDensity g (diskExtension q) (e x)) := by
    filter_upwards [hident, _root_.MeasureTheory.ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
    dsimp only [D]
    rw [hx]
    have hqd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (e x) :=
      (hq.contMDiffAt (Metric.isOpen_ball.mem_nhds (heBall hxB))).mdifferentiableAt one_ne_zero
    have hd := mfderiv_comp (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (I' := 𝓘(ℝ, ℂ)) (I'' := 𝓘(ℝ, E)) x hqd e.differentiableAt.mdifferentiableAt
    rw [mfderiv_eq_fderiv, e.hasFDerivAt.fderiv] at hd
    have hdj (j : Fin 2) :
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, E) U x
          (EuclideanSpace.single j 1) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (e x)
          (e (EuclideanSpace.single j 1)) :=
      congrArg (fun A : EuclideanSpace ℝ (Fin 2) →L[ℝ] E =>
        A (EuclideanSpace.single j 1)) hd
    have h0 : e (EuclideanSpace.single 0 (1 : ℝ)) = (1 : ℂ) := by simp [e]
    have h1 : e (EuclideanSpace.single 1 (1 : ℝ)) = Complex.I := by simp [e]
    simp only [Fin.sum_univ_two, hdj, h0, h1, diskMapEnergyDensity, diskMapPartial, U,
      Function.comp_apply]
    ring
  have hepre : e ⁻¹' Metric.ball (0 : ℂ) 1 =
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext x
    simp only [_root_.Set.mem_preimage, Metric.mem_ball, dist_zero_right, e.norm_map]
  have hemp : _root_.MeasureTheory.MeasurePreserving e
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1))
      (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    have hh := e.measurePreserving.restrict_preimage (s := Metric.ball (0 : ℂ) 1)
      Metric.isOpen_ball.measurableSet
    rwa [hepre] at hh
  have hcomp : _root_.MeasureTheory.Integrable (fun x => diskMapEnergyDensity g (diskExtension q) (e x))
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) := hD.congr hactual
  have hi : _root_.MeasureTheory.Integrable (diskMapEnergyDensity g (diskExtension q))
      (volume.restrict (Metric.ball (0 : ℂ) 1)) :=
    (hemp.integrable_comp_emb e.toMeasurableEquiv.measurableEmbedding).mp hcomp
  have hball := Analysis.Sobolev.Euclidean.restrict_ball_eq_restrict_closedBall_complex (1 : ℝ)
  refine ⟨by simpa only [_root_.MeasureTheory.IntegrableOn, ← hball] using hi, ?_⟩
  change (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension q) z) = _
  rw [← hball, _root_.MeasureTheory.integral_congr_ae hactual]
  exact (hemp.integral_comp e.toMeasurableEquiv.measurableEmbedding _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integrable_diskMapEnergyDensity_and_energy_eq_chartPartitionEnergyDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integrable_diskMapEnergyDensity_and_energy_eq_chartPartitionEnergyDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integrable_diskMapEnergyDensity_and_energy_eq_chartPartitionEnergyDensity ``Submission.DifferentialGeometry.Geometry.integrable_diskMapEnergyDensity_and_energy_eq_chartPartitionEnergyDensity

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {m : ℕ} {ι : Type*} [Countable ι]

theorem integrable_diskMapEnergyDensity_and_energy_eq_chartPartitionEnergyDensity_of_ae_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (N : TopologicalSpace.Opens M) [T2Space N]
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : ι → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E N ∞) (χ : ι → N → ℝ)
    (ρ : PartitionOfUnity ι N _root_.Set.univ)
    (hρ : ∀ i, tsupport (ρ i : N → ℝ) ⊆ interior {p | χ i p = 1} ∩ (Φ i).target)
    (v : ℂ → N)
    (hw : ∀ i, ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ i (v (Complex.orthonormalBasisOneI.repr.symm x)) •
        (Φ i).symm (v (Complex.orthonormalBasisOneI.repr.symm x))) k) (Metric.ball 0 1))
    (q : C(closedDisk, N))
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension q) (Metric.ball 0 1))
    (hvq : v =ᵐ[volume.restrict (Metric.ball (0 : ℂ) 1)] diskExtension q)
    (hD : _root_.MeasureTheory.Integrable (chartPartitionEnergyDensity (g.restrictOpen N) L Φ χ ρ
      (v ∘ Complex.orthonormalBasisOneI.repr.symm) hw)
      (volume.restrict (Metric.ball 0 1))) :
    _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g (diskExtension (Subtype.val ∘ q)))
        (Metric.closedBall (0 : ℂ) 1) ∧
      riemannianDiskEnergy g (Subtype.val ∘ q) =
        ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
          chartPartitionEnergyDensity (g.restrictOpen N) L Φ χ ρ
            (v ∘ Complex.orthonormalBasisOneI.repr.symm) hw x := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  have hepre : e ⁻¹' Metric.ball (0 : ℂ) 1 =
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext x
    simp only [_root_.Set.mem_preimage, Metric.mem_ball, dist_zero_right, e.norm_map]
  have hemp : _root_.MeasureTheory.MeasurePreserving e
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1))
      (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    have hh := e.measurePreserving.restrict_preimage (s := Metric.ball (0 : ℂ) 1)
      Metric.isOpen_ball.measurableSet
    rwa [hepre] at hh
  have hvqe : v ∘ e =ᵐ[volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)]
      diskExtension q ∘ e := hemp.quasiMeasurePreserving.ae_eq hvq
  obtain ⟨henergy, heq⟩ :=
    integrable_diskMapEnergyDensity_and_energy_eq_chartPartitionEnergyDensity
      (g.restrictOpen N) L Φ χ ρ hρ (v ∘ e) hw q hq hvqe hD
  have hdensity : diskMapEnergyDensity (g.restrictOpen N) (diskExtension q) =
      diskMapEnergyDensity g (diskExtension (Subtype.val ∘ q)) := by
    funext z
    exact diskMapEnergyDensity_restrictOpen g N _ z
  refine ⟨by rwa [hdensity] at henergy, ?_⟩
  rw [← riemannianDiskEnergy_restrictOpen g N q]
  exact heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integrable_diskMapEnergyDensity_and_energy_eq_chartPartitionEnergyDensity_of_ae_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integrable_diskMapEnergyDensity_and_energy_eq_chartPartitionEnergyDensity_of_ae_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integrable_diskMapEnergyDensity_and_energy_eq_chartPartitionEnergyDensity_of_ae_eq ``Submission.DifferentialGeometry.Geometry.integrable_diskMapEnergyDensity_and_energy_eq_chartPartitionEnergyDensity_of_ae_eq

theorem riemannianDiskEnergy_le_inf_of_component_chartPartitionEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (N : TopologicalSpace.Opens M) [T2Space N]
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : ι → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E N ∞) (χ : ι → N → ℝ)
    (ρ : PartitionOfUnity ι N _root_.Set.univ)
    (hρ : ∀ i, tsupport (ρ i : N → ℝ) ⊆ interior {p | χ i p = 1} ∩ (Φ i).target)
    (v : ℂ → N)
    (hw : ∀ i, ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ i (v (Complex.orthonormalBasisOneI.repr.symm x)) •
        (Φ i).symm (v (Complex.orthonormalBasisOneI.repr.symm x))) k) (Metric.ball 0 1))
    (q : C(closedDisk, N))
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension q) (Metric.ball 0 1))
    (hvq : v =ᵐ[volume.restrict (Metric.ball (0 : ℂ) 1)] diskExtension q)
    (hD : _root_.MeasureTheory.Integrable (chartPartitionEnergyDensity (g.restrictOpen N) L Φ χ ρ
      (v ∘ Complex.orthonormalBasisOneI.repr.symm) hw)
      (volume.restrict (Metric.ball 0 1)))
    (γ : freeLoop M)
    (hbound : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      chartPartitionEnergyDensity (g.restrictOpen N) L Φ χ ρ
        (v ∘ Complex.orthonormalBasisOneI.repr.symm) hw x) ≤
      _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ)) :
    _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g (diskExtension (Subtype.val ∘ q)))
        (Metric.closedBall (0 : ℂ) 1) ∧
      riemannianDiskEnergy g (Subtype.val ∘ q) ≤
        _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
          weaklyMonotoneDiskCompetitors g γ) := by
  obtain ⟨hi, heq⟩ :=
    integrable_diskMapEnergyDensity_and_energy_eq_chartPartitionEnergyDensity_of_ae_eq
      g N L Φ χ ρ hρ v hw q hq hvq hD
  exact ⟨hi, heq.le.trans hbound⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskEnergy_le_inf_of_component_chartPartitionEnergyDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskEnergy_le_inf_of_component_chartPartitionEnergyDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskEnergy_le_inf_of_component_chartPartitionEnergyDensity ``Submission.DifferentialGeometry.Geometry.riemannianDiskEnergy_le_inf_of_component_chartPartitionEnergyDensity

end DifferentialGeometry.Geometry

end

end
