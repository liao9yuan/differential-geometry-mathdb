import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.ChartEnergy.Transition
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import Submission.DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.Analysis.Normed.Group.Bounded
import Submission.DifferentialGeometry.Analysis.Integration.Measure.PartitionDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def weakChartEnergyDensity {d m : ℕ} (g : SmoothRiemannianMetric I M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (χ : M → ℝ)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (v : EuclideanSpace ℝ (Fin d) → M)
    (h : ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ (v x) • Φ.symm (v x)) k) Ω)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin d, pullbackMetricCoefficients g Φ (Φ.symm (v x))
    (L.symm (WithLp.toLp 2 (fun k => (h k).weakGrad x j)))
    (L.symm (WithLp.toLp 2 (fun k => (h k).weakGrad x j)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.weakChartEnergyDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.weakChartEnergyDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.weakChartEnergyDensity ``Submission.DifferentialGeometry.Geometry.weakChartEnergyDensity

theorem weakChartEnergyDensity_nonneg {d m : ℕ} (g : SmoothRiemannianMetric I M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (χ : M → ℝ)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (v : EuclideanSpace ℝ (Fin d) → M)
    (h : ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ (v x) • Φ.symm (v x)) k) Ω)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ weakChartEnergyDensity g L Φ χ v h x := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply Finset.sum_nonneg
  intro j _
  exact (pullbackMetricCoefficients_isPosSemidef g Φ (Φ.symm (v x))).isNonneg.nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.weakChartEnergyDensity_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.weakChartEnergyDensity_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.weakChartEnergyDensity_nonneg ``Submission.DifferentialGeometry.Geometry.weakChartEnergyDensity_nonneg

variable [T2Space M] [MeasurableSpace M] [BorelSpace M]

theorem weakChartEnergyDensity_ae_eq_on_open_overlap
    {d m : ℕ} (g : SmoothRiemannianMetric I M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (ΦA ΦB : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    {O : Set M} (hO : IsOpen O) (hOA : O ⊆ ΦA.target) (hOB : O ⊆ ΦB.target)
    {χA χB : M → ℝ} (hχA : ∀ p ∈ O, χA p = 1) (hχB : ∀ p ∈ O, χB p = 1)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {v : EuclideanSpace ℝ (Fin d) → M} (hv : AEMeasurable v (volume.restrict Ω))
    (hA : ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χA (v x) • ΦA.symm (v x)) k) Ω)
    (hB : ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χB (v x) • ΦB.symm (v x)) k) Ω) :
    weakChartEnergyDensity g L ΦA χA v hA =ᵐ[(volume.restrict Ω).restrict (v ⁻¹' O)]
      weakChartEnergyDensity g L ΦB χB v hB := by
  have h := gradient_energy_ae_eq_restrict_open_chart_overlap L g ΦA ΦB
    hO hOA hOB hχA hχB hΩ hv hA hB
  filter_upwards [h] with x hx
  unfold weakChartEnergyDensity
  congr 1
  exact Finset.sum_congr rfl (fun j _ => (hx j).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.weakChartEnergyDensity_ae_eq_on_open_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.weakChartEnergyDensity_ae_eq_on_open_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.weakChartEnergyDensity_ae_eq_on_open_overlap ``Submission.DifferentialGeometry.Geometry.weakChartEnergyDensity_ae_eq_on_open_overlap

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]

theorem weighted_chart_energy_density_nonneg_integrable
    {d m : ℕ} (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (χ ρ : M → ℝ) (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρsupport : tsupport ρ ⊆ Φ.target) (hρnonneg : ∀ p, 0 ≤ ρ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} {v : EuclideanSpace ℝ (Fin d) → M}
    (hv : AEMeasurable v (volume.restrict Ω))
    (hw : ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ (v x) • Φ.symm (v x)) k) Ω) :
    let G (j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :=
      WithLp.toLp 2 (fun k => (hw k).weakGrad x j)
    let B (p : M) : EuclideanSpace ℝ (Fin m) →L[ℝ]
        EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ :=
      (ρ p • pullbackMetricCoefficients g Φ (Φ.symm p)).bilinearComp
        L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
    let e (x : EuclideanSpace ℝ (Fin d)) := (1 / 2 : ℝ) * ∑ j : Fin d,
      B (v x) (G j x) (G j x)
    (∀ x, 0 ≤ e x) ∧
      (∀ j : Fin d, _root_.MeasureTheory.Integrable (fun x => B (v x) (G j x) (G j x)) (volume.restrict Ω)) ∧
      _root_.MeasureTheory.Integrable e (volume.restrict Ω) ∧
      (∫ x in Ω, e x) = (1 / 2 : ℝ) * ∑ j : Fin d, ∫ x in Ω,
        B (v x) (G j x) (G j x) := by
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let G (j : Fin d) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 (fun k => (hw k).weakGrad x j)
  let Q (p : M) : E →L[ℝ] E →L[ℝ] ℝ :=
    ρ p • pullbackMetricCoefficients g Φ (Φ.symm p)
  let B (p : M) : EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ :=
    (Q p).bilinearComp L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
  let e (x : EuclideanSpace ℝ (Fin d)) := (1 / 2 : ℝ) * ∑ j : Fin d,
    B (v x) (G j x) (G j x)
  have hQOn : ContinuousOn (fun p => pullbackMetricCoefficients g Φ (Φ.symm p)) Φ.target :=
    ((contDiffOn_pullback_metric_coefficients g Φ.open_source
      Φ.contMDiffOn_toFun).contMDiffOn.comp Φ.contMDiffOn_invFun
        (fun p hp => Φ.toOpenPartialHomeomorph.map_target hp)).continuousOn
  have hQ : Continuous Q := by
    refine continuous_of_tsupport fun p hp => ?_
    have hpTarget : p ∈ Φ.target := hρsupport (tsupport_smul_subset_left ρ
      (fun p => pullbackMetricCoefficients g Φ (Φ.symm p)) hp)
    exact hρ.continuousAt.smul (hQOn.continuousAt (Φ.open_target.mem_nhds hpTarget))
  have hQc : HasCompactSupport Q := hρc.mono (Function.support_smul_subset_left ρ
    (fun p => pullbackMetricCoefficients g Φ (Φ.symm p)))
  obtain ⟨C, hC⟩ := hQ.bounded_above_of_compact_support hQc
  have hG (j : Fin d) : _root_.MeasureTheory.MemLp (G j) 2 (volume.restrict Ω) :=
    MemLp.of_eval_piLp fun k => (hw k).weakGrad_component_memLp j
  have hGL (j : Fin d) : _root_.MeasureTheory.MemLp (fun x => L.symm (G j x)) 2 (volume.restrict Ω) :=
    L.symm.toContinuousLinearMap.comp_memLp' (hG j)
  have hQapply (a b : E) : _root_.MeasureTheory.AEStronglyMeasurable (fun x => Q (v x) a b)
      (volume.restrict Ω) :=
    ((hQ.clm_apply continuous_const |>.clm_apply continuous_const).measurable.comp_aemeasurable
      hv).aestronglyMeasurable
  have hcolumn (j : Fin d) : _root_.MeasureTheory.Integrable (fun x => B (v x) (G j x) (G j x))
      (volume.restrict Ω) := by
    exact integrable_bilinear_of_apply_aestronglyMeasurable (fun x => Q (v x)) hQapply
      (Eventually.of_forall fun x => hC (v x)) (hGL j) (hGL j)
  have hnonneg (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ e x := by
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    apply Finset.sum_nonneg
    intro j _
    change 0 ≤ ρ (v x) * pullbackMetricCoefficients g Φ (Φ.symm (v x))
      (L.symm (G j x)) (L.symm (G j x))
    exact mul_nonneg (hρnonneg (v x))
      ((pullbackMetricCoefficients_isPosSemidef g Φ (Φ.symm (v x))).isNonneg.nonneg _)
  have he : _root_.MeasureTheory.Integrable e (volume.restrict Ω) :=
    (_root_.MeasureTheory.integrable_finsetSum Finset.univ (fun j _ => hcolumn j)).const_mul (1 / 2 : ℝ)
  refine ⟨hnonneg, hcolumn, he, ?_⟩
  change (∫ x in Ω, (1 / 2 : ℝ) * ∑ j : Fin d, B (v x) (G j x) (G j x)) = _
  rw [_root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hcolumn j)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.weighted_chart_energy_density_nonneg_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.weighted_chart_energy_density_nonneg_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.weighted_chart_energy_density_nonneg_integrable ``Submission.DifferentialGeometry.Geometry.weighted_chart_energy_density_nonneg_integrable

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M]

theorem weakChartEnergyDensity_ae_eq_on_weight_overlap
    {d m : ℕ} (g : SmoothRiemannianMetric I M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (ΦA ΦB : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (χA χB : M → ℝ) (ρ σ : C(M, ℝ))
    (hρ : tsupport ρ ⊆ interior {p | χA p = 1} ∩ ΦA.target)
    (hσ : tsupport σ ⊆ interior {p | χB p = 1} ∩ ΦB.target)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {v : EuclideanSpace ℝ (Fin d) → M} (hv : AEMeasurable v (volume.restrict Ω))
    (hA : ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χA (v x) • ΦA.symm (v x)) k) Ω)
    (hB : ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χB (v x) • ΦB.symm (v x)) k) Ω) :
    ∀ᵐ x ∂volume.restrict Ω, ρ (v x) ≠ 0 → σ (v x) ≠ 0 →
      weakChartEnergyDensity g L ΦA χA v hA x = weakChartEnergyDensity g L ΦB χB v hB x := by
  let O : Set M := Function.support ρ ∩ Function.support σ
  have hO : IsOpen O := (isOpen_ne_fun ρ.continuous continuous_const).inter
    (isOpen_ne_fun σ.continuous continuous_const)
  have ha : ∀ p ∈ O, χA p = 1 := by
    intro p hp
    exact (interior_subset : interior {p : M | χA p = 1} ⊆ _) (hρ (subset_closure hp.1)).1
  have hb : ∀ p ∈ O, χB p = 1 := by
    intro p hp
    exact (interior_subset : interior {p : M | χB p = 1} ⊆ _) (hσ (subset_closure hp.2)).1
  have h := weakChartEnergyDensity_ae_eq_on_open_overlap g L ΦA ΦB hO
    (fun _ hp => (hρ (subset_closure hp.1)).2)
    (fun _ hp => (hσ (subset_closure hp.2)).2) ha hb hΩ hv hA hB
  filter_upwards [_root_.MeasureTheory.ae_imp_of_ae_restrict h] with x hx hρx hσx
  exact hx ⟨hρx, hσx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.weakChartEnergyDensity_ae_eq_on_weight_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.weakChartEnergyDensity_ae_eq_on_weight_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.weakChartEnergyDensity_ae_eq_on_weight_overlap ``Submission.DifferentialGeometry.Geometry.weakChartEnergyDensity_ae_eq_on_weight_overlap

variable {d m : ℕ} {ι : Type*}

def chartPartitionEnergyDensity
    (g : SmoothRiemannianMetric I M) (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : ι → PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (χ : ι → M → ℝ)
    (ρ : PartitionOfUnity ι M _root_.Set.univ) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (v : EuclideanSpace ℝ (Fin d) → M)
    (h : ∀ i, ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ i (v x) • (Φ i).symm (v x)) k) Ω)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑' i, ρ i (v x) * weakChartEnergyDensity g L (Φ i) (χ i) v (h i) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.chartPartitionEnergyDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.chartPartitionEnergyDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.chartPartitionEnergyDensity ``Submission.DifferentialGeometry.Geometry.chartPartitionEnergyDensity

theorem chartPartitionEnergyDensity_ae_eq_on_weight_support [Countable ι]
    (g : SmoothRiemannianMetric I M) (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : ι → PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (χ : ι → M → ℝ)
    (ρ : PartitionOfUnity ι M _root_.Set.univ)
    (hρ : ∀ i, tsupport (ρ i : M → ℝ) ⊆ interior {p | χ i p = 1} ∩ (Φ i).target)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {v : EuclideanSpace ℝ (Fin d) → M} (hv : AEMeasurable v (volume.restrict Ω))
    (h : ∀ i, ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ i (v x) • (Φ i).symm (v x)) k) Ω) :
    ∀ᵐ x ∂volume.restrict Ω, ∀ i, ρ i (v x) ≠ 0 →
      chartPartitionEnergyDensity g L Φ χ ρ v h x =
        weakChartEnergyDensity g L (Φ i) (χ i) v (h i) x := by
  exact ρ.tsum_mul_ae_eq_of_compatible v
    (fun i => weakChartEnergyDensity g L (Φ i) (χ i) v (h i))
    (fun i j => weakChartEnergyDensity_ae_eq_on_weight_overlap g L
      (Φ i) (Φ j) (χ i) (χ j) (ρ i) (ρ j) (hρ i) (hρ j) hΩ hv (h i) (h j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.chartPartitionEnergyDensity_ae_eq_on_weight_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.chartPartitionEnergyDensity_ae_eq_on_weight_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.chartPartitionEnergyDensity_ae_eq_on_weight_support ``Submission.DifferentialGeometry.Geometry.chartPartitionEnergyDensity_ae_eq_on_weight_support

theorem chartPartitionEnergyDensity_ae_eq [Countable ι]
    {κ : Type*} [Countable κ]
    (g : SmoothRiemannianMetric I M) (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : ι → PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (χ : ι → M → ℝ)
    (ρ : PartitionOfUnity ι M _root_.Set.univ)
    (Ψ : κ → PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (η : κ → M → ℝ)
    (σ : PartitionOfUnity κ M _root_.Set.univ)
    (hρ : ∀ i, tsupport (ρ i : M → ℝ) ⊆ interior {p | χ i p = 1} ∩ (Φ i).target)
    (hσ : ∀ j, tsupport (σ j : M → ℝ) ⊆ interior {p | η j p = 1} ∩ (Ψ j).target)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {v : EuclideanSpace ℝ (Fin d) → M} (hv : AEMeasurable v (volume.restrict Ω))
    (h : ∀ i, ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ i (v x) • (Φ i).symm (v x)) k) Ω)
    (h' : ∀ j, ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (η j (v x) • (Ψ j).symm (v x)) k) Ω) :
    chartPartitionEnergyDensity g L Φ χ ρ v h =ᵐ[volume.restrict Ω]
      chartPartitionEnergyDensity g L Ψ η σ v h' := by
  exact ρ.tsum_mul_ae_eq_of_cross_compatible σ v
    (fun i => weakChartEnergyDensity g L (Φ i) (χ i) v (h i))
    (fun j => weakChartEnergyDensity g L (Ψ j) (η j) v (h' j))
    (fun i j => weakChartEnergyDensity_ae_eq_on_weight_overlap g L
      (Φ i) (Ψ j) (χ i) (η j) (ρ i) (σ j) (hρ i) (hσ j) hΩ hv (h i) (h' j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.chartPartitionEnergyDensity_ae_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.chartPartitionEnergyDensity_ae_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.chartPartitionEnergyDensity_ae_eq ``Submission.DifferentialGeometry.Geometry.chartPartitionEnergyDensity_ae_eq

omit [T2Space M] in
theorem integrable_weighted_weakChartEnergyDensity
    (g : SmoothRiemannianMetric I M) (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (χ : M → ℝ) (ρ : C(M, ℝ))
    (hρc : HasCompactSupport (ρ : M → ℝ)) (hρ : tsupport ρ ⊆ Φ.target)
    (hρ0 : ∀ p, 0 ≤ ρ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {v : EuclideanSpace ℝ (Fin d) → M} (hv : AEMeasurable v (volume.restrict Ω))
    (h : ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ (v x) • Φ.symm (v x)) k) Ω) :
    _root_.MeasureTheory.Integrable (fun x => ρ (v x) * weakChartEnergyDensity g L Φ χ v h x)
      (volume.restrict Ω) := by
  have hi := (weighted_chart_energy_density_nonneg_integrable
    g Φ L χ ρ ρ.continuous hρc hρ hρ0 hv h).2.2.1
  convert hi using 1
  funext x
  simp only [weakChartEnergyDensity, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe, smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integrable_weighted_weakChartEnergyDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integrable_weighted_weakChartEnergyDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integrable_weighted_weakChartEnergyDensity ``Submission.DifferentialGeometry.Geometry.integrable_weighted_weakChartEnergyDensity

omit [T2Space M] in
theorem integrable_chartPartitionEnergyDensity [Countable ι]
    (g : SmoothRiemannianMetric I M) (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : ι → PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (χ : ι → M → ℝ)
    (ρ : PartitionOfUnity ι M _root_.Set.univ)
    (hρc : ∀ i, HasCompactSupport (ρ i : M → ℝ))
    (hρ : ∀ i, tsupport (ρ i : M → ℝ) ⊆ (Φ i).target)
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {v : EuclideanSpace ℝ (Fin d) → M} (hv : AEMeasurable v (volume.restrict Ω))
    (h : ∀ i, ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ i (v x) • (Φ i).symm (v x)) k) Ω)
    (hs : Summable (fun i => ∫ x in Ω,
      ρ i (v x) * weakChartEnergyDensity g L (Φ i) (χ i) v (h i) x)) :
    _root_.MeasureTheory.Integrable (chartPartitionEnergyDensity g L Φ χ ρ v h) (volume.restrict Ω) ∧
      (∫ x in Ω, chartPartitionEnergyDensity g L Φ χ ρ v h x) =
        ∑' i, ∫ x in Ω, ρ i (v x) * weakChartEnergyDensity g L (Φ i) (χ i) v (h i) x := by
  let f : ι → EuclideanSpace ℝ (Fin d) → ℝ := fun i x =>
    ρ i (v x) * weakChartEnergyDensity g L (Φ i) (χ i) v (h i) x
  have hfi (i : ι) : _root_.MeasureTheory.Integrable (f i) (volume.restrict Ω) :=
    integrable_weighted_weakChartEnergyDensity g L (Φ i) (χ i) (ρ i)
      (hρc i) (hρ i) (ρ.nonneg i) hv (h i)
  have hf0 (i : ι) (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ f i x :=
    mul_nonneg (ρ.nonneg i _) (weakChartEnergyDensity_nonneg g L (Φ i) (χ i) v (h i) x)
  have hsum : Summable (fun i => ∫ x in Ω, ‖f i x‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _ _)] using hs
  exact ⟨integrable_tsum_of_summable_integral_norm f hfi hsum,
    (_root_.MeasureTheory.integral_tsum_of_summable_integral_norm hfi hsum).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integrable_chartPartitionEnergyDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integrable_chartPartitionEnergyDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integrable_chartPartitionEnergyDensity ``Submission.DifferentialGeometry.Geometry.integrable_chartPartitionEnergyDensity

end DifferentialGeometry.Geometry

end

end
