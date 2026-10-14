import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.WeakPullback
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.QuadraticLowerSemicontinuity
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.BoundaryRecovery
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.StressConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι
local notation "μ" => volume.restrict (Metric.ball (0 : V) 1)

theorem riemannianDiskEnergy_le_inf_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : _root_.Set.range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
      (𝓝 (_root_.InfSet.sInf ((fun p : C(closedDisk, M) => riemannianDiskEnergy g p) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (w : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[μ]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : _root_.MeasureTheory.Lp V 2 μ),
      _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) _root_.Filter.atTop
        (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (hae : ∀ᵐ x ∂μ,
      _root_.Filter.Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        _root_.Filter.atTop (𝓝 (w x)))
    (v : V → F) (hvc : ContDiffOn ℝ 1 v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[μ] w) (hvK : _root_.Set.MapsTo v (Metric.ball (0 : V) 1) (_root_.Set.range Φ))
    (q : C(closedDisk, M))
    (hq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      diskExtension q z = r (v (Complex.orthonormalBasisOneI.repr z)))
    : riemannianDiskEnergy g q ≤
      _root_.InfSet.sInf ((fun p : C(closedDisk, M) => riemannianDiskEnergy g p) ''
        weaklyMonotoneDiskCompetitors g γ) := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  let f : ℕ → V → F := fun n x => Φ (diskExtension (u n) (e x))
  let A := pullbackMetricCoefficients g r
  have hA : ContinuousOn A (_root_.Set.range Φ) :=
    (continuousOn_pullback_metric_coefficients_of_contMDiffOn_one g hN hr).mono hΦN
  have hK : IsCompact (_root_.Set.range Φ) := isCompact_range hΦ.continuous
  have hwK : ∀ᵐ x ∂μ, w x ∈ _root_.Set.range Φ := by
    filter_upwards [hae] with x hx
    exact hK.isClosed.mem_of_tendsto hx (Eventually.of_forall fun n => _root_.Set.mem_range_self _)
  obtain ⟨CΦ, _, hCΦ⟩ := exists_lipschitzWith_comp_and_ae_norm_fderiv_sq_le g hΦ
  choose L hL using fun n => (hu n).2
  have hf (n : ℕ) : LipschitzWith (CΦ * L n) (f n) := by
    have h := (hCΦ (diskExtension (u n)) (L n)
      (diskExtension_riemannian_lipschitz g (hL n))).1
    intro x y
    simpa only [f, Function.comp_apply, e.isometry.edist_eq] using! h (e x) (e y)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hA
  have hBm (n : ℕ) : _root_.MeasureTheory.AEStronglyMeasurable (fun x => A (f n x)) μ :=
    (hA.comp_continuous (hf n).continuous (fun x => _root_.Set.mem_range_self _)).aestronglyMeasurable
  have hBC (n : ℕ) : ∀ᵐ x ∂μ, ‖A (f n x)‖ ≤ C :=
    Eventually.of_forall fun x => hC _ (_root_.Set.mem_range_self _)
  have hBlim : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => A (f n x)) _root_.Filter.atTop (𝓝 (A (w x))) := by
    filter_upwards [hae, hwK] with x hx hxK
    exact (hA (w x) hxK).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hx, Eventually.of_forall (fun n => _root_.Set.mem_range_self _)⟩)
  have hpos (n : ℕ) : ∀ᵐ x ∂μ, ∀ z, 0 ≤ A (f n x) z z :=
    Eventually.of_forall fun x z => (pullbackMetricCoefficients_isPosSemidef g r _).nonneg z
  have hlsc := Analysis.Sobolev.Euclidean.sum_integral_quadratic_gradient_column_le_liminf_of_tendsto_inner
    f w hs hw (fun n => CΦ * L n) hf hrep hweak (fun n x => A (f n x)) (fun x => A (w x))
    hBm C hBC hBlim hpos
  have heq (n : ℕ) : (∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
      A (f n x) (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
        (fderiv ℝ (f n) x (EuclideanSpace.single j 1))) = 2 * riemannianDiskEnergy g (u n) := by
    exact sum_integral_pullback_gradient_eq_two_mul_riemannianDiskEnergy
      g hΦ hN hr hΦN hleft (u n) (hL n)
  simp only [heq] at hlsc
  rw [(hmin.const_mul 2).liminf_eq] at hlsc
  have hqEnergy := (integrable_diskMapEnergyDensity_and_energy_eq_of_contDiffOn_representative
    g hN hr hK hΦN q w hw v hvc hvw hvK hq).2
  rw [hqEnergy]
  change _ / 2 ≤ _
  change (∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
    pullbackMetricCoefficients g r (w x)
      (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤ _ at hlsc
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskEnergy_le_inf_of_minimizing_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskEnergy_le_inf_of_minimizing_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskEnergy_le_inf_of_minimizing_sequence ``Submission.DifferentialGeometry.Geometry.riemannianDiskEnergy_le_inf_of_minimizing_sequence

end DifferentialGeometry.Geometry

end

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι
local notation "μ" => volume.restrict (Metric.ball (0 : V) 1)

theorem riemannianDiskEnergy_eq_inf_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N)
    (hΦN : _root_.Set.range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
      (𝓝 (_root_.InfSet.sInf ((fun p : C(closedDisk, M) => riemannianDiskEnergy g p) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (w : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[μ]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : _root_.MeasureTheory.Lp V 2 μ),
      _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) _root_.Filter.atTop
        (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (hae : ∀ᵐ x ∂μ,
      _root_.Filter.Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        _root_.Filter.atTop (𝓝 (w x)))
    (v : V → F) (hvc : ContDiffOn ℝ 1 v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[μ] w) (hvK : _root_.Set.MapsTo v (Metric.ball (0 : V) 1) (_root_.Set.range Φ))
    (q : C(closedDisk, M))
    (hq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      diskExtension q z = r (v (Complex.orthonormalBasisOneI.repr z)))
    {KΓ : ℝ≥0} (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (τ : C(loopCircle, loopCircle)) (hτ : IsWeaklyMonotoneOnce τ)
    (hτ0 : τ 0 = 0) (hτ1 : τ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle))
    (hτ2 : τ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle))
    (htrace : diskTrace q = γ.comp τ)
    : riemannianDiskEnergy g q =
      _root_.InfSet.sInf ((fun p : C(closedDisk, M) => riemannianDiskEnergy g p) ''
        weaklyMonotoneDiskCompetitors g γ) := by
  have hlo := riemannianDiskEnergy_le_inf_of_minimizing_sequence
    g (hΦ.of_le (by simp)) hN (hr.of_le (by simp)) hΦN hleft
    u hu hmin w hs hw hrep hweak hae v hvc hvw hvK q hq
  obtain ⟨qn, τn, hqn, hτn, hqnTrace, hqnUniform, hτnUniform, hqnEnergy, hhi⟩ :=
    exists_weakly_monotone_disks_tendsto_energy_of_weak_representative
      g hΦ hN hr hΦN hleft γ hΓ w hw v hvc hvw hvK q hq τ hτ hτ0 hτ1 hτ2 htrace
  exact le_antisymm hlo hhi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskEnergy_eq_inf_of_minimizing_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskEnergy_eq_inf_of_minimizing_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskEnergy_eq_inf_of_minimizing_sequence ``Submission.DifferentialGeometry.Geometry.riemannianDiskEnergy_eq_inf_of_minimizing_sequence

theorem radialDiskEnergyFirstVariation_eq_zero_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N)
    (hΦN : _root_.Set.range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
      (𝓝 (_root_.InfSet.sInf ((fun p : C(closedDisk, M) => riemannianDiskEnergy g p) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (w : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[μ]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : _root_.MeasureTheory.Lp V 2 μ),
      _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) _root_.Filter.atTop
        (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (hae : ∀ᵐ x ∂μ,
      _root_.Filter.Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        _root_.Filter.atTop (𝓝 (w x)))
    (v : V → F) (hvc : ContDiffOn ℝ 1 v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[μ] w) (hvK : _root_.Set.MapsTo v (Metric.ball (0 : V) 1) (_root_.Set.range Φ))
    (q : C(closedDisk, M))
    (hq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      diskExtension q z = r (v (Complex.orthonormalBasisOneI.repr z)))
    {KΓ : ℝ≥0} (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (τ : C(loopCircle, loopCircle)) (hτ : IsWeaklyMonotoneOnce τ)
    (hτ0 : τ 0 = 0) (hτ1 : τ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle))
    (hτ2 : τ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle))
    (htrace : diskTrace q = γ.comp τ)
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : Differentiable ℝ ψ)
    (hψLip : LipschitzWith C ψ) (hper : Function.Periodic ψ 1) :
    radialDiskEnergyFirstVariation g q ψ = 0 := by
  have he := riemannianDiskEnergy_eq_inf_of_minimizing_sequence
    g hΦ hN hr hΦN hleft u hu hmin w hs hw hrep hweak hae v hvc hvw hvK q hq
    hΓ τ hτ hτ0 hτ1 hτ2 htrace
  exact radialDiskEnergyFirstVariation_eq_zero_of_energy_attainment
    g (hΦ.of_le (by simp)) hN (hr.of_le (by simp)) hΦN hleft
    u hu hmin w hs hw hrep hweak hae v hvc hvw hvK q hq he hψ hψLip hper

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.radialDiskEnergyFirstVariation_eq_zero_of_minimizing_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.radialDiskEnergyFirstVariation_eq_zero_of_minimizing_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.radialDiskEnergyFirstVariation_eq_zero_of_minimizing_sequence ``Submission.DifferentialGeometry.Geometry.radialDiskEnergyFirstVariation_eq_zero_of_minimizing_sequence

end DifferentialGeometry.Geometry

end
