import Submission.DifferentialGeometry.Analysis.Integration.Lp.QuadraticResidual
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.Columns

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]

local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem tendsto_integral_weighted_gradient_pair_of_weak_of_energy_tendsto
    {Ω : Set V} (hΩ : MeasurableSet Ω) (f : ℕ → V → F) (v : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2 (fun x => f n x i) Ω)
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω)
    (L : ℕ → ℝ≥0) (hf : ∀ n, LipschitzWith (L n) (f n))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[volume.restrict Ω]
      (fun x => fderiv ℝ (fun y => f n y i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : _root_.MeasureTheory.Lp V 2 (volume.restrict Ω)),
      _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) _root_.Filter.atTop
        (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z)))
    {K : Set F} (hK : IsCompact K)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K)
    (hpos : ∀ y ∈ K, LinearMap.IsPosSemidef (A y).toBilinForm)
    (hfK : ∀ n, _root_.Set.MapsTo (f n) Ω K)
    (hvK : ∀ᵐ x ∂volume.restrict Ω, v x ∈ K)
    (hlim : ∀ᵐ x ∂volume.restrict Ω, _root_.Filter.Tendsto (fun n => f n x) _root_.Filter.atTop (𝓝 (v x)))
    (henergy : _root_.Filter.Tendsto (fun n => ∑ j : Fin d, ∫ x in Ω,
      A (f n x) (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
        (fderiv ℝ (f n) x (EuclideanSpace.single j 1))) _root_.Filter.atTop
      (𝓝 (∑ j : Fin d, ∫ x in Ω,
        A (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x j)))))
    (c : V → ℝ) (hcm : _root_.MeasureTheory.AEStronglyMeasurable c (volume.restrict Ω)) {D : ℝ≥0}
    (hc : ∀ᵐ x ∂volume.restrict Ω, |c x| ≤ D) (j k : Fin d) :
    _root_.Filter.Tendsto (fun n => ∫ x in Ω,
      c x * A (f n x) (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
        (fderiv ℝ (f n) x (EuclideanSpace.single k 1))) _root_.Filter.atTop
      (𝓝 (∫ x in Ω, c x * A (v x)
        (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hv i).weakGrad x k)))) := by
  classical
  obtain ⟨u, u₀, hu, hu₀, hweak'⟩ :=
    exists_lp_gradient_columns_of_tendsto_inner f v hs hv L hf hrep hweak
  have hm : Measurable (K.piecewise A 0) :=
    hA.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
  have hBm (n : ℕ) : _root_.MeasureTheory.AEStronglyMeasurable (fun x => A (f n x)) (volume.restrict Ω) := by
    have h : _root_.MeasureTheory.AEStronglyMeasurable (K.piecewise A 0 ∘ f n) (volume.restrict Ω) :=
      (hm.comp (hf n).continuous.measurable).aestronglyMeasurable
    apply h.congr
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hΩ] with x hx
    exact Set.piecewise_eq_of_mem K A 0 (hfK n hx)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hA
  have hBC (n : ℕ) : ∀ᵐ x ∂volume.restrict Ω, ‖A (f n x)‖ ≤ C := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hΩ] with x hx
    exact hC _ (hfK n hx)
  have hBpos (n : ℕ) : ∀ᵐ x ∂volume.restrict Ω,
      LinearMap.IsPosSemidef (A (f n x)).toBilinForm := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hΩ] with x hx
    exact hpos _ (hfK n hx)
  have hBlim : ∀ᵐ x ∂volume.restrict Ω,
      Tendsto (fun n => A (f n x)) _root_.Filter.atTop (𝓝 (A (v x))) := by
    filter_upwards [hlim, hvK, _root_.MeasureTheory.ae_restrict_mem hΩ] with x hx hxK hxΩ
    exact (hA (v x) hxK).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hx, Eventually.of_forall (fun n => hfK n hxΩ)⟩)
  have heq (n : ℕ) (j k : Fin d) (c : V → ℝ) :
      (∫ x in Ω, c x * A (f n x) (u j n x) (u k n x)) =
        ∫ x in Ω, c x * A (f n x)
          (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
          (fderiv ℝ (f n) x (EuclideanSpace.single k 1)) := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hu j n, hu k n] with x hj hk
    rw [hj, hk]
  have heq₀ (j k : Fin d) (c : V → ℝ) :
      (∫ x in Ω, c x * A (v x) (u₀ j x) (u₀ k x)) =
        ∫ x in Ω, c x * A (v x)
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x k)) := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hu₀ j, hu₀ k] with x hj hk
    rw [hj, hk]
  have he (n : ℕ) (j : Fin d) := heq n j j (fun _ => 1)
  have he₀ (j : Fin d) := heq₀ j j (fun _ => 1)
  simp only [one_mul] at he he₀
  have henergy' : _root_.Filter.Tendsto (fun n => ∑ j : Fin d, ∫ x in Ω,
      A (f n x) (u j n x) (u j n x)) _root_.Filter.atTop
      (𝓝 (∑ j : Fin d, ∫ x in Ω, A (v x) (u₀ j x) (u₀ j x))) := by
    simpa only [he, he₀] using henergy
  have ht := tendsto_integral_weighted_bilinear_of_weak_of_sum_energy_tendsto
    (fun n x => A (f n x)) (fun x => A (v x)) hBm C hBC hBlim hBpos u u₀ hweak'
    henergy' c hcm hc j k
  simpa only [heq, heq₀] using ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.tendsto_integral_weighted_gradient_pair_of_weak_of_energy_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.tendsto_integral_weighted_gradient_pair_of_weak_of_energy_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.tendsto_integral_weighted_gradient_pair_of_weak_of_energy_tendsto ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.tendsto_integral_weighted_gradient_pair_of_weak_of_energy_tendsto

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
