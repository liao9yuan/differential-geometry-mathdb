import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import Submission.DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem integral_smul_weak_partial_eq
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {φ : E → ℝ}
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    {v : E → ℝ}
    {w : Fin d → E → ℝ}
    (hv_localMemLp : ∀ K : Set E, IsCompact K → K ⊆ Ω →
      MeasureTheory.MemLp v 2
        ((MeasureTheory.volume : MeasureTheory.Measure E).restrict K))
    (hw_localMemLp : ∀ (j : Fin d) (K : Set E), IsCompact K → K ⊆ Ω →
      MeasureTheory.MemLp (w j) 2
        ((MeasureTheory.volume : MeasureTheory.Measure E).restrict K))
    (hw_isWeakPartial : ∀ j : Fin d,
      DeGiorgi.HasWeakPartialDeriv (d := d) j (w j) v Ω)
    (j : Fin d)
    {ψ : E → ℝ}
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ Ω) :
    (∫ y in Ω, φ y * v y *
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
      ∂(MeasureTheory.volume : MeasureTheory.Measure E))
    = -((∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single j 1) * v y * ψ y
        ∂(MeasureTheory.volume : MeasureTheory.Measure E))
      + (∫ y in Ω, φ y * w j y * ψ y
        ∂(MeasureTheory.volume : MeasureTheory.Measure E))) := by
  classical
  let _ := hΩ_open
  set K : Set E := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_meas : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
  have hK_sub : K ⊆ Ω := hψ_support
  set ξ : E → ℝ := fun y => φ y * ψ y with hξ_def
  have hξ_smooth : ContDiff ℝ (⊤ : ℕ∞) ξ := hφ_smooth.mul hψ_smooth
  have hξ_cs : HasCompactSupport ξ := hψ_cs.mul_left
  have hξ_tsupport : tsupport ξ ⊆ K := by
    have h_sub_support : Function.support ξ ⊆ Function.support ψ := by
      intro y hy
      have : φ y * ψ y ≠ 0 := hy
      have : ψ y ≠ 0 := fun hψy => this (by simp [hψy])
      exact this
    have h_sub_tsupport : tsupport ξ ⊆ tsupport ψ :=
      closure_mono h_sub_support
    exact h_sub_tsupport
  have hξ_support : tsupport ξ ⊆ Ω := hξ_tsupport.trans hK_sub
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by simp)
  have hψ_diff : Differentiable ℝ ψ := hψ_smooth.differentiable (by simp)
  let ej : E := EuclideanSpace.single j (1 : ℝ)
  have hφ_cont : Continuous φ := hφ_smooth.continuous
  have hψ_cont : Continuous ψ := hψ_smooth.continuous
  have hφ_deriv_cont : Continuous (fun y : E => (fderiv ℝ φ y) ej) :=
    (hφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ_deriv_cont : Continuous (fun y : E => (fderiv ℝ ψ y) ej) :=
    (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have fderiv_prod : ∀ y : E, (fderiv ℝ ξ y) ej =
      (fderiv ℝ φ y) ej * ψ y + φ y * (fderiv ℝ ψ y) ej := by
    intro y
    have hfd :
        fderiv ℝ (fun z => φ z * ψ z) y =
          φ y • fderiv ℝ ψ y + ψ y • fderiv ℝ φ y :=
      fderiv_fun_mul hφ_diff.differentiableAt hψ_diff.differentiableAt
    have hξ_eq : (fderiv ℝ ξ y) ej = (fderiv ℝ (fun z => φ z * ψ z) y) ej := rfl
    rw [hξ_eq, hfd]
    simp [add_apply, smul_apply,
      smul_eq_mul]
    ring
  have key :
      ∫ y in Ω, v y * (fderiv ℝ ξ y) ej
        ∂(MeasureTheory.volume : MeasureTheory.Measure E) =
      -∫ y in Ω, w j y * ξ y
        ∂(MeasureTheory.volume : MeasureTheory.Measure E) := by
    simpa [ej] using hw_isWeakPartial j ξ hξ_smooth hξ_cs hξ_support
  have hvK_memLp : _root_.MeasureTheory.MemLp v 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict K) :=
    hv_localMemLp K hK_compact hK_sub
  have hwK_memLp : _root_.MeasureTheory.MemLp (w j) 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict K) :=
    hw_localMemLp j K hK_compact hK_sub
  have hvolK_finite : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) K < ∞ := hK_compact.measure_lt_top
  have hvolK_finite' : (volume.restrict K : _root_.MeasureTheory.Measure E) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hvolK_finite
  have : _root_.MeasureTheory.IsFiniteMeasure ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict K) := ⟨hvolK_finite'⟩
  have hv_int_K : _root_.MeasureTheory.IntegrableOn v K (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
    hvK_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hw_int_K : _root_.MeasureTheory.IntegrableOn (w j) K (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
    hwK_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have integrable_mul_compact :
      ∀ {h : E → ℝ}, Continuous h → tsupport h ⊆ K →
        Integrable (fun y => v y * h y) (volume.restrict Ω) := by
    intro h hh_cont hh_support
    have hh_contOn : ContinuousOn h K := hh_cont.continuousOn
    have step_K : _root_.MeasureTheory.IntegrableOn (fun y => v y * h y) K (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
      hv_int_K.mul_continuousOn hh_contOn hK_compact
    have h_vanish : ∀ y, y ∉ K → v y * h y = 0 := by
      intro y hy
      have : h y = 0 := image_eq_zero_of_notMem_tsupport
        (fun hy_support => hy (hh_support hy_support))
      simp [this]
    have h_eq_ind :
        (fun y => v y * h y) = K.indicator (fun y => v y * h y) := by
      funext y
      by_cases hy : y ∈ K
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy, h_vanish y hy]
    have ind_int : _root_.MeasureTheory.Integrable (K.indicator (fun y => v y * h y))
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
      (_root_.MeasureTheory.integrable_indicator_iff hK_meas).mpr step_K
    have full_int : _root_.MeasureTheory.Integrable (fun y => v y * h y) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
      rw [h_eq_ind]; exact ind_int
    exact full_int.restrict
  have integrable_mul_compact_w :
      ∀ {h : E → ℝ}, Continuous h → tsupport h ⊆ K →
        Integrable (fun y => w j y * h y) (volume.restrict Ω) := by
    intro h hh_cont hh_support
    have hh_contOn : ContinuousOn h K := hh_cont.continuousOn
    have step_K : _root_.MeasureTheory.IntegrableOn (fun y => w j y * h y) K (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
      hw_int_K.mul_continuousOn hh_contOn hK_compact
    have h_vanish : ∀ y, y ∉ K → w j y * h y = 0 := by
      intro y hy
      have : h y = 0 := image_eq_zero_of_notMem_tsupport
        (fun hy_support => hy (hh_support hy_support))
      simp [this]
    have h_eq_ind :
        (fun y => w j y * h y) = K.indicator (fun y => w j y * h y) := by
      funext y
      by_cases hy : y ∈ K
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy, h_vanish y hy]
    have ind_int : _root_.MeasureTheory.Integrable (K.indicator (fun y => w j y * h y))
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
      (_root_.MeasureTheory.integrable_indicator_iff hK_meas).mpr step_K
    have full_int : _root_.MeasureTheory.Integrable (fun y => w j y * h y) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
      rw [h_eq_ind]; exact ind_int
    exact full_int.restrict
  have h_dφ_ψ_cont : Continuous (fun y : E => (fderiv ℝ φ y) ej * ψ y) :=
    hφ_deriv_cont.mul hψ_cont
  have h_dφ_ψ_support : tsupport (fun y : E => (fderiv ℝ φ y) ej * ψ y) ⊆ K := by
    have h_sub : Function.support (fun y : E => (fderiv ℝ φ y) ej * ψ y) ⊆
        Function.support ψ := by
      intro y hy
      have : (fderiv ℝ φ y) ej * ψ y ≠ 0 := hy
      have : ψ y ≠ 0 := fun hψy => this (by simp [hψy])
      exact this
    exact closure_mono h_sub
  have h_φ_dψ_cont : Continuous (fun y : E => φ y * (fderiv ℝ ψ y) ej) :=
    hφ_cont.mul hψ_deriv_cont
  have h_φ_dψ_support : tsupport (fun y : E => φ y * (fderiv ℝ ψ y) ej) ⊆ K := by
    have h1 : Function.support (fun y : E => (fderiv ℝ ψ y) ej) ⊆
        tsupport ψ := by
      intro y hy
      by_contra hy'
      have hψeq : ψ =ᶠ[𝓝 y] 0 :=
        (isClosed_tsupport (f := ψ)).isOpen_compl.eventually_mem hy' |>.mono
          (fun z hz => image_eq_zero_of_notMem_tsupport hz)
      have hfderiv_eq : fderiv ℝ ψ y = fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
        Filter.EventuallyEq.fderiv_eq hψeq
      have hψfderiv_zero : fderiv ℝ ψ y = 0 := by
        rw [hfderiv_eq]
        exact fderiv_const_apply (0 : ℝ)
      have : (fderiv ℝ ψ y) ej = 0 := by simp [hψfderiv_zero]
      exact hy this
    have h2 : Function.support (fun y : E => φ y * (fderiv ℝ ψ y) ej) ⊆
        Function.support (fun y : E => (fderiv ℝ ψ y) ej) := by
      intro y hy
      have : φ y * (fderiv ℝ ψ y) ej ≠ 0 := hy
      have : (fderiv ℝ ψ y) ej ≠ 0 := fun h0 => this (by simp [h0])
      exact this
    have : tsupport (fun y : E => φ y * (fderiv ℝ ψ y) ej) ⊆
        tsupport (fun y : E => (fderiv ℝ ψ y) ej) := closure_mono h2
    have : tsupport (fun y : E => φ y * (fderiv ℝ ψ y) ej) ⊆ tsupport ψ :=
      this.trans (by
        exact (closure_mono h1).trans (by
          rw [closure_eq_iff_isClosed.mpr (isClosed_tsupport ψ)]))
    exact this
  have h_ψ_cont : Continuous ψ := hψ_cont
  have h_ψ_support : tsupport ψ ⊆ K := by rw [hK_def]
  have int_v_dφ_ψ :
      _root_.MeasureTheory.Integrable (fun y => v y * ((fderiv ℝ φ y) ej * ψ y))
        (volume.restrict Ω) :=
    integrable_mul_compact h_dφ_ψ_cont h_dφ_ψ_support
  have int_v_φ_dψ :
      _root_.MeasureTheory.Integrable (fun y => v y * (φ y * (fderiv ℝ ψ y) ej))
        (volume.restrict Ω) :=
    integrable_mul_compact h_φ_dψ_cont h_φ_dψ_support
  have int_w_ξ :
      Integrable (fun y => w j y * ξ y) (volume.restrict Ω) := by
    have h_ξ_cont : Continuous ξ := hφ_cont.mul hψ_cont
    exact integrable_mul_compact_w h_ξ_cont hξ_tsupport
  have key' :
      ∫ y in Ω, v y * ((fderiv ℝ φ y) ej * ψ y) +
        v y * (φ y * (fderiv ℝ ψ y) ej)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
      -∫ y in Ω, w j y * ξ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
    have eq1 :
        ∫ y in Ω, v y * (fderiv ℝ ξ y) ej ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
        ∫ y in Ω, v y * ((fderiv ℝ φ y) ej * ψ y) +
          v y * (φ y * (fderiv ℝ ψ y) ej) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
      refine _root_.MeasureTheory.integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun y => ?_)
      have := fderiv_prod y
      calc
        v y * (fderiv ℝ ξ y) ej
            = v y * ((fderiv ℝ φ y) ej * ψ y + φ y * (fderiv ℝ ψ y) ej) := by
              rw [this]
        _ = v y * ((fderiv ℝ φ y) ej * ψ y) + v y * (φ y * (fderiv ℝ ψ y) ej) := by
              ring
    rw [eq1] at key
    exact key
  rw [_root_.MeasureTheory.integral_add int_v_dφ_ψ int_v_φ_dψ] at key'
  have congr_lhs :
      (fun y => φ y * v y * (fderiv ℝ ψ y) ej) =
      (fun y => v y * (φ y * (fderiv ℝ ψ y) ej)) := by
    funext y; ring
  have congr_dφ_v_ψ :
      (fun y => (fderiv ℝ φ y) ej * v y * ψ y) =
      (fun y => v y * ((fderiv ℝ φ y) ej * ψ y)) := by
    funext y; ring
  have congr_φ_w_ψ :
      (fun y => φ y * w j y * ψ y) = (fun y => w j y * ξ y) := by
    funext y; simp [ξ]; ring
  change ∫ y in Ω, φ y * v y * (fderiv ℝ ψ y) ej ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
    -((∫ y in Ω, (fderiv ℝ φ y) ej * v y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
      + (∫ y in Ω, φ y * w j y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)))
  rw [show
      (fun y => φ y * v y * (fderiv ℝ ψ y) ej) =
      (fun y => v y * (φ y * (fderiv ℝ ψ y) ej)) from congr_lhs,
    show
      (fun y => (fderiv ℝ φ y) ej * v y * ψ y) =
      (fun y => v y * ((fderiv ℝ φ y) ej * ψ y)) from congr_dφ_v_ψ,
    show (fun y => φ y * w j y * ψ y) = (fun y => w j y * ξ y) from
      congr_φ_w_ψ]
  have h_extract :
      ∫ y in Ω, v y * (φ y * (fderiv ℝ ψ y) ej) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
      -(∫ y in Ω, w j y * ξ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) -
        ∫ y in Ω, v y * ((fderiv ℝ φ y) ej * ψ y) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
    linarith
  rw [h_extract]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smul_weak_partial_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smul_weak_partial_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smul_weak_partial_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smul_weak_partial_eq

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry

namespace DeGiorgi

open _root_.Metric

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem HasWeakPartialDeriv.mul_contDiffOn {Ω : Set E} (hΩ : IsOpen Ω)
    {i : Fin d} {g f η : E → ℝ}
    (hf : HasWeakPartialDeriv i g f Ω)
    (hη : ContDiffOn ℝ (⊤ : ℕ∞) η Ω)
    (hf_int : _root_.MeasureTheory.LocallyIntegrable f (volume.restrict Ω))
    (hg_int : _root_.MeasureTheory.LocallyIntegrable g (volume.restrict Ω)) :
    HasWeakPartialDeriv i
      (fun x => η x * g x + fderiv ℝ η x (EuclideanSpace.single i 1) * f x)
      (fun x => η x * f x) Ω := by
  intro φ hφ hφc hφs
  obtain ⟨δ, χ, hδ, _, hχ, hχc, _, hχone, hχs⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      hφc hΩ hφs
  let η' := fun x => χ x * η x
  have hη's : tsupport η' ⊆ Ω := (tsupport_mul_subset_left (f := χ) (g := η)).trans hχs
  have hη' : ContDiff ℝ (⊤ : ℕ∞) η' :=
    (hχ.contDiffOn.mul hη).contDiff_of_tsupport_subset hΩ hη's
  have hlocal : ∀ x ∈ tsupport φ, η' =ᶠ[𝓝 x] η := by
    intro x hx
    have hχloc : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [_root_.Metric.ball_mem_nhds x hδ] with y hy
      apply hχone
      exact _root_.Metric.closedBall_subset_cthickening hx δ (mem_closedBall.mpr (le_of_lt hy))
    filter_upwards [hχloc] with y hy
    change χ y * η y = η y
    rw [hy, one_mul]
  have htest := (hf.mul_smooth hΩ hη' hf_int hg_int) φ hφ hφc hφs
  have hl : (∫ x in Ω, η' x * f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ x in Ω, η x * f x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport φ
    · rw [(hlocal x hx).eq_of_nhds]
    · have hz : fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
          (fun hs => hx ((tsupport_fderiv_apply_subset (f := φ) ℝ (EuclideanSpace.single i 1)) hs))
      simp only [hz, _root_.MulZeroClass.mul_zero]
  have hr : (∫ x in Ω,
        (η' x * g x + fderiv ℝ η' x (EuclideanSpace.single i 1) * f x) * φ x) =
      ∫ x in Ω, (η x * g x + fderiv ℝ η x (EuclideanSpace.single i 1) * f x) * φ x := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport φ
    · rw [(hlocal x hx).eq_of_nhds, (hlocal x hx).fderiv_eq]
    · rw [image_eq_zero_of_notMem_tsupport hx, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero]
  exact hl.symm.trans (htest.trans (congrArg Neg.neg hr))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasWeakPartialDeriv.mul_contDiffOn then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasWeakPartialDeriv.mul_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasWeakPartialDeriv.mul_contDiffOn ``Submission.DeGiorgi.HasWeakPartialDeriv.mul_contDiffOn

end DeGiorgi
