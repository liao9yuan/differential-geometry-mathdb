import Submission.DifferentialGeometry.Analysis.Integration.Lp.Composition
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Mollification
import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.BoundedDerivative
import Submission.DifferentialGeometry.Analysis.Integration.Lp.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Finite ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem weakGrad_eq_fderiv_retraction_of_strong_approximation
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (r : F → F) (u : ℕ → E → F)
    (hu : ∀ n i, ContDiffOn ℝ 1 (fun x => r (u n x) i) Ω)
    (hum : ∀ n i, _root_.MeasureTheory.MemLp (fun x => r (u n x) i) 2 (volume.restrict Ω))
    (hud : ∀ n i j, _root_.MeasureTheory.MemLp (fun x =>
      fderiv ℝ (fun y => r (u n y) i) x (EuclideanSpace.single j 1)) 2
      (volume.restrict Ω))
    (hlim : ∀ i, _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => r (u n x) i - f x i) 2
      (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0))
    (hG : ∀ i j, _root_.MeasureTheory.MemLp (fun x =>
      (fderiv ℝ r (f x) (WithLp.toLp 2 (fun k => (hf k).weakGrad x j))) i)
      2 (volume.restrict Ω))
    (hdlim : ∀ i j, _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
      fderiv ℝ (fun y => r (u n y) i) x (EuclideanSpace.single j 1) -
        (fderiv ℝ r (f x) (WithLp.toLp 2 (fun k => (hf k).weakGrad x j))) i)
      2 (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0)) :
    ∀ j, (fun x => fderiv ℝ r (f x) (WithLp.toLp 2 (fun k => (hf k).weakGrad x j)))
      =ᵐ[volume.restrict Ω] (fun x => WithLp.toLp 2 (fun k => (hf k).weakGrad x j)) := by
  intro j
  have hweak (i : ι) : DeGiorgi.HasWeakPartialDeriv j
      (fun x => (fderiv ℝ r (f x) (WithLp.toLp 2 (fun k => (hf k).weakGrad x j))) i)
      (fun x => f x i) Ω :=
    hasWeakPartialDeriv_of_tendsto_eLpNorm (by norm_num) j (fun n => hum n i)
      (fun n => hud n i j) (hf i).memLp (hG i j)
      (fun n => hasWeakPartialDeriv_of_contDiffOn hΩ (hu n i) j) (hlim i) (hdlim i j)
  have heq (i : ι) : (fun x =>
      (fderiv ℝ r (f x) (WithLp.toLp 2 (fun k => (hf k).weakGrad x j))) i)
      =ᵐ[volume.restrict Ω] (fun x => (hf i).weakGrad x j) :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ (hweak i) ((hf i).isWeakGrad j)
      ((hG i j).locallyIntegrable (by norm_num))
      (((hf i).weakGrad_component_memLp j).locallyIntegrable (by norm_num))
  filter_upwards [ae_all_iff.mpr heq] with x hx
  exact PiLp.ext hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.weakGrad_eq_fderiv_retraction_of_strong_approximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.weakGrad_eq_fderiv_retraction_of_strong_approximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.weakGrad_eq_fderiv_retraction_of_strong_approximation ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.weakGrad_eq_fderiv_retraction_of_strong_approximation

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem weakGrad_fixed_by_fderiv_of_contDiff_fixed_approximation
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (r : F → F) (hr : ContDiff ℝ 1 r) {C : ℝ} (hC : ∀ y, ‖fderiv ℝ r y‖ ≤ C)
    (u : ℕ → E → F) (hu : ∀ n, ContDiff ℝ 1 (u n))
    (humeas : ∀ n i, _root_.MeasureTheory.MemLp (fun x => r (u n x) i) 2 (volume.restrict Ω))
    (hudmeas : ∀ n i j, _root_.MeasureTheory.MemLp (fun x =>
      fderiv ℝ (fun y => r (u n y) i) x (EuclideanSpace.single j 1)) 2
      (volume.restrict Ω))
    (hdu : ∀ n j, _root_.MeasureTheory.MemLp (fun x => fderiv ℝ (u n) x (EuclideanSpace.single j 1))
      2 (volume.restrict Ω))
    (hval : ∀ i, _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => r (u n x) i - f x i) 2
      (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict Ω, _root_.Filter.Tendsto (fun n => u n x) _root_.Filter.atTop (𝓝 (f x)))
    (hder : ∀ j, _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
      fderiv ℝ (u n) x (EuclideanSpace.single j 1) -
        WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) 2 (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0)) :
    ∀ j, (fun x => fderiv ℝ r (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)))
      =ᵐ[volume.restrict Ω] (fun x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) := by
  let G (j : Fin d) (x : E) : F := WithLp.toLp 2 (fun i => (hf i).weakGrad x j)
  have hG (j : Fin d) : _root_.MeasureTheory.MemLp (G j) 2 (volume.restrict Ω) :=
    MemLp.of_eval_piLp fun i => (hf i).weakGrad_component_memLp j
  have hfm : _root_.MeasureTheory.MemLp f 2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hf i).memLp
  have hA : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (fun x => fderiv ℝ r (u n x)) (volume.restrict Ω) :=
    fun n => ((hr.continuous_fderiv one_ne_zero).comp (hu n).continuous).aestronglyMeasurable
  have hAr : ∀ᵐ x ∂volume.restrict Ω, _root_.Filter.Tendsto (fun n => fderiv ℝ r (u n x)) _root_.Filter.atTop
      (𝓝 (fderiv ℝ r (f x))) :=
    hae.mono fun x hx => ((hr.continuous_fderiv one_ne_zero).tendsto (f x)).comp hx
  have htarget (j : Fin d) : _root_.MeasureTheory.MemLp (fun x => fderiv ℝ r (f x) (G j x)) 2
      (volume.restrict Ω) :=
    MemLp.clm_apply_of_ae_norm_le
      ((hr.continuous_fderiv one_ne_zero).comp_aestronglyMeasurable hfm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => hC (f x)) (hG j)
  apply weakGrad_eq_fderiv_retraction_of_strong_approximation hΩ hf r u
    (fun n i => by
      have h : ContDiff ℝ 1 ((EuclideanSpace.proj i : F →L[ℝ] ℝ) ∘ r ∘ u n) :=
        (EuclideanSpace.proj i : F →L[ℝ] ℝ).contDiff.comp (hr.comp (hu n))
      exact h.contDiffOn)
    humeas hudmeas hval (fun i j => (htarget j).eval_piLp i)
  intro i j
  exact MeasureTheory.tendsto_eLpNorm_fderiv_comp_coordinate_of_ae_tendsto u f r hu hr j (G j)
    hA (fun n => Filter.Eventually.of_forall fun x => hC (u n x)) hAr (fun n => hdu n j)
    (hG j) (hder j) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.weakGrad_fixed_by_fderiv_of_contDiff_fixed_approximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.weakGrad_fixed_by_fderiv_of_contDiff_fixed_approximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.weakGrad_fixed_by_fderiv_of_contDiff_fixed_approximation ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.weakGrad_fixed_by_fderiv_of_contDiff_fixed_approximation

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.ContinuousLinearMap
open scoped _root_.ContDiff _root_.Topology _root_.ENNReal _root_.Convolution _root_.NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem weakGrad_fixed_by_fderiv_retraction_on_ball
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (r : F → F) (hr : ContDiffOn ℝ ∞ r U) (hfix : ∀ y ∈ K, r y = y)
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    {c : E} {a : ℝ} (hball : Metric.closedBall c a ⊆ Ω) :
    ∀ j, (fun x => fderiv ℝ r (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)))
      =ᵐ[volume.restrict (Metric.ball c a)]
        (fun x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) := by
  obtain ⟨R, hR, hRc, hfixR, hDR, C, _, hC⟩ :=
    exists_contDiff_extension_eq_fixed_on_compact hK hU hKU r hr hfix
  let S := Metric.closedBall c a
  let B := Metric.ball c a
  have hBΩ : B ⊆ Ω := Metric.ball_subset_closedBall.trans hball
  let hb (i : ι) := (hf i).restrict Metric.isOpen_ball hBΩ
  have hfm : _root_.MeasureTheory.MemLp f 2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hf i).memLp
  have hglobal : _root_.MeasureTheory.LocallyIntegrable (Ω.indicator f) volume :=
    ((_root_.MeasureTheory.memLp_indicator_iff_restrict hΩ.measurableSet).mpr hfm).locallyIntegrable (by norm_num)
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε0 : _root_.Filter.Tendsto ε _root_.Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let φ (n : ℕ) := mollifierBumpEps (d := d) (hε n)
  let v (n : ℕ) := (φ n).normed _root_.MeasureTheory.MeasureSpace.volume ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] (Ω.indicator f)
  have hv (n : ℕ) : ContDiff ℝ ∞ (v n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left
      (_root_.ContinuousLinearMap.lsmul ℝ ℝ) (φ n).contDiff_normed hglobal
  have hval : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => v n x - f x) 2
      (volume.restrict B)) _root_.Filter.atTop (𝓝 0) :=
    tendsto_eLpNorm_normed_convolution_indicator_sub hΩ.measurableSet hBΩ hfm hε hε0
  have hae : ∀ᵐ x ∂volume.restrict B, _root_.Filter.Tendsto (fun n => v n x) _root_.Filter.atTop (𝓝 (f x)) := by
    have hφ0 : _root_.Filter.Tendsto (fun n => (φ n).rOut) _root_.Filter.atTop (𝓝 0) := hε0
    have hratio : ∀ᶠ n in _root_.Filter.atTop, (φ n).rOut ≤ 2 * (φ n).rIn :=
      Filter.Eventually.of_forall fun n => by dsimp [φ, mollifierBumpEps]; linarith
    have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := _root_.MeasureTheory.MeasureSpace.volume) hφ0 hratio hglobal
    filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae (s := B) h, _root_.MeasureTheory.ae_restrict_mem Metric.isOpen_ball.measurableSet]
      with x hx hxB
    simpa only [Set.indicator_of_mem (hBΩ hxB) f] using hx
  have hfixed : (fun x => R (f x)) =ᵐ[volume.restrict B] f := by
    have hfk : ∀ᵐ x ∂volume.restrict B, f x ∈ K :=
      _root_.MeasureTheory.ae_mono (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hBΩ) hfK
    exact hfk.mono fun x hx => hfixR _ hx
  obtain ⟨L, hL⟩ := hR.lipschitzWith_of_hasCompactSupport hRc (by simp)
  have hRval := hL.tendsto_eLpNorm_comp_sub_of_fixed_ae v f hfixed hval
  have hRv (n : ℕ) (i : ι) : ContDiff ℝ ∞ (fun x => R (v n x) i) := by
    exact (EuclideanSpace.proj i : F →L[ℝ] ℝ).contDiff.comp (hR.comp (hv n))
  have hum (n : ℕ) (i : ι) : _root_.MeasureTheory.MemLp (fun x => R (v n x) i) 2 (volume.restrict B) :=
    ((hRv n i).continuous.continuousOn.memLp_restrict_compact (_root_.ProperSpace.isCompact_closedBall c a) 2).mono_measure
      (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume Metric.ball_subset_closedBall)
  have hud (n : ℕ) (i : ι) (j : Fin d) : _root_.MeasureTheory.MemLp (fun x =>
      fderiv ℝ (fun y => R (v n y) i) x (EuclideanSpace.single j 1)) 2 (volume.restrict B) :=
    ((((hRv n i).continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn.memLp_restrict_compact
      (_root_.ProperSpace.isCompact_closedBall c a) 2).mono_measure
        (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume Metric.ball_subset_closedBall)
  have hdu (n : ℕ) (j : Fin d) : _root_.MeasureTheory.MemLp (fun x => fderiv ℝ (v n) x
      (EuclideanSpace.single j 1)) 2 (volume.restrict B) :=
    (memLp_fderiv_normed_convolution_apply_on_compact (_root_.ProperSpace.isCompact_closedBall c a)
      (φ n) hglobal (EuclideanSpace.single j 1) 2).mono_measure
        (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume Metric.ball_subset_closedBall)
  have hvalc (i : ι) : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => R (v n x) i - f x i)
      2 (volume.restrict B)) _root_.Filter.atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRval (fun _ => zero_le)
    intro n
    exact _root_.MeasureTheory.eLpNorm_mono_ae (Filter.Eventually.of_forall fun x =>
      PiLp.norm_apply_le (R (v n x) - f x) i)
  have hder (j : Fin d) : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
      fderiv ℝ (v n) x (EuclideanSpace.single j 1) -
        WithLp.toLp 2 (fun i => (hb i).weakGrad x j)) 2 (volume.restrict B)) _root_.Filter.atTop (𝓝 0) := by
    have h := tendsto_eLpNorm_partial_normed_convolution_indicator_sub_weakGrad
      hΩ (_root_.ProperSpace.isCompact_closedBall c a) hball hf hε hε0 j
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    intro n
    exact _root_.MeasureTheory.eLpNorm_mono_measure _ (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume Metric.ball_subset_closedBall)
  have ht := weakGrad_fixed_by_fderiv_of_contDiff_fixed_approximation Metric.isOpen_ball hb R
    (hR.of_le (by simp)) hC v (fun n => (hv n).of_le (by simp)) hum hud hdu hvalc hae hder
  intro j
  filter_upwards [ht j, _root_.MeasureTheory.ae_mono (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hBΩ) hfK] with x hx hxK
  rw [← hDR _ hxK]
  exact hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.weakGrad_fixed_by_fderiv_retraction_on_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.weakGrad_fixed_by_fderiv_retraction_on_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.weakGrad_fixed_by_fderiv_retraction_on_ball ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.weakGrad_fixed_by_fderiv_retraction_on_ball

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
