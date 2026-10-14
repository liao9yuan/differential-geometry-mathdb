import Submission.DifferentialGeometry.Geometry.Geodesic.Maximal.Interval
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def curveEnergy (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b,
    g.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.curveEnergy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.curveEnergy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.curveEnergy ``Submission.DifferentialGeometry.Geometry.Riemannian.curveEnergy

theorem integrableOn_inner_mfderiv_self_of_contMDiffOn
    (g : SmoothRiemannianMetric I M) {gamma : ℝ → M} {a b : ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc a b)) :
    _root_.MeasureTheory.IntegrableOn (fun s => g.inner (gamma s)
      (mfderiv 𝓘(ℝ, ℝ) I gamma s (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I gamma s (1 : ℝ))) (_root_.Set.Icc a b) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · let v (s : ℝ) : TangentSpace I (gamma s) :=
      mfderivWithin 𝓘(ℝ, ℝ) I gamma (_root_.Set.Icc a b) s (1 : ℝ)
    have hu : UniqueMDiffOn 𝓘(ℝ, ℝ) (_root_.Set.Icc a b) :=
      (uniqueDiffOn_Icc hab).uniqueMDiffOn
    have hone : Continuous (fun s : ℝ =>
        (TotalSpace.mk' ℝ s (1 : ℝ) : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      ((contMDiff_vectorSpace_iff_contDiff (V := fun _ : ℝ => (1 : ℝ))).mpr
        (contDiff_const (n := 0))).continuous
    have hv : ContinuousOn (fun s => TotalSpace.mk' E (gamma s) (v s)) (_root_.Set.Icc a b) := by
      exact (hgamma.continuousOn_tangentMapWithin le_rfl hu).comp hone.continuousOn
        (fun s hs => hs)
    have hq : ContinuousOn (fun s => g.inner (gamma s) (v s) (v s)) (_root_.Set.Icc a b) := by
      have hc : ContinuousOn (fun s =>
          TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (gamma s)
            (g.inner (gamma s) (v s) (v s))) (_root_.Set.Icc a b) :=
        (g.contMDiff.continuous.comp_continuousOn hgamma.continuousOn).clm_bundle_apply₂
          (F₁ := E) (F₂ := E) hv hv
      intro s hs
      have hc' := hc s hs
      rw [FiberBundle.continuousWithinAt_totalSpace] at hc'
      exact hc'.2
    apply hq.integrableOn_compact _root_.CompactIccSpace.isCompact_Icc |>.congr
    rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with s hs
    dsimp only [v]
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]
  · simp
  · simp [_root_.Set.Icc_eq_empty_of_lt hba]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.integrableOn_inner_mfderiv_self_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.integrableOn_inner_mfderiv_self_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.integrableOn_inner_mfderiv_self_of_contMDiffOn ``Submission.DifferentialGeometry.Geometry.Riemannian.integrableOn_inner_mfderiv_self_of_contMDiffOn

theorem curveEnergy_mono (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    {a s t b : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hE : _root_.MeasureTheory.IntegrableOn (fun u =>
      g.inner (γ u)
        (mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ))) (Set.Icc a b)) :
    curveEnergy (I := I) g γ s t ≤ curveEnergy (I := I) g γ a b := by
  apply intervalIntegral.integral_mono_interval has hst htb
  · filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    let v := mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ)
    rcases eq_or_ne v 0 with hv | hv
    · simp only [v, hv, map_zero]
      exact le_rfl
    · exact (g.pos (γ u) v hv).le
  · apply MeasureTheory.IntegrableOn.intervalIntegrable
    simpa only [_root_.Set.uIcc_of_le (has.trans (hst.trans htb))] using hE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.curveEnergy_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.curveEnergy_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.curveEnergy_mono ``Submission.DifferentialGeometry.Geometry.Riemannian.curveEnergy_mono

private lemma int_sqrt_le {q : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hq0 : ∀ t ∈ Set.Icc a b, 0 ≤ q t)
    (hq : _root_.MeasureTheory.IntegrableOn q (Set.Icc a b)) :
    ∫ t in a..b, Real.sqrt (q t) ≤
      Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, q t) := by
  let μ : _root_.MeasureTheory.Measure ℝ := volume.restrict (Set.Ioc a b)
  have hqIoc : _root_.MeasureTheory.Integrable q μ := hq.mono_set Set.Ioc_subset_Icc_self
  have hqae : 0 ≤ᵐ[μ] q := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact hq0 t ⟨ht.1.le, ht.2⟩
  have hsqrt_meas : _root_.MeasureTheory.AEStronglyMeasurable (fun t => Real.sqrt (q t)) μ :=
    (hqIoc.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hsqrt_mem_two : _root_.MeasureTheory.MemLp (fun t => Real.sqrt (q t)) 2 μ := by
    rw [_root_.MeasureTheory.memLp_two_iff_integrable_sq hsqrt_meas]
    exact hqIoc.congr (hqae.mono fun t ht => (Real.sq_sqrt ht).symm)
  have hsqrt_mem : _root_.MeasureTheory.MemLp (fun t => Real.sqrt (q t)) (ENNReal.ofReal 2) μ := by
    norm_num at hsqrt_mem_two ⊢
    exact hsqrt_mem_two
  have hone_mem : _root_.MeasureTheory.MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    simpa using (_root_.MeasureTheory.memLp_const (p := (2 : ℝ≥0∞)) (1 : ℝ) :
      _root_.MeasureTheory.MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ)
  have hholder := _root_.MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (_root_.MeasureTheory.ae_of_all _ fun t => Real.sqrt_nonneg (q t))
    (_root_.MeasureTheory.ae_of_all _ fun _ => zero_le_one) hsqrt_mem hone_mem
  have hsquares : ∫ t, Real.sqrt (q t) ^ (2 : ℝ) ∂μ = ∫ t, q t ∂μ := by
    exact _root_.MeasureTheory.integral_congr_ae (hqae.mono fun t ht => by
      change Real.sqrt (q t) ^ (2 : ℝ) = q t
      rw [Real.rpow_two, Real.sq_sqrt ht])
  have hone : ∫ _ : ℝ, (1 : ℝ) ^ (2 : ℝ) ∂μ = b - a := by
    simp [μ, hab]
  rw [hsquares, hone, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  change ∫ t, Real.sqrt (q t) ∂μ ≤
    Real.sqrt (b - a) * Real.sqrt (∫ t, q t ∂μ)
  calc
    ∫ t, Real.sqrt (q t) ∂μ = ∫ t, Real.sqrt (q t) * 1 ∂μ := by simp
    _ ≤ Real.sqrt (∫ t, q t ∂μ) * Real.sqrt (b - a) := hholder
    _ = Real.sqrt (b - a) * Real.sqrt (∫ t, q t ∂μ) := mul_comm _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.int_sqrt_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.int_sqrt_le target :: scope.openDecls } }

theorem arcLength_le_energy (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b)
    (hE : _root_.MeasureTheory.IntegrableOn (fun t =>
      g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) (Set.Icc a b)) :
    Variation.arcLength (I := I) g γ a b ≤
      Real.sqrt (b - a) * Real.sqrt (curveEnergy (I := I) g γ a b) := by
  exact int_sqrt_le hab
    (fun t _ => by
      let v := mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)
      rcases eq_or_ne v 0 with hv | hv
      · simp only [v, hv, map_zero]
        exact le_rfl
      · exact (g.pos (γ t) v hv).le) hE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.arcLength_le_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.arcLength_le_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.arcLength_le_energy ``Submission.DifferentialGeometry.Geometry.Riemannian.arcLength_le_energy

theorem edistOf_le_energy (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc a b))
    (hE : _root_.MeasureTheory.IntegrableOn (fun t =>
      g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) (Set.Icc a b)) :
    riemannianEDistOf (I := I) g (γ a) (γ b) ≤
      ENNReal.ofReal
        (Real.sqrt (b - a) * Real.sqrt (curveEnergy (I := I) g γ a b)) := by
  let rb : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdist := Geodesic.riemannianEDist_le_arcLength (I := I) g hab hγ
    (fun t _ => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
  have hlength := arcLength_le_energy (I := I) g hab hE
  simpa only [riemannianEDistOf] using
    hdist.trans (ENNReal.ofReal_le_ofReal hlength)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.edistOf_le_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.edistOf_le_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.edistOf_le_energy ``Submission.DifferentialGeometry.Geometry.Riemannian.edistOf_le_energy

theorem edistOf_le_budget (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b C : ℝ}
    (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc a b))
    (hE : _root_.MeasureTheory.IntegrableOn (fun t =>
      g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) (Set.Icc a b))
    (hEC : curveEnergy (I := I) g γ a b ≤ C) :
    riemannianEDistOf (I := I) g (γ a) (γ b) ≤
      ENNReal.ofReal (Real.sqrt (b - a) * Real.sqrt C) := by
  refine (edistOf_le_energy (I := I) g hab hγ hE).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEC) (Real.sqrt_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.edistOf_le_budget then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.edistOf_le_budget"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.edistOf_le_budget ``Submission.DifferentialGeometry.Geometry.Riemannian.edistOf_le_budget

end Riemannian
end Geometry
end DifferentialGeometry
