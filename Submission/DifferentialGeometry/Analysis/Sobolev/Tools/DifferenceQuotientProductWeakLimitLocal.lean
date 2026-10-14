import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientProductWeakLimit
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientProductCutoff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Set
open scoped _root_.ENNReal _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "ν" => μ.prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry : MeasurableSpace E := WithLp.measurableSpace 2 (Fin d → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry target :: scope.openDecls } }

theorem exists_ae_hasWeakPartialDeriv_of_integral_sq_diffQuot_cutoff_le
    {η : E → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {Ω Ω' : Set E}, MeasurableSet Ω → IsOpen Ω' →
      (∀ x ∈ Ω', η x = 1) →
      ∀ {w : ℝ × E → ℝ}, _root_.MeasureTheory.MemLp w 2 (μ.prod (volume.restrict Ω)) →
      ∀ (k : Fin d) {C r : ℝ}, 0 < r → _root_.Metric.cthickening r (tsupport η) ⊆ Ω →
      (∀ h : ℝ, 0 < |h| → |h| ≤ r →
        (∫ t, ∫ x, (η x * diffQuot k h (fun y => w (t, y)) x)^2 ∂volume ∂μ) ≤ C) →
      ∃ v : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω')),
        ‖v‖ ≤ Real.sqrt C + L * (_root_.MeasureTheory.eLpNorm w 2 (μ.prod (volume.restrict Ω))).toReal ∧
        ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun x => v (t, x)) (fun x => w (t, x)) Ω' := by
  obtain ⟨L, hL, hcutoff⟩ := exists_cutoff_toLp_spatial_diffQuot_uniform_bound_on (μ := μ) hη hηc
  refine ⟨L, hL, ?_⟩
  intro Ω Ω' hΩ hΩ' hηone w hw k C r hr hroom hbound
  obtain ⟨u, hu, hub⟩ := hcutoff hΩ hw k hroom hbound
  have hconst : 0 ≤ Real.sqrt C + L * (_root_.MeasureTheory.eLpNorm w 2 (μ.prod (volume.restrict Ω))).toReal :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hL ENNReal.toReal_nonneg)
  obtain ⟨v, hv, hvweak⟩ := exists_ae_hasWeakPartialDeriv_of_spatial_diffQuot_uniform_bound
    u k hconst hr hub
  have hm : μ.prod (volume.restrict Ω') ≤ ν := Measure.prod_mono le_rfl Measure.restrict_le_self
  have hvlocal : _root_.MeasureTheory.MemLp v 2 (μ.prod (volume.restrict Ω')) := (Lp.memLp v).mono_measure hm
  let vlocal : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω')) := hvlocal.toLp v
  have heq : (vlocal : ℝ × E → ℝ) =ᵐ[μ.prod (volume.restrict Ω')] (v : ℝ × E → ℝ) := hvlocal.coeFn_toLp
  have hvnorm : ‖vlocal‖ ≤ ‖v‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (_root_.MeasureTheory.eLpNorm_mono_measure _ hm)
  refine ⟨vlocal, hvnorm.trans hv, ?_⟩
  filter_upwards [hvweak, Measure.ae_ae_of_ae_prod hu, Measure.ae_ae_of_ae_prod heq]
    with t ht htu htv
  have hweak := DeGiorgi.HasWeakPartialDeriv.restrict hΩ' (_root_.Set.subset_univ Ω') ht
  intro φ hφ hφc hφs
  have hi := hweak φ hφ hφc hφs
  have hsource : (fun x => u (t, x)) =ᵐ[volume.restrict Ω'] fun x => w (t, x) := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae htu, _root_.MeasureTheory.ae_restrict_mem hΩ'.measurableSet] with x hx hxΩ
    exact hx.trans (by rw [hηone x hxΩ, one_mul])
  have hl : (∫ x in Ω', u (t, x) * fderiv ℝ φ x (EuclideanSpace.single k 1)) =
      ∫ x in Ω', w (t, x) * fderiv ℝ φ x (EuclideanSpace.single k 1) := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hsource] with x hx
    rw [hx]
  have hrr : (∫ x in Ω', vlocal (t, x) * φ x) = ∫ x in Ω', v (t, x) * φ x := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [htv] with x hx
    rw [hx]
  exact hl.symm.trans (hi.trans (congrArg Neg.neg hrr.symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_ae_hasWeakPartialDeriv_of_integral_sq_diffQuot_cutoff_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_ae_hasWeakPartialDeriv_of_integral_sq_diffQuot_cutoff_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_ae_hasWeakPartialDeriv_of_integral_sq_diffQuot_cutoff_le ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_ae_hasWeakPartialDeriv_of_integral_sq_diffQuot_cutoff_le

end DifferentialGeometry.Analysis.Sobolev
