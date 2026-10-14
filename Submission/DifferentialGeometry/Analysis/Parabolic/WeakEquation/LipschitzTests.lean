import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.LinearEquivApproximation
import Submission.DifferentialGeometry.Analysis.Integration.Lp.BoundedLinearPairing
import Submission.DifferentialGeometry.Topology.LipschitzSupport
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

variable {d : ℕ}

theorem integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests_of_measurePreserving
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] {μ : _root_.MeasureTheory.Measure X}
    (e : X ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (he : _root_.MeasureTheory.MeasurePreserving e μ _root_.MeasureTheory.MeasureSpace.volume)
    {Ω : Set X} (hΩ : IsOpen Ω)
    (b : X → (X →L[ℝ] ℝ) →L[ℝ] ℝ) (c : X → ℝ)
    (hb : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun x => b x v) (μ.restrict Ω))
    (hc : _root_.MeasureTheory.AEStronglyMeasurable c (μ.restrict Ω))
    (hbound : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∃ M N : ℝ,
      (∀ᵐ x ∂μ.restrict K, ‖b x‖ ≤ M) ∧
      (∀ᵐ x ∂μ.restrict K, ‖c x‖ ≤ N))
    (hweak : ∀ φ : X → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∀ x, 0 ≤ φ x) →
        0 ≤ ∫ x, b x (fderiv ℝ φ x) + c x * φ x ∂μ)
    {u : X → ℝ} (hu : LocallyLipschitzOn Ω u) (huc : HasCompactSupport u)
    (husupport : tsupport u ⊆ Ω) (hunonneg : ∀ x, 0 ≤ u x) :
    _root_.MeasureTheory.Integrable (fun x => b x (fderiv ℝ u x) + c x * u x) μ ∧
      0 ≤ ∫ x, b x (fderiv ℝ u x) + c x * u x ∂μ := by
  obtain ⟨K, hK, hKΩ, huK, huInt, hduInt, v, hv, hlim, hdlim⟩ :=
    Sobolev.exists_nonneg_smooth_compactSupport_approx_of_measurePreserving e he
      (hu.locallyLipschitz_of_tsupport_subset hΩ husupport) huc hunonneg hΩ husupport
  obtain ⟨M, N, hM, hN⟩ := hbound K hK hKΩ
  have hbK (w : X →L[ℝ] ℝ) : _root_.MeasureTheory.AEStronglyMeasurable (fun x => b x w) (μ.restrict K) :=
    (hb w).mono_measure (Measure.restrict_mono hKΩ le_rfl)
  have hcK : _root_.MeasureTheory.AEStronglyMeasurable c (μ.restrict K) :=
    hc.mono_measure (Measure.restrict_mono hKΩ le_rfl)
  have hzero {f : X → ℝ} (hfK : tsupport f ⊆ K) (x : X) (hx : x ∉ K) :
      b x (fderiv ℝ f x) + c x * f x = 0 := by
    have hxs : x ∉ tsupport f := fun h => hx (hfK h)
    rw [fderiv_of_notMem_tsupport ℝ hxs, image_eq_zero_of_notMem_tsupport hxs,
      map_zero, _root_.MulZeroClass.mul_zero, add_zero]
  have hrestrict {f : X → ℝ} (hfK : tsupport f ⊆ K) :
      (∫ x in K, b x (fderiv ℝ f x) + c x * f x ∂μ) =
        ∫ x, b x (fderiv ℝ f x) + c x * f x ∂μ :=
    _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (hzero hfK)
  have huIntK : _root_.MeasureTheory.Integrable u (μ.restrict K) := huInt.mono_measure Measure.restrict_le_self
  have hduIntK : _root_.MeasureTheory.Integrable (fderiv ℝ u) (μ.restrict K) :=
    hduInt.mono_measure Measure.restrict_le_self
  have hresIntK : _root_.MeasureTheory.Integrable (fun x => b x (fderiv ℝ u x) + c x * u x)
      (μ.restrict K) :=
    (integrable_clm_apply_of_ae_norm_le b hbK hM hduIntK).add (huIntK.bdd_mul hcK hN)
  have hresInt : _root_.MeasureTheory.Integrable (fun x => b x (fderiv ℝ u x) + c x * u x) μ :=
    (_root_.MeasureTheory.integrableOn_iff_integrable_of_support_subset
      (Function.support_subset_iff'.mpr (hzero huK))).mp hresIntK
  have hvInt (n : ℕ) : _root_.MeasureTheory.Integrable (v n) (μ.restrict K) :=
    (hv n).2.2.2.1.mono_measure Measure.restrict_le_self
  have hdvInt (n : ℕ) : _root_.MeasureTheory.Integrable (fderiv ℝ (v n)) (μ.restrict K) :=
    (hv n).2.2.2.2.mono_measure Measure.restrict_le_self
  have hlimK : _root_.Filter.Tendsto (fun n => ∫ x in K, ‖v n x - u x‖ ∂μ) _root_.Filter.atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => _root_.MeasureTheory.integral_nonneg fun _ => norm_nonneg _) _ hlim
    intro n
    exact _root_.MeasureTheory.integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun _ => norm_nonneg _) (((hv n).2.2.2.1.sub huInt).norm)
  have hdlimK : _root_.Filter.Tendsto
      (fun n => ∫ x in K, ‖fderiv ℝ (v n) x - fderiv ℝ u x‖ ∂μ) _root_.Filter.atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => _root_.MeasureTheory.integral_nonneg fun _ => norm_nonneg _) _ hdlim
    intro n
    exact _root_.MeasureTheory.integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun _ => norm_nonneg _) (((hv n).2.2.2.2.sub hduInt).norm)
  have hnonneg : ∀ᶠ n in _root_.Filter.atTop, 0 ≤ ∫ x in K, b x (fderiv ℝ (v n) x) + c x * v n x ∂μ := by
    apply Eventually.of_forall
    intro n
    rw [hrestrict (hv n).2.1]
    exact hweak (v n) (hv n).1 (hK.of_isClosed_subset (isClosed_tsupport _) (hv n).2.1)
      ((hv n).2.1.trans hKΩ) (hv n).2.2.1
  refine ⟨hresInt, ?_⟩
  rw [← hrestrict huK]
  exact integral_clm_apply_add_mul_nonneg_of_tendsto_integral_norm_sub b c hbK hcK hM hN
    (Eventually.of_forall hdvInt) hduIntK (Eventually.of_forall hvInt) huIntK
    hdlimK hlimK hnonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests_of_measurePreserving then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests_of_measurePreserving"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests_of_measurePreserving ``Submission.DifferentialGeometry.Analysis.integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests_of_measurePreserving

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests
    {Ω : Set E} (hΩ : IsOpen Ω)
    (b : E → (E →L[ℝ] ℝ) →L[ℝ] ℝ) (c : E → ℝ)
    (hb : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun x => b x v) (volume.restrict Ω))
    (hc : _root_.MeasureTheory.AEStronglyMeasurable c (volume.restrict Ω))
    (hbound : ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ M N : ℝ,
      (∀ᵐ x ∂volume.restrict K, ‖b x‖ ≤ M) ∧
      (∀ᵐ x ∂volume.restrict K, ‖c x‖ ≤ N))
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∀ x, 0 ≤ φ x) →
        0 ≤ ∫ x, b x (fderiv ℝ φ x) + c x * φ x)
    {u : E → ℝ} (hu : LocallyLipschitzOn Ω u) (huc : HasCompactSupport u)
    (husupport : tsupport u ⊆ Ω) (hunonneg : ∀ x, 0 ≤ u x) :
    _root_.MeasureTheory.Integrable (fun x => b x (fderiv ℝ u x) + c x * u x) _root_.MeasureTheory.MeasureSpace.volume ∧
      0 ≤ ∫ x, b x (fderiv ℝ u x) + c x * u x := by
  exact integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests_of_measurePreserving
    (ContinuousLinearEquiv.refl ℝ E) (MeasurePreserving.id _root_.MeasureTheory.MeasureSpace.volume) hΩ b c hb hc hbound
    hweak hu huc husupport hunonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests ``Submission.DifferentialGeometry.Analysis.integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]

private local instance _root_.Submission.DifferentialGeometry.Analysis.instNormedSpaceReal_differentialGeometry : NormedSpace ℝ Y := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.instNormedSpaceReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.instNormedSpaceReal_differentialGeometry target :: scope.openDecls } }

theorem integrable_and_integral_fderiv_add_mul_nonneg_on_prod_of_smooth_tests
    {Ω : Set (ℝ × Y)} (hΩ : IsOpen Ω)
    (b : (ℝ × Y) → ((ℝ × Y) →L[ℝ] ℝ) →L[ℝ] ℝ) (c : (ℝ × Y) → ℝ)
    (hb : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun x => b x v) ((volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict Ω))
    (hc : _root_.MeasureTheory.AEStronglyMeasurable c ((volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict Ω))
    (hbound : ∀ K : Set (ℝ × Y), IsCompact K → K ⊆ Ω → ∃ M N : ℝ,
      (∀ᵐ x ∂(volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict K, ‖b x‖ ≤ M) ∧
      (∀ᵐ x ∂(volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict K, ‖c x‖ ≤ N))
    (hweak : ∀ φ : (ℝ × Y) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∀ x, 0 ≤ φ x) →
        0 ≤ ∫ x, b x (fderiv ℝ φ x) + c x * φ x ∂volume.prod _root_.MeasureTheory.MeasureSpace.volume)
    {u : (ℝ × Y) → ℝ} (hu : LocallyLipschitzOn Ω u) (huc : HasCompactSupport u)
    (husupport : tsupport u ⊆ Ω) (hunonneg : ∀ x, 0 ≤ u x) :
    _root_.MeasureTheory.Integrable (fun x => b x (fderiv ℝ u x) + c x * u x) (volume.prod _root_.MeasureTheory.MeasureSpace.volume) ∧
      0 ≤ ∫ x, b x (fderiv ℝ u x) + c x * u x ∂volume.prod volume := by
  let e₁ : (ℝ × Y) ≃L[ℝ] WithLp 2 (ℝ × Y) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ Y).symm
  let basis := stdOrthonormalBasis ℝ (WithLp 2 (ℝ × Y))
  let e := e₁.trans basis.repr.toContinuousLinearEquiv
  have he : _root_.MeasureTheory.MeasurePreserving e (volume.prod _root_.MeasureTheory.MeasureSpace.volume) volume :=
    basis.measurePreserving_repr.comp (WithLp.volume_preserving_toLp ℝ Y)
  exact integrable_and_integral_fderiv_add_mul_nonneg_of_smooth_tests_of_measurePreserving
    e he hΩ b c hb hc hbound hweak hu huc husupport hunonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrable_and_integral_fderiv_add_mul_nonneg_on_prod_of_smooth_tests then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrable_and_integral_fderiv_add_mul_nonneg_on_prod_of_smooth_tests"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrable_and_integral_fderiv_add_mul_nonneg_on_prod_of_smooth_tests ``Submission.DifferentialGeometry.Analysis.integrable_and_integral_fderiv_add_mul_nonneg_on_prod_of_smooth_tests

end DifferentialGeometry.Analysis
