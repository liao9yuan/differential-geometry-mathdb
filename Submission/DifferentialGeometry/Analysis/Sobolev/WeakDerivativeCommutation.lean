import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import Submission.DifferentialGeometry.Analysis.Sobolev.WeakDerivativeUniqueness
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {μ : Measure E} {Ω : Set E}

omit [MeasurableSpace E] in
private theorem fderiv_fderiv_apply_comm
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w =
      fderiv ℝ (fun y => fderiv ℝ φ y w) x v := by
  have hc : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_cast)
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x := (hc.differentiable (by norm_num)) x
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  rw [fderiv_fun_const, fderiv_fun_const]
  simp only [add_apply, ContinuousLinearMap.comp_apply, Pi.zero_apply, zero_apply, map_zero, zero_add]
  exact hφ.contDiffAt.isSymmSndFDerivAt (by simpa only [minSmoothness_of_isRCLikeNormedField] using (show (2 : ℕ∞ω) ≤ (⊤ : ℕ∞) from by norm_cast)) w v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.fderiv_fderiv_apply_comm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.fderiv_fderiv_apply_comm target :: scope.openDecls } }

theorem integral_weak_deriv_fderiv_comm
    {U V R : E → ℝ} (v w : E)
    (hv : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, V x * φ x ∂μ)
    (hw : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x w ∂μ) = -∫ x, R x * φ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) :
    (∫ x, V x * fderiv ℝ φ x w ∂μ) = ∫ x, R x * fderiv ℝ φ x v ∂μ := by
  have hd (z : E) : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ φ x z) :=
    (hφ.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
  have h₁ := hv (fun x => fderiv ℝ φ x w) (hd w) (hφc.fderiv_apply ℝ w)
    ((tsupport_fderiv_apply_subset ℝ w).trans hφs)
  have h₂ := hw (fun x => fderiv ℝ φ x v) (hd v) (hφc.fderiv_apply ℝ v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hφs)
  apply neg_injective
  rw [← h₁, ← h₂]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [fderiv_fderiv_apply_comm hφ x w v]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_fderiv_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_fderiv_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_fderiv_comm ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_fderiv_comm


theorem integral_weak_deriv_divergence
    {ι : Type*} (s : Finset ι)
    (U W R DR : E → ℝ) (V H : ι → E → ℝ) (v w : E) (e : ι → E)
    (hU : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, W x * φ x ∂μ)
    (hV : ∀ i ∈ s, ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, V i x * fderiv ℝ φ x v ∂μ) = -∫ x, H i x * φ x ∂μ)
    (hR : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, R x * fderiv ℝ φ x v ∂μ) = -∫ x, DR x * φ x ∂μ)
    (hbase : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x w ∂μ) =
        (∑ i ∈ s, ∫ x, V i x * fderiv ℝ φ x (e i) ∂μ) - ∫ x, R x * φ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) :
    (∫ x, W x * fderiv ℝ φ x w ∂μ) =
      (∑ i ∈ s, ∫ x, H i x * fderiv ℝ φ x (e i) ∂μ) - ∫ x, DR x * φ x ∂μ := by
  have hd (z : E) : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ φ x z) :=
    (hφ.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
  have hc (z : E) : HasCompactSupport (fun x => fderiv ℝ φ x z) := hφc.fderiv_apply ℝ z
  have hs (z : E) : tsupport (fun x => fderiv ℝ φ x z) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ z).trans hφs
  have hu := hU (fun x => fderiv ℝ φ x w) (hd w) (hc w) (hs w)
  have hb := hbase (fun x => fderiv ℝ φ x v) (hd v) (hc v) (hs v)
  have hr := hR φ hφ hφc hφs
  have hucomm : (∫ x, U x * fderiv ℝ (fun y => fderiv ℝ φ y w) x v ∂μ) =
      ∫ x, U x * fderiv ℝ (fun y => fderiv ℝ φ y v) x w ∂μ := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    rw [fderiv_fderiv_apply_comm hφ x w v]
  have hflux (i : ι) (hi : i ∈ s) :
      (∫ x, V i x * fderiv ℝ (fun y => fderiv ℝ φ y v) x (e i) ∂μ) =
        -∫ x, H i x * fderiv ℝ φ x (e i) ∂μ := by
    have hiw := hV i hi (fun x => fderiv ℝ φ x (e i)) (hd (e i)) (hc (e i)) (hs (e i))
    convert hiw using 1
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    rw [fderiv_fderiv_apply_comm hφ x v (e i)]
  have hsum : (∑ i ∈ s, ∫ x, V i x * fderiv ℝ (fun y => fderiv ℝ φ y v) x (e i) ∂μ) =
      -(∑ i ∈ s, ∫ x, H i x * fderiv ℝ φ x (e i) ∂μ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hflux
  rw [hucomm, hb, hsum, hr] at hu
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_divergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_divergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_divergence ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_divergence

variable [OpensMeasurableSpace E]

omit [NormedSpace ℝ E] in
private theorem integrable_mul_continuousOn_mul_test
    (hΩ : IsOpen Ω) {U c φ : E → ℝ}
    (hU : _root_.MeasureTheory.LocallyIntegrable U μ) (hc : ContinuousOn c Ω)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    Integrable (fun x => c x * U x * φ x) μ := by
  have hcφ : Continuous (fun x => c x * φ x) :=
    (hc.mul hφ.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)
  convert hU.integrable_smul_right_of_hasCompactSupport hcφ hφc.mul_left using 1
  ext x
  simp only [smul_eq_mul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.integrable_mul_continuousOn_mul_test
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.integrable_mul_continuousOn_mul_test target :: scope.openDecls } }

theorem integral_weak_product_deriv
    (hΩ : IsOpen Ω) {U V c : E → ℝ} (v : E)
    (hU : _root_.MeasureTheory.LocallyIntegrable U μ) (hV : _root_.MeasureTheory.LocallyIntegrable V μ)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, V x * φ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) :
    (∫ x, c x * U x * fderiv ℝ φ x v ∂μ) =
      -∫ x, (c x * V x + fderiv ℝ c x v * U x) * φ x ∂μ := by
  let ψ := fun x => c x * φ x
  have hψs : tsupport ψ ⊆ Ω := tsupport_mul_subset_right.trans hφs
  have hψc : HasCompactSupport ψ := hφc.mul_left
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (hc.mul hφ.contDiffOn).contDiff_of_tsupport_subset hΩ hψs
  have hdc : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ c x v) Ω :=
    (hc.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have heq : (fun x => U x * fderiv ℝ ψ x v) = fun x =>
      c x * U x * fderiv ℝ φ x v + fderiv ℝ c x v * U x * φ x := by
    ext x
    by_cases hx : x ∈ Ω
    · have hcd := (hc.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
      dsimp only [ψ]
      rw [fderiv_fun_mul hcd (hφ.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    · have hp : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))
      have hdφ : fderiv ℝ φ x v = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ φ y v)
        (fun h => hx (hφs (tsupport_fderiv_apply_subset ℝ v h)))
      have hdψ : fderiv ℝ ψ x v = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ ψ y v)
        (fun h => hx (hψs (tsupport_fderiv_apply_subset ℝ v h)))
      simp only [hp, hdφ, hdψ, _root_.MulZeroClass.mul_zero, zero_add]
  have hI := integrable_mul_continuousOn_mul_test hΩ hU hc.continuousOn
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hφc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hφs)
  have hJ := integrable_mul_continuousOn_mul_test hΩ hU hdc.continuousOn
    hφ.continuous hφc hφs
  have hK := integrable_mul_continuousOn_mul_test hΩ hV hc.continuousOn
    hφ.continuous hφc hφs
  have ht := hweak ψ hψ hψc hψs
  rw [heq, _root_.MeasureTheory.integral_add hI hJ] at ht
  have hright : (∫ x, V x * ψ x ∂μ) = ∫ x, c x * V x * φ x ∂μ := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    dsimp only [ψ]
    ring
  rw [hright] at ht
  simp_rw [add_mul]
  rw [_root_.MeasureTheory.integral_add hK hJ]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integral_weak_product_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integral_weak_product_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integral_weak_product_deriv ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_weak_product_deriv


theorem integral_weak_deriv_weighted_divergence
    {ι : Type*} (s : Finset ι) (hΩ : IsOpen Ω)
    {U W R ρ L : E → ℝ} {V H A : ι → E → ℝ} (v w : E) (e : ι → E)
    (hU : _root_.MeasureTheory.LocallyIntegrable U μ) (hW : _root_.MeasureTheory.LocallyIntegrable W μ)
    (hR : _root_.MeasureTheory.LocallyIntegrable R μ)
    (hV : ∀ i ∈ s, _root_.MeasureTheory.LocallyIntegrable (V i) μ)
    (hH : ∀ i ∈ s, _root_.MeasureTheory.LocallyIntegrable (H i) μ)
    (hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ Ω)
    (hA : ∀ i ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (A i) Ω)
    (hspace : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, U x * fderiv ℝ ψ x v ∂μ) = -∫ x, W x * ψ x ∂μ)
    (hsource : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, U x * fderiv ℝ ψ x w ∂μ) = -∫ x, R x * ψ x ∂μ)
    (hflux : ∀ i ∈ s, ∀ ψ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ x, V i x * fderiv ℝ ψ x v ∂μ) = -∫ x, H i x * ψ x ∂μ)
    (hbase : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, ρ x * U x * fderiv ℝ ψ x w ∂μ) =
        (∑ i ∈ s, ∫ x, A i x * V i x * fderiv ℝ ψ x (e i) ∂μ) -
          ∫ x, L x * ψ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    (∫ x, ρ x * W x * fderiv ℝ φ x w ∂μ) =
      (∑ i ∈ s, ∫ x, (A i x * H i x + fderiv ℝ (A i) x v * V i x) *
        fderiv ℝ φ x (e i) ∂μ) + (∫ x, L x * fderiv ℝ φ x v ∂μ) +
        ∫ x, (fderiv ℝ ρ x v * R x +
          fderiv ℝ (fun y => fderiv ℝ ρ y v) x w * U x) * φ x ∂μ := by
  have hd (z : E) : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ φ x z) :=
    (hφ.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
  have hdc (z : E) : HasCompactSupport (fun x => fderiv ℝ φ x z) :=
    hφc.fderiv_apply ℝ z
  have hds (z : E) : tsupport (fun x => fderiv ℝ φ x z) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ z).trans hφs
  have hDρ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ ρ x v) Ω :=
    (hρ.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hT := integral_weak_product_deriv hΩ v hU hW hρ hspace (hd w) (hdc w) (hds w)
  have hS := integral_weak_product_deriv hΩ w hU hR hDρ hsource hφ hφc hφs
  have hI := integrable_mul_continuousOn_mul_test hΩ hW hρ.continuousOn
    (hd w).continuous (hdc w) (hds w)
  have hJ := integrable_mul_continuousOn_mul_test hΩ hU hDρ.continuousOn
    (hd w).continuous (hdc w) (hds w)
  have hTcomm : (∫ x, ρ x * U x * fderiv ℝ (fun y => fderiv ℝ φ y w) x v ∂μ) =
      ∫ x, ρ x * U x * fderiv ℝ (fun y => fderiv ℝ φ y v) x w ∂μ := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    rw [fderiv_fderiv_apply_comm hφ x w v]
  rw [hTcomm] at hT
  simp_rw [add_mul] at hT
  rw [_root_.MeasureTheory.integral_add hI hJ, hS] at hT
  have hF (i : ι) (hi : i ∈ s) :
      (∫ x, A i x * V i x * fderiv ℝ (fun y => fderiv ℝ φ y v) x (e i) ∂μ) =
        -∫ x, (A i x * H i x + fderiv ℝ (A i) x v * V i x) *
          fderiv ℝ φ x (e i) ∂μ := by
    have h := integral_weak_product_deriv hΩ v (hV i hi) (hH i hi) (hA i hi)
      (hflux i hi) (hd (e i)) (hdc (e i)) (hds (e i))
    convert h using 1
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    rw [fderiv_fderiv_apply_comm hφ x v (e i)]
  have hsum :
      (∑ i ∈ s, ∫ x, A i x * V i x * fderiv ℝ (fun y => fderiv ℝ φ y v) x (e i) ∂μ) =
        -(∑ i ∈ s, ∫ x, (A i x * H i x + fderiv ℝ (A i) x v * V i x) *
          fderiv ℝ φ x (e i) ∂μ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hF
  have hb := hbase (fun x => fderiv ℝ φ x v) (hd v) (hdc v) (hds v)
  rw [hsum] at hb
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_weighted_divergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_weighted_divergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_weighted_divergence ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_weighted_divergence

theorem integral_weak_deriv_weighted_divergence_eq_source
    {ι : Type*} (s : Finset ι) (hΩ : IsOpen Ω)
    {U W R ρ F DF : E → ℝ} {V H J A : ι → E → ℝ} (v w : E) (e : ι → E)
    (hU : _root_.MeasureTheory.LocallyIntegrable U μ) (hW : _root_.MeasureTheory.LocallyIntegrable W μ)
    (hR : _root_.MeasureTheory.LocallyIntegrable R μ) (hDF : _root_.MeasureTheory.LocallyIntegrable DF μ)
    (hV : ∀ i ∈ s, _root_.MeasureTheory.LocallyIntegrable (V i) μ)
    (hH : ∀ i ∈ s, _root_.MeasureTheory.LocallyIntegrable (H i) μ)
    (hJ : ∀ i ∈ s, _root_.MeasureTheory.LocallyIntegrable (J i) μ)
    (hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ Ω)
    (hA : ∀ i ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (A i) Ω)
    (hspace : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, U x * fderiv ℝ ψ x v ∂μ) = -∫ x, W x * ψ x ∂μ)
    (htime : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, U x * fderiv ℝ ψ x w ∂μ) = -∫ x, R x * ψ x ∂μ)
    (hflux : ∀ i ∈ s, ∀ ψ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ x, V i x * fderiv ℝ ψ x v ∂μ) = -∫ x, H i x * ψ x ∂μ)
    (hdiv : ∀ i ∈ s, ∀ ψ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ x, V i x * fderiv ℝ ψ x (e i) ∂μ) = -∫ x, J i x * ψ x ∂μ)
    (hsource : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, F x * fderiv ℝ ψ x v ∂μ) = -∫ x, DF x * ψ x ∂μ)
    (hbase : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, ρ x * U x * fderiv ℝ ψ x w ∂μ) =
        (∑ i ∈ s, ∫ x, A i x * V i x * fderiv ℝ ψ x (e i) ∂μ) -
          ∫ x, F x * ψ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    (∫ x, ρ x * W x * fderiv ℝ φ x w ∂μ) =
      (∑ i ∈ s, ∫ x, A i x * H i x * fderiv ℝ φ x (e i) ∂μ) -
        ∫ x, (DF x +
          (∑ i ∈ s, (fderiv ℝ (A i) x v * J i x +
            fderiv ℝ (fun y => fderiv ℝ (A i) y v) x (e i) * V i x)) -
          (fderiv ℝ ρ x v * R x +
            fderiv ℝ (fun y => fderiv ℝ ρ y v) x w * U x)) * φ x ∂μ := by
  let DA := fun i x => fderiv ℝ (A i) x v
  let DDA := fun i x => fderiv ℝ (DA i) x (e i)
  let Dρ := fun x => fderiv ℝ ρ x v
  let TDρ := fun x => fderiv ℝ Dρ x w
  let B := fun i x => DA i x * J i x + DDA i x * V i x
  let C := fun x => Dρ x * R x + TDρ x * U x
  have hDA (i) (hi : i ∈ s) : ContDiffOn ℝ (⊤ : ℕ∞) (DA i) Ω :=
    ((hA i hi).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hDDA (i) (hi : i ∈ s) : ContDiffOn ℝ (⊤ : ℕ∞) (DDA i) Ω :=
    ((hDA i hi).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hDρ : ContDiffOn ℝ (⊤ : ℕ∞) Dρ Ω :=
    (hρ.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hTDρ : ContDiffOn ℝ (⊤ : ℕ∞) TDρ Ω :=
    (hDρ.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hint {f c : E → ℝ} (hf : _root_.MeasureTheory.LocallyIntegrable f μ) (hc : ContinuousOn c Ω) :
      Integrable (fun x => c x * f x * φ x) μ :=
    integrable_mul_continuousOn_mul_test hΩ hf hc hφ.continuous hφc hφs
  have hB (i) (hi : i ∈ s) : _root_.MeasureTheory.Integrable (fun x => B i x * φ x) μ := by
    simp only [B, add_mul]
    exact (hint (hJ i hi) (hDA i hi).continuousOn).add
      (hint (hV i hi) (hDDA i hi).continuousOn)
  have hC : _root_.MeasureTheory.Integrable (fun x => C x * φ x) μ := by
    simp only [C, add_mul]
    exact (hint hR hDρ.continuousOn).add (hint hU hTDρ.continuousOn)
  have hDFI : _root_.MeasureTheory.Integrable (fun x => DF x * φ x) μ :=
    hDF.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  have hsplit (i) (hi : i ∈ s) :
      (∫ x, (A i x * H i x + DA i x * V i x) * fderiv ℝ φ x (e i) ∂μ) =
        (∫ x, A i x * H i x * fderiv ℝ φ x (e i) ∂μ) -
          ∫ x, B i x * φ x ∂μ := by
    have hp := integral_weak_product_deriv hΩ (e i) (hV i hi) (hJ i hi)
      (hDA i hi) (hdiv i hi) hφ hφc hφs
    have hd := (hφ.continuous_fderiv (by simp)).clm_apply (continuous_const (y := e i))
    have hdc := hφc.fderiv_apply ℝ (e i)
    have hds := (tsupport_fderiv_apply_subset ℝ (e i)).trans hφs
    have hmain := integrable_mul_continuousOn_mul_test hΩ (hH i hi)
      (hA i hi).continuousOn hd hdc hds
    have herr := integrable_mul_continuousOn_mul_test hΩ (hV i hi)
      (hDA i hi).continuousOn hd hdc hds
    simp_rw [add_mul]
    rw [_root_.MeasureTheory.integral_add hmain herr, hp]
    rfl
  have hsum : (∫ x, (∑ i ∈ s, B i x) * φ x ∂μ) =
      ∑ i ∈ s, ∫ x, B i x * φ x ∂μ := by
    simp_rw [Finset.sum_mul]
    exact _root_.MeasureTheory.integral_finsetSum _ hB
  have hsumI : _root_.MeasureTheory.Integrable (fun x => (∑ i ∈ s, B i x) * φ x) μ := by
    simpa only [Finset.sum_mul] using _root_.MeasureTheory.integrable_finsetSum s hB
  have hS : (∫ x, (DF x + (∑ i ∈ s, B i x) - C x) * φ x ∂μ) =
      (∫ x, DF x * φ x ∂μ) + (∑ i ∈ s, ∫ x, B i x * φ x ∂μ) -
        ∫ x, C x * φ x ∂μ := by
    simp_rw [sub_mul, add_mul]
    have hplus : _root_.MeasureTheory.Integrable (fun x => DF x * φ x + (∑ i ∈ s, B i x) * φ x) μ :=
      hDFI.add hsumI
    rw [_root_.MeasureTheory.integral_sub hplus hC, _root_.MeasureTheory.integral_add hDFI hsumI, hsum]
  have hc := integral_weak_deriv_weighted_divergence s hΩ v w e hU hW hR hV hH
    hρ hA hspace htime hflux hbase hφ hφc hφs
  change _ = (∑ i ∈ s, ∫ x, (A i x * H i x + DA i x * V i x) *
    fderiv ℝ φ x (e i) ∂μ) + _ + ∫ x, C x * φ x ∂μ at hc
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
    hsource φ hφ hφc hφs] at hc
  change _ = _ - ∫ x, (DF x + (∑ i ∈ s, B i x) - C x) * φ x ∂μ
  rw [hS]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_weighted_divergence_eq_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_weighted_divergence_eq_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_weighted_divergence_eq_source ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_weighted_divergence_eq_source

theorem exists_lp_weak_deriv_weighted_divergence [_root_.MeasureTheory.IsLocallyFiniteMeasure μ]
    {ι : Type*} (s : Finset ι) (hΩ : IsOpen Ω) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {U W R ρ F DF : E → ℝ} {V H J A : ι → E → ℝ} (v w : E) (e : ι → E)
    (hU : _root_.MeasureTheory.MemLp U p μ) (hW : _root_.MeasureTheory.LocallyIntegrable W μ)
    (hR : _root_.MeasureTheory.MemLp R p μ) (hDF : _root_.MeasureTheory.MemLp DF p μ)
    (hV : ∀ i ∈ s, _root_.MeasureTheory.MemLp (V i) p μ)
    (hH : ∀ i ∈ s, _root_.MeasureTheory.LocallyIntegrable (H i) μ)
    (hJ : ∀ i ∈ s, _root_.MeasureTheory.MemLp (J i) p μ)
    (hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ Ω)
    (hA : ∀ i ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (A i) Ω)
    (hDA : ∀ i ∈ s, _root_.MeasureTheory.MemLp (fun x => fderiv ℝ (A i) x v) ∞ μ)
    (hDDA : ∀ i ∈ s, _root_.MeasureTheory.MemLp (fun x =>
      fderiv ℝ (fun y => fderiv ℝ (A i) y v) x (e i)) ∞ μ)
    (hDρ : _root_.MeasureTheory.MemLp (fun x => fderiv ℝ ρ x v) ∞ μ)
    (hTDρ : _root_.MeasureTheory.MemLp (fun x => fderiv ℝ (fun y => fderiv ℝ ρ y v) x w) ∞ μ)
    (hspace : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, U x * fderiv ℝ ψ x v ∂μ) = -∫ x, W x * ψ x ∂μ)
    (htime : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, U x * fderiv ℝ ψ x w ∂μ) = -∫ x, R x * ψ x ∂μ)
    (hflux : ∀ i ∈ s, ∀ ψ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ x, V i x * fderiv ℝ ψ x v ∂μ) = -∫ x, H i x * ψ x ∂μ)
    (hdiv : ∀ i ∈ s, ∀ ψ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ x, V i x * fderiv ℝ ψ x (e i) ∂μ) = -∫ x, J i x * ψ x ∂μ)
    (hsource : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, F x * fderiv ℝ ψ x v ∂μ) = -∫ x, DF x * ψ x ∂μ)
    (hbase : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, ρ x * U x * fderiv ℝ ψ x w ∂μ) =
        (∑ i ∈ s, ∫ x, A i x * V i x * fderiv ℝ ψ x (e i) ∂μ) -
          ∫ x, F x * ψ x ∂μ) :
    ∃ S : _root_.MeasureTheory.Lp ℝ p μ,
      (S =ᵐ[μ] fun x => DF x +
        (∑ i ∈ s, (fderiv ℝ (A i) x v * J i x +
          fderiv ℝ (fun y => fderiv ℝ (A i) y v) x (e i) * V i x)) -
        (fderiv ℝ ρ x v * R x +
          fderiv ℝ (fun y => fderiv ℝ ρ y v) x w * U x)) ∧
      ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ x, ρ x * W x * fderiv ℝ φ x w ∂μ) =
          (∑ i ∈ s, ∫ x, A i x * H i x * fderiv ℝ φ x (e i) ∂μ) -
            ∫ x, S x * φ x ∂μ := by
  let S := fun x => DF x +
    (∑ i ∈ s, (fderiv ℝ (A i) x v * J i x +
      fderiv ℝ (fun y => fderiv ℝ (A i) y v) x (e i) * V i x)) -
    (fderiv ℝ ρ x v * R x + fderiv ℝ (fun y => fderiv ℝ ρ y v) x w * U x)
  have hS : _root_.MeasureTheory.MemLp S p μ :=
    (hDF.add (_root_.MeasureTheory.memLp_finsetSum s fun i hi =>
      ((hJ i hi).mul (hDA i hi)).add ((hV i hi).mul (hDDA i hi)))).sub
      ((hR.mul hDρ).add (hU.mul hTDρ))
  refine ⟨hS.toLp S, hS.coeFn_toLp, ?_⟩
  intro φ hφ hφc hφs
  have heq := integral_weak_deriv_weighted_divergence_eq_source s hΩ v w e
    (hU.locallyIntegrable hp) hW (hR.locallyIntegrable hp) (hDF.locallyIntegrable hp)
    (fun i hi => (hV i hi).locallyIntegrable hp) hH
    (fun i hi => (hJ i hi).locallyIntegrable hp) hρ hA hspace htime hflux hdiv
    hsource hbase hφ hφc hφs
  refine heq.trans ?_
  congr 1
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [hS.coeFn_toLp] with x hx
  rw [hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_lp_weak_deriv_weighted_divergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_lp_weak_deriv_weighted_divergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_lp_weak_deriv_weighted_divergence ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_lp_weak_deriv_weighted_divergence

omit [OpensMeasurableSpace E] in
theorem ae_eq_of_weak_second_deriv_comm [FiniteDimensional ℝ E] [BorelSpace E]
    (hΩ : IsOpen Ω) (hμΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    {U V W H K : E → ℝ} (v w : E)
    (hUv : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, V x * φ x ∂μ)
    (hUw : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x w ∂μ) = -∫ x, W x * φ x ∂μ)
    (hVw : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, V x * fderiv ℝ φ x w ∂μ) = -∫ x, H x * φ x ∂μ)
    (hWv : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, W x * fderiv ℝ φ x v ∂μ) = -∫ x, K x * φ x ∂μ)
    (hH : _root_.MeasureTheory.LocallyIntegrable H μ) (hK : _root_.MeasureTheory.LocallyIntegrable K μ) :
    H =ᵐ[μ] K := by
  apply ae_eq_of_integral_contDiff_mul_eq_on hΩ hμΩ hH hK
  intro φ hφ hφc hφs
  have hc := integral_weak_deriv_fderiv_comm v w hUv hUw hφ hφc hφs
  have hi := hVw φ hφ hφc hφs
  have hk := hWv φ hφ hφc hφs
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.ae_eq_of_weak_second_deriv_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.ae_eq_of_weak_second_deriv_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.ae_eq_of_weak_second_deriv_comm ``Submission.DifferentialGeometry.Analysis.Sobolev.ae_eq_of_weak_second_deriv_comm


end DifferentialGeometry.Analysis.Sobolev
