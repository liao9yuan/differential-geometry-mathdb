import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleContinuousComposition
import Submission.DifferentialGeometry.Analysis.Integration.Lp.BoundedConvergence
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleTameComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

open _root_.AddCircle in
private theorem tendstoInMeasure_scalar_composition_of_order
    {Ω : Type*} [MeasurableSpace Ω] (μ : _root_.MeasureTheory.Measure Ω) [_root_.MeasureTheory.IsFiniteMeasure μ]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    {σ : ℝ} (hσ : σ = (k : ℝ) + 1)
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (u : ℕ → Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 σ))
    (u0 : Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 σ))
    (v : ℕ → Ω → TensorHs g 0 0 σ)
    (v0 : Ω → TensorHs g 0 0 σ)
    (hu : _root_.MeasureTheory.TendstoInMeasure μ u _root_.Filter.atTop u0)
    (hv : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (v n) μ) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by rw [hσ]; norm_num : (1 : ℝ) ≤ σ)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    (∀ᵐ t ∂μ, _root_.Set.range (scalarH1PiToContinuous g (P (u0 t))) ⊆ U) →
    (∀ n, ∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v n t)) x =
      F (scalarH1PiToContinuous g (P (u n t)) x)) →
    (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v0 t)) x =
      F (scalarH1PiToContinuous g (P (u0 t)) x)) →
    TendstoInMeasure μ v _root_.Filter.atTop v0 := by
  subst σ
  intro J P hRange hEval hEval0
  apply (_root_.MeasureTheory.exists_seq_tendstoInMeasure_atTop_iff hv).mpr
  intro ns hns
  obtain ⟨ms, hms, hlim⟩ := (hu.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hlim, hRange, hEval0, ae_all_iff.mpr hEval] with t ht hRt hEt hEnt
  exact tendsto_scalarHs_composition g k F hF hU
    (fun n => u (ns (ms n)) t) (u0 t)
    (fun n => v (ns (ms n)) t) (v0 t) ht hRt
    (Eventually.of_forall (fun n => hEnt (ns (ms n)))) hEt

run_cmd do
  let target := ``Submission.AddCircle.tendstoInMeasure_scalar_composition_of_order
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.tendstoInMeasure_scalar_composition_of_order target :: scope.openDecls } }

open _root_.AddCircle in
theorem tendstoInMeasure_scalarHs_composition
    {Ω : Type*} [MeasurableSpace Ω] (μ : _root_.MeasureTheory.Measure Ω) [_root_.MeasureTheory.IsFiniteMeasure μ]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (u : ℕ → Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (u0 : Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (v : ℕ → Ω → TensorHs g 0 0 ((k : ℝ) + 1))
    (v0 : Ω → TensorHs g 0 0 ((k : ℝ) + 1))
    (hu : _root_.MeasureTheory.TendstoInMeasure μ u _root_.Filter.atTop u0)
    (hv : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (v n) μ) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    (∀ᵐ t ∂μ, _root_.Set.range (scalarH1PiToContinuous g (P (u0 t))) ⊆ U) →
    (∀ n, ∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v n t)) x =
      F (scalarH1PiToContinuous g (P (u n t)) x)) →
    (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v0 t)) x =
      F (scalarH1PiToContinuous g (P (u0 t)) x)) →
    TendstoInMeasure μ v _root_.Filter.atTop v0 := by
  exact tendstoInMeasure_scalar_composition_of_order μ g k rfl F hF hU u u0 v v0 hu hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.tendstoInMeasure_scalarHs_composition then
    throwError "Refusing to shadow existing declaration AddCircle.tendstoInMeasure_scalarHs_composition"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.tendstoInMeasure_scalarHs_composition ``Submission.AddCircle.tendstoInMeasure_scalarHs_composition

open _root_.AddCircle in
private theorem tendsto_lp_scalarHs_composition_seq_of_lower_order_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : _root_.MeasureTheory.Measure Ω) [_root_.MeasureTheory.IsFiniteMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ (⊤ : ℝ≥0∞))
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ)
    (u : ℕ → _root_.MeasureTheory.Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))) p μ)
    (u0 : _root_.MeasureTheory.Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))) p μ)
    (v : ℕ → _root_.MeasureTheory.Lp (TensorHs g 0 0 ((k : ℝ) + 2)) p μ)
    (v0 : _root_.MeasureTheory.Lp (TensorHs g 0 0 ((k : ℝ) + 2)) p μ)
    (hu : _root_.Filter.Tendsto u _root_.Filter.atTop (𝓝 u0)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    let L := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    (∀ n, ∀ᵐ t ∂μ, _root_.Set.range (scalarH1PiToContinuous g (P (u n t))) ⊆ K) →
    (∀ᵐ t ∂μ, _root_.Set.range (scalarH1PiToContinuous g (P (u0 t))) ⊆ U) →
    (∀ n, ∀ᵐ t ∂μ, (∑ i, ‖L (u n t i)‖) ≤ R) →
    (∀ n, ∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v n t)) x =
      F (scalarH1PiToContinuous g (P (u n t)) x)) →
    (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v0 t)) x =
      F (scalarH1PiToContinuous g (P (u0 t)) x)) →
    Tendsto v _root_.Filter.atTop (𝓝 v0) := by
  intro J P L hRange hRange0 hBound hEval hEval0
  have hv : _root_.MeasureTheory.TendstoInMeasure μ (fun n => v n) _root_.Filter.atTop v0 := by
    exact tendstoInMeasure_scalar_composition_of_order μ g (k + 1)
      (by push_cast; ring : (k : ℝ) + 2 = ((k + 1 : ℕ) : ℝ) + 1)
      F hF hU (fun n => u n) u0 (fun n => v n) v0
      (_root_.MeasureTheory.tendstoInMeasure_of_tendsto_Lp hu) (fun n => Lp.aestronglyMeasurable (v n))
      hRange0 hEval hEval0
  obtain ⟨C, hC, hc⟩ := exists_scalarHs_composition_bound_of_lower_order_bound
    g k F hF hU hK hKU R
  let E := PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))
  let c : ℝ := Fintype.card ι
  let one : _root_.MeasureTheory.Lp ℝ p μ := (_root_.MeasureTheory.memLp_const (1 : ℝ)).toLp (fun _ : Ω => 1)
  let q : _root_.MeasureTheory.Lp E p μ → _root_.MeasureTheory.Lp ℝ p μ := lipschitzWith_one_norm.compLp (norm_zero : ‖(0 : E)‖ = 0)
  let B : _root_.MeasureTheory.Lp E p μ → _root_.MeasureTheory.Lp ℝ p μ := fun w => C • (one + c • q w)
  have hq : Continuous q := lipschitzWith_one_norm.continuous_compLp (norm_zero : ‖(0 : E)‖ = 0)
  have hB : Continuous B := (continuous_const.add (hq.const_smul c)).const_smul C
  have hBeval (w : _root_.MeasureTheory.Lp E p μ) : ∀ᵐ t ∂μ, B w t = C * (1 + c * ‖w t‖) := by
    filter_upwards [Lp.coeFn_smul C (one + c • q w), Lp.coeFn_add one (c • q w),
      (_root_.MeasureTheory.memLp_const (1 : ℝ) : _root_.MeasureTheory.MemLp (fun _ : Ω => (1 : ℝ)) p μ).coeFn_toLp,
      Lp.coeFn_smul c (q w),
      lipschitzWith_one_norm.coeFn_compLp (norm_zero : ‖(0 : E)‖ = 0) w] with t h₁ h₂ h₃ h₄ h₅
    change (C • (one + c • q w)) t = _
    change one t = 1 at h₃
    change q w t = ‖w t‖ at h₅
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h₁ h₂ h₄
    rw [h₁, h₂, h₄, h₃, h₅]
  apply Lp.tendsto_of_tendstoInMeasure_of_ae_norm_le hp v v0
    (fun n => B (u n)) (B u0) (hB.tendsto u0 |>.comp hu) _ hv
  intro n
  filter_upwards [hRange n, hBound n, hEval n, hBeval (u n)] with t hRt hBt hEt hBwt
  obtain ⟨z, hz, hze⟩ := hc (u n t) hRt hBt
  have heq : v n t = z := by
    apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    apply scalarH1ToContinuous_injective g
    exact ContinuousMap.ext (fun x => (hEt x).trans (hze x).symm)
  have hsum : (∑ i, ‖u n t i‖) ≤ c * ‖u n t‖ := by
    calc
      _ ≤ ∑ _i : ι, ‖u n t‖ := Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le (u n t) i)
      _ = _ := by simp [c]
  rw [heq, hBwt, Real.norm_eq_abs, abs_of_nonneg]
  · exact hz.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hC)
  · exact mul_nonneg hC (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))

run_cmd do
  let target := ``Submission.AddCircle.tendsto_lp_scalarHs_composition_seq_of_lower_order_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.tendsto_lp_scalarHs_composition_seq_of_lower_order_bound target :: scope.openDecls } }

open _root_.AddCircle in
theorem tendsto_lp_scalarHs_composition_of_lower_order_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : _root_.MeasureTheory.Measure Ω) [_root_.MeasureTheory.IsFiniteMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ (⊤ : ℝ≥0∞))
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ)
    {X : Type*} {l : Filter X}
    (u : X → _root_.MeasureTheory.Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))) p μ)
    (u0 : _root_.MeasureTheory.Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))) p μ)
    (v : X → _root_.MeasureTheory.Lp (TensorHs g 0 0 ((k : ℝ) + 2)) p μ)
    (v0 : _root_.MeasureTheory.Lp (TensorHs g 0 0 ((k : ℝ) + 2)) p μ)
    (hu : _root_.Filter.Tendsto u l (𝓝 u0)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    let L := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    (∀ n, ∀ᵐ t ∂μ, _root_.Set.range (scalarH1PiToContinuous g (P (u n t))) ⊆ K) →
    (∀ᵐ t ∂μ, _root_.Set.range (scalarH1PiToContinuous g (P (u0 t))) ⊆ U) →
    (∀ n, ∀ᵐ t ∂μ, (∑ i, ‖L (u n t i)‖) ≤ R) →
    (∀ n, ∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v n t)) x =
      F (scalarH1PiToContinuous g (P (u n t)) x)) →
    (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v0 t)) x =
      F (scalarH1PiToContinuous g (P (u0 t)) x)) →
    Tendsto v l (𝓝 v0) := by
  intro J P L hRange hRange0 hBound hEval hEval0
  have hv : _root_.Filter.Tendsto v (Filter.comap u (𝓝 u0)) (𝓝 v0) := by
    apply Filter.tendsto_of_seq_tendsto
    intro ns hns
    exact tendsto_lp_scalarHs_composition_seq_of_lower_order_bound μ hp g k F hF hU hK hKU R
      (fun n => u (ns n)) u0 (fun n => v (ns n)) v0
      (tendsto_comap_iff.mp hns) (fun n => hRange (ns n)) hRange0
      (fun n => hBound (ns n)) (fun n => hEval (ns n)) hEval0
  exact hv.mono_left hu.le_comap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.tendsto_lp_scalarHs_composition_of_lower_order_bound then
    throwError "Refusing to shadow existing declaration AddCircle.tendsto_lp_scalarHs_composition_of_lower_order_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.tendsto_lp_scalarHs_composition_of_lower_order_bound ``Submission.AddCircle.tendsto_lp_scalarHs_composition_of_lower_order_bound

end AddCircle
