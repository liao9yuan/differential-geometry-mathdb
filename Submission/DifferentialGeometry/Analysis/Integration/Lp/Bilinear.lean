import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Bilinear

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable
    {P X Y : Type*} [MeasurableSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {μ : _root_.MeasureTheory.Measure P} (A : P → X →L[ℝ] Y)
    (hA : ∀ x, _root_.MeasureTheory.AEStronglyMeasurable (fun p => A p x) μ)
    (u : P → X) (hu : _root_.MeasureTheory.AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun p => A p (u p)) μ := by
  classical
  let u' : P → X := hu.mk u
  have hu' : _root_.MeasureTheory.StronglyMeasurable u' := hu.stronglyMeasurable_mk
  let s : ℕ → _root_.MeasureTheory.SimpleFunc P X := hu'.approx
  have hs (m : ℕ) : _root_.MeasureTheory.AEStronglyMeasurable (fun p => A p (s m p)) μ := by
    let F : P → Y := fun p =>
      ∑ x ∈ (s m).range, (s m ⁻¹' {x}).indicator (fun r => A r x) p
    have hF : _root_.MeasureTheory.AEStronglyMeasurable F μ := by
      let F' : P → Y :=
        ∑ x ∈ (s m).range, (s m ⁻¹' {x}).indicator (fun r => A r x)
      have hF' : _root_.MeasureTheory.AEStronglyMeasurable F' μ :=
        Finset.aestronglyMeasurable_sum (s m).range (fun x _ =>
          (hA x).indicator ((s m).measurableSet_fiber x))
      have hFF' : F = F' := by
        funext p
        simp only [F, F', Finset.sum_apply]
      exact hFF' ▸ hF'
    refine hF.congr (Eventually.of_forall fun p => ?_)
    dsimp only [F]
    rw [Finset.sum_eq_single (s m p)]
    · apply Set.indicator_of_mem
      change (s m p) ∈ ({s m p} : Set X)
      exact Set.mem_singleton _
    · intro x hx hne
      rw [Set.indicator_of_notMem]
      exact fun hmem => hne hmem.symm
    · exact fun hmem => (hmem ((s m).mem_range_self p)).elim
  refine aestronglyMeasurable_of_tendsto_ae _root_.Filter.atTop hs ?_
  filter_upwards [hu.ae_eq_mk] with p hup
  have hs_tendsto : _root_.Filter.Tendsto (fun m => s m p) _root_.Filter.atTop (nhds (u' p)) :=
    hu'.tendsto_approx p
  have happly : _root_.Filter.Tendsto (fun m => A p (s m p)) _root_.Filter.atTop (nhds (A p (u' p))) :=
    (A p).continuous.continuousAt.tendsto.comp hs_tendsto
  simpa only [u', hup] using happly

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.AEStronglyMeasurable
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace MeasureTheory
open _root_.MeasureTheory

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

open _root_.MeasureTheory in
theorem integrable_bilinear_of_apply_aestronglyMeasurable
    {P : Type*} [MeasurableSpace P] {μ : _root_.MeasureTheory.Measure P}
    (B : P → X →L[ℝ] Y →L[ℝ] Z)
    (hB : ∀ x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => B t x y) μ)
    {C : ℝ} (hC : ∀ᵐ t ∂μ, ‖B t‖ ≤ C)
    {u : P → X} (hu : _root_.MeasureTheory.MemLp u 2 μ) {v : P → Y} (hv : _root_.MeasureTheory.MemLp v 2 μ) :
    Integrable (fun t => B t (u t) (v t)) μ := by
  have hmeas : _root_.MeasureTheory.AEStronglyMeasurable (fun t => B t (u t) (v t)) μ := by
    apply DifferentialGeometry.Analysis.Parabolic.TimeSobolev.AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable
      (fun t => B t (u t)) _ v hv.aestronglyMeasurable
    intro y
    exact DifferentialGeometry.Analysis.Parabolic.TimeSobolev.AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable
      (fun t => (B t).flip y) (fun x => hB x y) u hu.aestronglyMeasurable
  have hprod : _root_.MeasureTheory.Integrable (fun t => ‖u t‖ * ‖v t‖) μ :=
    hu.norm.integrable_mul hv.norm
  refine (hprod.const_mul C).mono' hmeas ?_
  filter_upwards [hC] with t ht
  calc
    ‖B t (u t) (v t)‖ ≤ ‖B t‖ * ‖u t‖ * ‖v t‖ := (B t).le_opNorm₂ _ _
    _ ≤ C * (‖u t‖ * ‖v t‖) := by
      calc
        _ ≤ C * ‖u t‖ * ‖v t‖ := by gcongr
        _ = _ := mul_assoc _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable ``Submission.MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable

end MeasureTheory

namespace MeasureTheory
open _root_.MeasureTheory

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
open _root_.MeasureTheory in
private theorem integral_norm_mul_norm_le_lp_norm
    {P : Type*} [MeasurableSpace P] {μ : _root_.MeasureTheory.Measure P}
    (u : _root_.MeasureTheory.Lp X 2 μ) (v : _root_.MeasureTheory.Lp Y 2 μ) :
    (∫ t, ‖u t‖ * ‖v t‖ ∂μ) ≤ ‖u‖ * ‖v‖ := by
  let uN : _root_.MeasureTheory.Lp ℝ 2 μ := (Lp.memLp u).norm.toLp (fun t => ‖u t‖)
  let vN : _root_.MeasureTheory.Lp ℝ 2 μ := (Lp.memLp v).norm.toLp (fun t => ‖v t‖)
  have hpair : (∫ t, ‖u t‖ * ‖v t‖ ∂μ) = _root_.Inner.inner ℝ uN vN := by
    rw [L2.inner_def]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [(Lp.memLp u).norm.coeFn_toLp, (Lp.memLp v).norm.coeFn_toLp]
      with t hu hv
    simp only [Real.inner_apply]
    change ‖u t‖ * ‖v t‖ = uN t * vN t
    rw [show uN t = ‖u t‖ from hu, show vN t = ‖v t‖ from hv]
  have hun : ‖uN‖ = ‖u‖ := by rw [Lp.norm_toLp, _root_.MeasureTheory.eLpNorm_norm, Lp.norm_def]
  have hvn : ‖vN‖ = ‖v‖ := by rw [Lp.norm_toLp, _root_.MeasureTheory.eLpNorm_norm, Lp.norm_def]
  rw [hpair, ← hun, ← hvn]
  exact real_inner_le_norm _ _

run_cmd do
  let target := ``Submission.MeasureTheory.integral_norm_mul_norm_le_lp_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.integral_norm_mul_norm_le_lp_norm target :: scope.openDecls } }

open _root_.MeasureTheory in
theorem norm_integral_bilinear_le_lp_norm
    {P : Type*} [MeasurableSpace P] {μ : _root_.MeasureTheory.Measure P}
    (B : P → X →L[ℝ] Y →L[ℝ] Z)
    (hB : ∀ x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => B t x y) μ)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ t ∂μ, ‖B t‖ ≤ C)
    (u : _root_.MeasureTheory.Lp X 2 μ) (v : _root_.MeasureTheory.Lp Y 2 μ) :
    ‖∫ t, B t (u t) (v t) ∂μ‖ ≤ C * (‖u‖ * ‖v‖) := by
  have hint := integrable_bilinear_of_apply_aestronglyMeasurable B hB hC
    (Lp.memLp u) (Lp.memLp v)
  have hprod : _root_.MeasureTheory.Integrable (fun t => ‖u t‖ * ‖v t‖) μ :=
    (Lp.memLp u).norm.integrable_mul (Lp.memLp v).norm
  calc
    _ ≤ ∫ t, ‖B t (u t) (v t)‖ ∂μ := _root_.MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t, C * (‖u t‖ * ‖v t‖) ∂μ := by
      apply _root_.MeasureTheory.integral_mono_ae hint.norm (hprod.const_mul C)
      filter_upwards [hC] with t ht
      calc
        _ ≤ ‖B t‖ * ‖u t‖ * ‖v t‖ := (B t).le_opNorm₂ _ _
        _ ≤ C * (‖u t‖ * ‖v t‖) := by
          calc
            _ ≤ C * ‖u t‖ * ‖v t‖ := by gcongr
            _ = _ := mul_assoc _ _ _
    _ = C * ∫ t, ‖u t‖ * ‖v t‖ ∂μ := _root_.MeasureTheory.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_norm_mul_norm_le_lp_norm u v) hC0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.norm_integral_bilinear_le_lp_norm then
    throwError "Refusing to shadow existing declaration MeasureTheory.norm_integral_bilinear_le_lp_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.norm_integral_bilinear_le_lp_norm ``Submission.MeasureTheory.norm_integral_bilinear_le_lp_norm

open _root_.MeasureTheory in
theorem continuous_integral_bilinear_lp_right
    {P : Type*} [MeasurableSpace P] {μ : _root_.MeasureTheory.Measure P}
    (B : P → X →L[ℝ] Y →L[ℝ] Z)
    (hB : ∀ x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => B t x y) μ)
    {C : ℝ} (hC : ∀ᵐ t ∂μ, ‖B t‖ ≤ C) (u : _root_.MeasureTheory.Lp X 2 μ) :
    Continuous (fun v : _root_.MeasureTheory.Lp Y 2 μ => ∫ t, B t (u t) (v t) ∂μ) := by
  have hC' : ∀ᵐ t ∂μ, ‖B t‖ ≤ _root_.Max.max 0 C := hC.mono fun _ ht => ht.trans (le_max_right 0 C)
  apply LipschitzWith.continuous (K := ⟨max 0 C * ‖u‖, mul_nonneg (le_max_left 0 C) (norm_nonneg _)⟩)
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have hid : (∫ t, B t (u t) (v t) ∂μ) - (∫ t, B t (u t) (w t) ∂μ) =
      ∫ t, B t (u t) ((v - w) t) ∂μ := by
    rw [← _root_.MeasureTheory.integral_sub
      (integrable_bilinear_of_apply_aestronglyMeasurable B hB hC (Lp.memLp u) (Lp.memLp v))
      (integrable_bilinear_of_apply_aestronglyMeasurable B hB hC (Lp.memLp u) (Lp.memLp w))]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [Lp.coeFn_sub v w] with t ht
    rw [ht, Pi.sub_apply, map_sub]
  rw [dist_eq_norm, hid, dist_eq_norm]
  exact (norm_integral_bilinear_le_lp_norm B hB (le_max_left 0 C) hC' u (v - w)).trans_eq
    (mul_assoc _ _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.continuous_integral_bilinear_lp_right then
    throwError "Refusing to shadow existing declaration MeasureTheory.continuous_integral_bilinear_lp_right"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.continuous_integral_bilinear_lp_right ``Submission.MeasureTheory.continuous_integral_bilinear_lp_right

end MeasureTheory
