import Submission.DifferentialGeometry.Analysis.Integration.Lp.SpatialSteklov
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.SteklovAverage
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialGraph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory.Lp
open _root_.MeasureTheory _root_.MeasureTheory.Lp

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} [SFinite μ]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
local notation "E" => EuclideanSpace ℝ (Fin d)
open _root_.MeasureTheory _root_.MeasureTheory.Lp in
local notation "X" => _root_.MeasureTheory.Lp ℝ 2 (μ.prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
def spatialDiffQuot (k : Fin d) (h : ℝ) (u : X) : X :=
  h⁻¹ • (spatialTranslate (h • EuclideanSpace.single k 1) u - u)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.spatialDiffQuot then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.spatialDiffQuot"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.spatialDiffQuot ``Submission.MeasureTheory.Lp.spatialDiffQuot

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem coeFn_spatialDiffQuot (k : Fin d) (h : ℝ) (u : X) :
    spatialDiffQuot k h u =ᵐ[μ.prod _root_.MeasureTheory.MeasureSpace.volume] fun p =>
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h (fun x => u (p.1, x)) p.2 := by
  by_cases hh : h = 0
  · subst h
    simp only [spatialDiffQuot, inv_zero, zero_smul,
      DifferentialGeometry.Analysis.Sobolev.diffQuot_zero_h, Pi.zero_apply]
    exact _root_.MeasureTheory.Lp.coeFn_zero _ _ _
  filter_upwards [_root_.MeasureTheory.Lp.coeFn_smul h⁻¹ (spatialTranslate (h • EuclideanSpace.single k 1) u - u),
    _root_.MeasureTheory.Lp.coeFn_sub (spatialTranslate (h • EuclideanSpace.single k 1) u) u,
    coeFn_spatialTranslate (h • EuclideanSpace.single k 1) u] with p hsmul hsub htrans
  change (h⁻¹ • (spatialTranslate (h • EuclideanSpace.single k 1) u - u) : X) p = _
  rw [hsmul, Pi.smul_apply, hsub, Pi.sub_apply, htrans,
    DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne k hh, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.coeFn_spatialDiffQuot then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.coeFn_spatialDiffQuot"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.coeFn_spatialDiffQuot ``Submission.MeasureTheory.Lp.coeFn_spatialDiffQuot

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem norm_spatialDiffQuot_eq (k : Fin d) (h : ℝ) (u : X) :
    ‖spatialDiffQuot k h u‖ =
      (_root_.MeasureTheory.eLpNorm (fun p : Z × E =>
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (fun x => u (p.1, x)) p.2)
          2 (μ.prod _root_.MeasureTheory.MeasureSpace.volume)).toReal := by
  rw [Lp.norm_def, _root_.MeasureTheory.eLpNorm_congr_ae (coeFn_spatialDiffQuot k h u)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.norm_spatialDiffQuot_eq then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.norm_spatialDiffQuot_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.norm_spatialDiffQuot_eq ``Submission.MeasureTheory.Lp.norm_spatialDiffQuot_eq

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem norm_spatialDiffQuot_le (k : Fin d) (h : ℝ) (u : X) {C : ℝ} (hC : 0 ≤ C)
    (hbound : _root_.MeasureTheory.eLpNorm (fun p : Z × E =>
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h (fun x => u (p.1, x)) p.2)
        2 (μ.prod _root_.MeasureTheory.MeasureSpace.volume) ≤ ENNReal.ofReal C) :
    ‖spatialDiffQuot k h u‖ ≤ C := by
  rw [norm_spatialDiffQuot_eq]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hC)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.norm_spatialDiffQuot_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.norm_spatialDiffQuot_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.norm_spatialDiffQuot_le ``Submission.MeasureTheory.Lp.norm_spatialDiffQuot_le

end MeasureTheory.Lp


namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "X" => _root_.MeasureTheory.Lp ℝ 2 (μ.prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))

theorem ae_hasWeakPartialDeriv_spatialSteklovAverage (k : Fin d) (h : ℝ) (u : X) :
    ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => Lp.spatialDiffQuot k h u (t, x))
      (fun x => Lp.spatialSteklovAverage (EuclideanSpace.single k 1) h u (t, x)) univ := by
  filter_upwards [(Lp.memLp u).prodMk_left (by norm_num),
    Measure.ae_ae_of_ae_prod (Lp.coeFn_spatialDiffQuot k h u),
    Measure.ae_ae_of_ae_prod (Lp.coeFn_spatialSteklovAverage (EuclideanSpace.single k 1) h u)]
    with t ht hdiff hav
  have hweak := hasWeakPartialDeriv_integral_translate ht k h
  intro φ hφ hφc hφs
  have htest := hweak φ hφ hφc hφs
  simp only [Measure.restrict_univ] at htest ⊢
  have hl : (∫ x, Lp.spatialSteklovAverage (EuclideanSpace.single k 1) h u (t, x) *
        fderiv ℝ φ x (EuclideanSpace.single k 1)) =
      ∫ x, (h⁻¹ * ∫ r in (0 : ℝ)..h, u (t, x + r • EuclideanSpace.single k 1)) *
        fderiv ℝ φ x (EuclideanSpace.single k 1) := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hav] with x hx
    rw [hx]
  have hr : (∫ x, Lp.spatialDiffQuot k h u (t, x) * φ x) =
      ∫ x, diffQuot k h (fun y => u (t, y)) x * φ x := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hdiff] with x hx
    rw [hx]
  exact hl.trans (htest.trans (congrArg Neg.neg hr.symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.ae_hasWeakPartialDeriv_spatialSteklovAverage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.ae_hasWeakPartialDeriv_spatialSteklovAverage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.ae_hasWeakPartialDeriv_spatialSteklovAverage ``Submission.DifferentialGeometry.Analysis.Sobolev.ae_hasWeakPartialDeriv_spatialSteklovAverage

private theorem positive_vanishing_steps {h₀ : ℝ} (hh₀ : 0 < h₀) :
    ∃ H : ℕ → ℝ, (∀ n, 0 < |H n| ∧ |H n| ≤ h₀) ∧
      Tendsto H _root_.Filter.atTop (𝓝[≠] 0) := by
  let H : ℕ → ℝ := fun n => h₀ / ((n : ℝ) + 1)
  have hpos (n : ℕ) : 0 < H n := div_pos hh₀ (by positivity)
  refine ⟨H, ?_, ?_⟩
  · intro n
    rw [abs_of_pos (hpos n)]
    refine ⟨hpos n, ?_⟩
    dsimp [H]
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · have ht : _root_.Filter.Tendsto H _root_.Filter.atTop (𝓝 0) := by
      simpa only [H, div_eq_mul_inv, one_div, one_mul, _root_.MulZeroClass.mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul h₀
    exact tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall fun n => (hpos n).ne'⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.positive_vanishing_steps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.positive_vanishing_steps target :: scope.openDecls } }

theorem exists_ae_hasWeakPartialDeriv_of_spatial_diffQuot_uniform_bound
    (u : X) (k : Fin d) {C h₀ : ℝ} (hC : 0 ≤ C) (hh₀ : 0 < h₀)
    (hbound : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      _root_.MeasureTheory.eLpNorm (fun p : ℝ × E => diffQuot k h (fun x => u (p.1, x)) p.2)
        2 (μ.prod _root_.MeasureTheory.MeasureSpace.volume) ≤ ENNReal.ofReal C) :
    ∃ v : X, ‖v‖ ≤ C ∧ ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => v (t, x)) (fun x => u (t, x)) univ := by
  let _ : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let _ : SecondCountableTopology X := Lp.SecondCountableTopology
  obtain ⟨H, hH, hHlim⟩ := positive_vanishing_steps hh₀
  let U : ℕ → X := fun n => Lp.spatialSteklovAverage (EuclideanSpace.single k 1) (H n) u
  let V : ℕ → X := fun n => Lp.spatialDiffQuot k (H n) u
  have hU : _root_.Filter.Tendsto U _root_.Filter.atTop (𝓝 u) :=
    (Lp.tendsto_spatialSteklovAverage (EuclideanSpace.single k 1) u).comp hHlim
  have hV (n : ℕ) : ‖V n‖ ≤ C :=
    Lp.norm_spatialDiffQuot_le k (H n) u hC (hbound (H n) (hH n).1 (hH n).2)
  have hw (n : ℕ) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => V n (t, x)) (fun x => U n (t, x)) univ :=
    ae_hasWeakPartialDeriv_spatialSteklovAverage k (H n) u
  have hcompact := fun (U V : ℕ → _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict (_root_.Set.univ : Set E))))
    (u : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict (_root_.Set.univ : Set E)))) (C : ℝ) =>
      @Euclidean.exists_ae_hasWeakPartialDeriv_of_norm_bounded d ℝ _ μ _root_.Set.univ inferInstance k U V u C
  rw [Measure.restrict_univ] at hcompact
  exact hcompact U V u C hU hV hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_ae_hasWeakPartialDeriv_of_spatial_diffQuot_uniform_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_ae_hasWeakPartialDeriv_of_spatial_diffQuot_uniform_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_ae_hasWeakPartialDeriv_of_spatial_diffQuot_uniform_bound ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_ae_hasWeakPartialDeriv_of_spatial_diffQuot_uniform_bound

end DifferentialGeometry.Analysis.Sobolev
