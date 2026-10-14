import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.LocallyLipschitz.ChainRule
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memLp_spatial_fderiv_of_locallyLipschitzOn
    {a b : ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {u : ℝ × E → ℝ} (hu : LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ closure Ω) u)
    (p : ℝ≥0∞) (i : Fin d) :
    _root_.MeasureTheory.MemLp (fun q : ℝ × E =>
      fderiv ℝ (fun x => u (q.1, x)) q.2 (EuclideanSpace.single i 1)) p
        ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) := by
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by
      simpa only [Measure.restrict_apply_univ] using
        (_root_.MeasureTheory.measure_mono (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
          (subset_closure : Ω ⊆ closure Ω)).trans_lt hΩc.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hu.exists_lipschitzOnWith_of_compact (isCompact_Icc.prod hΩc)
  obtain ⟨g, hg, hug⟩ := hC.extend_real
  have hgSlice (t : ℝ) : LipschitzWith C (fun x : E => g (t, x)) := by
    simpa only [mul_one, Function.comp_def] using hg.comp (LipschitzWith.prodMk_left t)
  have hgMem : _root_.MeasureTheory.MemLp (fun q : ℝ × E =>
      fderiv ℝ (fun x => g (q.1, x)) q.2 (EuclideanSpace.single i 1)) p
        ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) := by
    apply MemLp.of_bound
      (measurable_fderiv_apply_const_with_param ℝ
        (f := fun (t : ℝ) (x : E) => g (t, x)) hg.continuous
        (EuclideanSpace.single i (1 : ℝ))).aestronglyMeasurable
      ((C : ℝ) * ‖EuclideanSpace.single i (1 : ℝ)‖)
    apply Eventually.of_forall
    intro q
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hgSlice q.1))
        (norm_nonneg _))
  apply hgMem.ae_eq
  rw [Measure.prod_restrict]
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem (measurableSet_Icc.prod hΩ.measurableSet)] with q hq
  have hlocal : (fun x : E => u (q.1, x)) =ᶠ[𝓝 q.2] fun x => g (q.1, x) := by
    filter_upwards [hΩ.mem_nhds hq.2] with x hx
    exact hug ⟨hq.1, subset_closure hx⟩
  exact congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hlocal.fderiv_eq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_spatial_fderiv_of_locallyLipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_spatial_fderiv_of_locallyLipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_spatial_fderiv_of_locallyLipschitzOn ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_spatial_fderiv_of_locallyLipschitzOn

theorem exists_lp_spatial_weak_derivatives_of_locallyLipschitzOn
    {a b : ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {u : ℝ × E → ℝ} (hu : LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ closure Ω) u)
    (p : ℝ≥0∞) :
    let ν := (volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)
    ∃ U : _root_.MeasureTheory.Lp ℝ p ν, ∃ K : Fin d → _root_.MeasureTheory.Lp ℝ p ν,
      (U =ᵐ[ν] u) ∧
      (∀ i, K i =ᵐ[ν] fun q =>
        fderiv ℝ (fun x => u (q.1, x)) q.2 (EuclideanSpace.single i 1)) ∧
      ∀ i, ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => K i (t, x)) (fun x => U (t, x)) Ω := by
  intro ν
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by
      simpa only [Measure.restrict_apply_univ] using
        (_root_.MeasureTheory.measure_mono (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
          (subset_closure : Ω ⊆ closure Ω)).trans_lt hΩc.measure_lt_top⟩
  have huMem : _root_.MeasureTheory.MemLp u p ν := by
    have htop : _root_.MeasureTheory.MemLp u ∞ ν := by
      change _root_.MeasureTheory.MemLp u ∞ ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω))
      rw [Measure.prod_restrict]
      exact hu.continuousOn.memLp_top_of_subset_isCompact (isCompact_Icc.prod hΩc)
        (measurableSet_Icc.prod hΩ.measurableSet) (_root_.Set.prod_mono Subset.rfl subset_closure)
    exact htop.mono_exponent le_top
  let D : Fin d → ℝ × E → ℝ := fun i q =>
    fderiv ℝ (fun x => u (q.1, x)) q.2 (EuclideanSpace.single i 1)
  have hDMem (i : Fin d) : _root_.MeasureTheory.MemLp (D i) p ν :=
    memLp_spatial_fderiv_of_locallyLipschitzOn hΩ hΩc hu p i
  let U : _root_.MeasureTheory.Lp ℝ p ν := huMem.toLp u
  let K : Fin d → _root_.MeasureTheory.Lp ℝ p ν := fun i => (hDMem i).toLp (D i)
  have hU : U =ᵐ[ν] u := huMem.coeFn_toLp
  have hK (i : Fin d) : K i =ᵐ[ν] D i := (hDMem i).coeFn_toLp
  refine ⟨U, K, hU, hK, ?_⟩
  obtain ⟨C, hC⟩ := hu.exists_lipschitzOnWith_of_compact (isCompact_Icc.prod hΩc)
  intro i
  filter_upwards [Measure.ae_ae_of_ae_prod hU, Measure.ae_ae_of_ae_prod (hK i),
    _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t htU htK ht
  have hslice : LipschitzOnWith C (fun x : E => u (t, x)) Ω := by
    simpa only [mul_one, Function.comp_def] using
      hC.comp (LipschitzWith.prodMk_left t).lipschitzOnWith
        (fun x hx => ⟨ht, subset_closure hx⟩)
  exact (hasWeakPartialDeriv_fderiv_of_lipschitzOnWith hΩ hslice i).congr_ae
    (Filter.EventuallyEq.symm htU) (Filter.EventuallyEq.symm htK)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_spatial_weak_derivatives_of_locallyLipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_spatial_weak_derivatives_of_locallyLipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_spatial_weak_derivatives_of_locallyLipschitzOn ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_spatial_weak_derivatives_of_locallyLipschitzOn

end DifferentialGeometry.Analysis.Sobolev.Euclidean
