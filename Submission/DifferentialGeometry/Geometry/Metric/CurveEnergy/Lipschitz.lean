import Submission.DifferentialGeometry.Geometry.Metric.ScalarCurveComparison
import Submission.DifferentialGeometry.Geometry.Metric.LipschitzCurves
import Submission.DifferentialGeometry.Topology.EMetricSpace.FiniteDistanceLipschitz
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Submission.DifferentialGeometry.Geometry.Metric.SmoothLipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

private theorem norm_sub_sq_le_length_mul_integral_deriv_sq
    {ν : ℝ → ℝ} {C : ℝ≥0} (hν : LipschitzWith C ν) {a b : ℝ} (hab : a ≤ b) :
    ‖ν b - ν a‖ ^ 2 ≤ (b - a) * ∫ t in _root_.Set.Icc a b, ‖deriv ν t‖ ^ 2 := by
  let μ : _root_.MeasureTheory.Measure ℝ := volume.restrict (_root_.Set.Icc a b)
  let : _root_.MeasureTheory.IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hd : _root_.MeasureTheory.MemLp (deriv ν) 2 μ := MemLp.of_bound (aestronglyMeasurable_deriv ν _) C
    (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hν)
  have hac := hν.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  have hnorm : ‖ν b - ν a‖ ≤ ∫ t, ‖deriv ν t‖ ∂μ := by
    rw [← hac.integral_deriv_eq_sub]
    calc
      _ ≤ ∫ t in _root_.Set.uIoc a b, ‖deriv ν t‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ = ∫ t, ‖deriv ν t‖ ∂μ := by
        rw [_root_.Set.uIoc_of_le hab]
        exact integral_Icc_eq_integral_Ioc.symm
  have hholder : (∫ t, ‖deriv ν t‖ ∂μ) ≤
      Real.sqrt (b - a) * Real.sqrt (∫ t, ‖deriv ν t‖ ^ 2 ∂μ) := by
    have h := _root_.MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
      (f := fun _ : ℝ => (1 : ℝ)) (g := fun t => ‖deriv ν t‖)
      (by simpa using (_root_.MeasureTheory.memLp_const (p := 2) (μ := μ) (1 : ℝ)))
      (by simpa using hd.norm)
    simpa only [_root_.NormOneClass.norm_one, norm_norm, one_mul, one_pow, _root_.MeasureTheory.integral_const, Measure.real, μ,
      Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul, mul_one,
      Real.one_rpow, Real.rpow_two, ← Real.sqrt_eq_rpow] using h
  have hnonneg : 0 ≤ ∫ t, ‖deriv ν t‖ ^ 2 ∂μ := _root_.MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  calc
    ‖ν b - ν a‖ ^ 2 ≤
        (Real.sqrt (b - a) * Real.sqrt (∫ t, ‖deriv ν t‖ ^ 2 ∂μ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hholder) 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hab), Real.sq_sqrt hnonneg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.norm_sub_sq_le_length_mul_integral_deriv_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.norm_sub_sq_le_length_mul_integral_deriv_sq target :: scope.openDecls } }

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_toReal_sq_le_interval_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    {a b : ℝ} (hab : a ≤ b)
    (henergy : _root_.MeasureTheory.IntegrableOn (fun t => (riemannianCurveSpeed g γ t) ^ 2) (_root_.Set.Icc a b)) :
    (riemannianEDistOf g (γ a) (γ b)).toReal ^ 2 ≤
      (b - a) * ∫ t in _root_.Set.Icc a b, (riemannianCurveSpeed g γ t) ^ 2 := by
  let : IsManifold 𝓘(ℝ, E) 1 M :=
    IsManifold.of_le (I := 𝓘(ℝ, E)) (M := M) (n := ∞) (by decide)
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  have hγLip : LipschitzWith C γ := hγ
  have hfin (t : ℝ) : _root_.EDist.edist (γ t) (γ a) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top t a)) (hγLip t a)
  let ν : ℝ → ℝ := fun t => (_root_.EDist.edist (γ t) (γ a)).toReal
  have hν : LipschitzWith C ν := EMetric.lipschitzWith_toReal_edist_comp hγLip (γ a) hfin
  have hνa : ν a = 0 := by simp only [ν, _root_.PseudoEMetricSpace.edist_self, ENNReal.toReal_zero]
  have hder : ∀ᵐ t ∂volume, ‖deriv ν t‖ ^ 2 ≤ (riemannianCurveSpeed g γ t) ^ 2 := by
    filter_upwards [ae_mdifferentiableAt_riemannian_curve g hγ, hν.ae_differentiableAt_real]
      with t ht hνt
    have hb := abs_deriv_le_of_riemannian_distance_bound g ht hνt (fun y => by
      change |(_root_.EDist.edist (γ y) (γ a)).toReal - (_root_.EDist.edist (γ t) (γ a)).toReal| ≤
        (_root_.EDist.edist (γ t) (γ y)).toReal
      simpa only [_root_.PseudoEMetricSpace.edist_comm (γ y) (γ t)] using
        EMetric.abs_toReal_edist_sub_le_of_edist_ne_top (hfin y) (hfin t))
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hb) 2
  let μ : _root_.MeasureTheory.Measure ℝ := volume.restrict (_root_.Set.Icc a b)
  let : _root_.MeasureTheory.IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hd : _root_.MeasureTheory.MemLp (deriv ν) 2 μ := MemLp.of_bound (aestronglyMeasurable_deriv ν _) C
    (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hν)
  have hcompare : (∫ t in _root_.Set.Icc a b, ‖deriv ν t‖ ^ 2) ≤
      ∫ t in _root_.Set.Icc a b, (riemannianCurveSpeed g γ t) ^ 2 :=
    _root_.MeasureTheory.integral_mono_ae hd.norm.integrable_sq henergy (_root_.MeasureTheory.ae_restrict_of_ae hder)
  have hscalar := norm_sub_sq_le_length_mul_integral_deriv_sq hν hab
  rw [hνa, sub_zero, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hscalar
  have hdist : ν b = (riemannianEDistOf g (γ a) (γ b)).toReal := by
    change (_root_.EDist.edist (γ b) (γ a)).toReal = (_root_.EDist.edist (γ a) (γ b)).toReal
    rw [_root_.PseudoEMetricSpace.edist_comm]
  change ν b ^ 2 ≤ (b - a) * ∫ t in _root_.Set.Icc a b, ‖deriv ν t‖ ^ 2 at hscalar
  rw [hdist] at hscalar
  exact hscalar.trans (mul_le_mul_of_nonneg_left hcompare (sub_nonneg.mpr hab))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianEDistOf_toReal_sq_le_interval_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianEDistOf_toReal_sq_le_interval_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianEDistOf_toReal_sq_le_interval_energy ``Submission.DifferentialGeometry.Geometry.riemannianEDistOf_toReal_sq_le_interval_energy

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_le_ofReal_sqrt_interval_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    {a b : ℝ} (hab : a ≤ b)
    (henergy : _root_.MeasureTheory.IntegrableOn (fun t => (riemannianCurveSpeed g γ t) ^ 2) (_root_.Set.Icc a b)) :
    riemannianEDistOf g (γ a) (γ b) ≤ ENNReal.ofReal
      (Real.sqrt ((b - a) * ∫ t in _root_.Set.Icc a b, (riemannianCurveSpeed g γ t) ^ 2)) := by
  have hfin : riemannianEDistOf g (γ a) (γ b) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top a b)) (hγ a b)
  apply (ENNReal.le_ofReal_iff_toReal_le hfin (Real.sqrt_nonneg _)).mpr
  have hs := Real.sqrt_le_sqrt (riemannianEDistOf_toReal_sq_le_interval_energy g hγ hab henergy)
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianEDistOf_le_ofReal_sqrt_interval_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianEDistOf_le_ofReal_sqrt_interval_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianEDistOf_le_ofReal_sqrt_interval_energy ``Submission.DifferentialGeometry.Geometry.riemannianEDistOf_le_ofReal_sqrt_interval_energy

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_energy_bound_curve_range_subset_of_isCompact
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {K O : Set M}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (α : ℝ → M) (C : ℝ≥0),
      (∀ x y, riemannianEDistOf g (α x) (α y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y) →
      α 0 ∈ K →
      _root_.MeasureTheory.IntegrableOn (fun t => (riemannianCurveSpeed g α t) ^ 2) (_root_.Set.Icc (0 : ℝ) 1) →
      (∫ t in _root_.Set.Icc (0 : ℝ) 1, (riemannianCurveSpeed g α t) ^ 2) ≤ ε →
      MapsTo α (_root_.Set.Icc (0 : ℝ) 1) O := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  obtain ⟨ρ, hρ, hsep⟩ := Metric.exists_pos_forall_lt_edist hK hO.isClosed_compl
    hKO.disjoint_compl_right
  refine ⟨(ρ : ℝ) ^ 2, sq_pos_of_pos (by exact_mod_cast hρ), ?_⟩
  intro α C hα hα0 hint hsmall t ht
  have hsub : _root_.Set.Icc (0 : ℝ) t ⊆ _root_.Set.Icc (0 : ℝ) 1 := _root_.Set.Icc_subset_Icc le_rfl ht.2
  have hI : (∫ s in _root_.Set.Icc (0 : ℝ) t, (riemannianCurveSpeed g α s) ^ 2) ≤
      ∫ s in _root_.Set.Icc (0 : ℝ) 1, (riemannianCurveSpeed g α s) ^ 2 :=
    _root_.MeasureTheory.setIntegral_mono_set hint (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall hsub)
  have hI0 : 0 ≤ ∫ s in _root_.Set.Icc (0 : ℝ) t, (riemannianCurveSpeed g α s) ^ 2 :=
    _root_.MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hb : t * (∫ s in _root_.Set.Icc (0 : ℝ) t, (riemannianCurveSpeed g α s) ^ 2) ≤ (ρ : ℝ) ^ 2 :=
    (mul_le_of_le_one_left hI0 ht.2).trans (hI.trans hsmall)
  have hd := riemannianEDistOf_le_ofReal_sqrt_interval_energy g hα ht.1 (hint.mono_set hsub)
  rw [sub_zero] at hd
  have hroot : Real.sqrt (t * ∫ s in _root_.Set.Icc (0 : ℝ) t,
      (riemannianCurveSpeed g α s) ^ 2) ≤ ρ := by
    exact (Real.sqrt_le_sqrt hb).trans_eq (Real.sqrt_sq ρ.coe_nonneg)
  have hdρ : riemannianEDistOf g (α 0) (α t) ≤ (ρ : ℝ≥0∞) := by
    exact hd.trans ((ENNReal.ofReal_le_ofReal hroot).trans_eq ENNReal.ofReal_coe_nnreal)
  by_contra hnot
  exact (hsep (α 0) hα0 (α t) hnot).not_ge hdρ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_energy_bound_curve_range_subset_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_energy_bound_curve_range_subset_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_energy_bound_curve_range_subset_of_isCompact ``Submission.DifferentialGeometry.Geometry.exists_energy_bound_curve_range_subset_of_isCompact

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_curve_energy_bound_of_hasCompactSupport
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {e : M → F}
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (hes : HasCompactSupport e) :
    ∃ C : ℝ≥0, 0 < C ∧
      (∀ x y, _root_.EDist.edist (e x) (e y) ≤ (C : ℝ≥0∞) * riemannianEDistOf g x y) ∧
      ∀ (α : ℝ → M) (L : ℝ≥0),
        (∀ s t, riemannianEDistOf g (α s) (α t) ≤ (L : ℝ≥0∞) * _root_.EDist.edist s t) →
        ∀ a b : ℝ,
          _root_.MeasureTheory.IntegrableOn (fun t => (riemannianCurveSpeed g α t) ^ 2) (_root_.Set.Icc a b) →
          _root_.MeasureTheory.IntegrableOn (fun t => ‖deriv (e ∘ α) t‖ ^ 2) (_root_.Set.Icc a b) ∧
          (∫ t in _root_.Set.Icc a b, ‖deriv (e ∘ α) t‖ ^ 2) ≤
            (C : ℝ) ^ 2 * ∫ t in _root_.Set.Icc a b, (riemannianCurveSpeed g α t) ^ 2 := by
  obtain ⟨B, hB⟩ := exists_metric_mfderiv_bound_of_hasCompactSupport g he hes
  let C : ℝ≥0 := B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound (p : M) (v : TangentSpace 𝓘(ℝ, E) p) :
      ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p v : F)‖ ≤ C * Real.sqrt (g.inner p v v) :=
    (hB p v).trans (mul_le_mul_of_nonneg_right (by simp [C]) (Real.sqrt_nonneg _))
  have hLip := edist_map_le_of_metric_mfderiv_bound g hC he hbound
  refine ⟨C, hC, hLip, ?_⟩
  intro α L hα a b hint
  have hcomp : LipschitzWith (C * L) (e ∘ α) := by
    intro s t
    apply (hLip (α s) (α t)).trans
    rw [ENNReal.coe_mul, mul_assoc]
    exact mul_le_mul' le_rfl (hα s t)
  let μ := volume.restrict (_root_.Set.Icc a b)
  let : _root_.MeasureTheory.IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hd : _root_.MeasureTheory.MemLp (deriv (e ∘ α)) 2 μ := MemLp.of_bound
    (aestronglyMeasurable_deriv (e ∘ α) μ) (C * L)
    (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hcomp)
  have hpoint : ∀ᵐ t ∂volume,
      ‖deriv (e ∘ α) t‖ ^ 2 ≤ (C : ℝ) ^ 2 * (riemannianCurveSpeed g α t) ^ 2 := by
    filter_upwards [ae_mdifferentiableAt_riemannian_curve g hα] with t ht
    have heq : deriv (e ∘ α) t = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e (α t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) α t 1) := by
      rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv,
        mfderiv_comp t (he.mdifferentiableAt one_ne_zero) ht]
      rfl
    rw [heq]
    have hb := pow_le_pow_left₀ (norm_nonneg _)
      (hbound (α t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) α t 1)) 2
    rw [mul_pow] at hb
    exact hb
  refine ⟨hd.norm.integrable_sq, ?_⟩
  have h := _root_.MeasureTheory.integral_mono_ae hd.norm.integrable_sq (hint.const_mul ((C : ℝ) ^ 2))
    (_root_.MeasureTheory.ae_restrict_of_ae hpoint)
  simpa only [_root_.MeasureTheory.integral_const_mul] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_curve_energy_bound_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_curve_energy_bound_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_curve_energy_bound_of_hasCompactSupport ``Submission.DifferentialGeometry.Geometry.exists_curve_energy_bound_of_hasCompactSupport

end DifferentialGeometry.Geometry

end

end
