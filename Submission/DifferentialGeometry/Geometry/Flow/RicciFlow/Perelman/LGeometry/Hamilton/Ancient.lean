import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceCorollaries
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M]
  {D : RealTimeInterval}

theorem lHamilton_ge_neg_scalar_div_of_ancient
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : ℝ, _root_.Set.Icc a b ⊆ D.regular →
      ∃ C : ℝ, ∀ t ∈ _root_.Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (T : ℝ) {tau : ℝ} (htau : 0 < tau)
    (hregular : _root_.Set.Iic (T - tau) ⊆ D.regular)
    (x : M) (V : TangentSpace I x) :
    -(S.scalar (T - tau) x / tau) ≤ lHamilton S T tau x V := by
  have ht : T - tau ∈ D.regular := hregular (mem_Iic.mpr le_rfl)
  have h := hamilton_ancient_backward_time_trace (I := I) S hS
    hcomplete hcurv hR T ⟨tau, htau⟩ hregular x V
  change 0 ≤ -deriv (fun s : ℝ => S.scalar (T - s) x) tau -
    2 * (S.base.metric (T - tau)).inner x
      (gradientFun (I := I) (S.base.metric (T - tau))
        (S.scalar (T - tau)) x) V +
    2 * S.ricciAt (T - tau) x (vec2 V V) at h
  rw [lHamilton_eq S hS T tau ht x V]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lHamilton_ge_neg_scalar_div_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lHamilton_ge_neg_scalar_div_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lHamilton_ge_neg_scalar_div_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lHamilton_ge_neg_scalar_div_of_ancient

theorem lHamSq_ge_neg_sq_mul_scalar_of_ancient
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : ℝ, _root_.Set.Icc a b ⊆ D.regular →
      ∃ C : ℝ, ∀ t ∈ _root_.Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (T : ℝ) (alpha : ℝ → M) {s : ℝ} (hs : s ≠ 0)
    (hregular : _root_.Set.Iic (T - s ^ 2) ⊆ D.regular) :
    -(s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) ≤ lHamSq S T alpha s := by
  let V : TangentSpace I (alpha s) := (2 * s)⁻¹ • lVelocity (I := I) alpha s
  have hV : lVelocity (I := I) alpha s = (2 * s) • V := by
    dsimp only [V]
    rw [smul_smul, mul_inv_cancel₀ (mul_ne_zero (by norm_num) hs), one_smul]
  have h := mul_le_mul_of_nonneg_left
    (lHamilton_ge_neg_scalar_div_of_ancient S hS hcomplete hcurv hR T
      (sq_pos_of_ne_zero hs) hregular (alpha s) V) (pow_nonneg (by exact sq_nonneg s) 2)
  rw [lHamSq_eq S T alpha s V hV]
  calc
    -(s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) =
        (s ^ 2) ^ 2 * -(S.scalar (T - s ^ 2) (alpha s) / s ^ 2) := by
      field_simp [hs]
    _ ≤ (s ^ 2) ^ 2 * lHamilton S T (s ^ 2) (alpha s) V := h
    _ = s ^ 4 * lHamilton S T (s ^ 2) (alpha s) V := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lHamSq_ge_neg_sq_mul_scalar_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lHamSq_ge_neg_sq_mul_scalar_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lHamSq_ge_neg_sq_mul_scalar_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lHamSq_ge_neg_sq_mul_scalar_of_ancient

theorem lK_ge_neg_lRegularizedAction_of_ancient
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : ℝ, _root_.Set.Icc a b ⊆ D.regular →
      ∃ C : ℝ, ∀ t ∈ _root_.Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (T : ℝ) (alpha : ℝ → M) {b : ℝ} (hb : 0 ≤ b)
    (hregular : ∀ s ∈ _root_.Set.Ioc 0 b, _root_.Set.Iic (T - s ^ 2) ⊆ D.regular)
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha)
      MeasureTheory.volume 0 b)
    (hHam : IntervalIntegrable (lHamSq S T alpha) MeasureTheory.volume 0 b) :
    -lRegularizedAction S T alpha 0 b ≤ lK S T alpha b := by
  have hpoint (s : ℝ) (hs : s ∈ _root_.Set.Icc 0 b) :
      -lRegularizedLagrangian S T alpha s ≤ 2 * lHamSq S T alpha s := by
    by_cases hs0 : s = 0
    · subst s
      have hspeed := metric_inner_self_nonneg (S.base.metric T) (alpha 0)
        (lVelocity (I := I) alpha 0)
      norm_num [lRegularizedLagrangian, lHamSq]
      exact hspeed
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hbound := lHamSq_ge_neg_sq_mul_scalar_of_ancient S hS hcomplete hcurv hR T
      alpha hs0 (hregular s ⟨hspos, hs.2⟩)
    have hspeed : 0 ≤ (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) :=
      metric_inner_self_nonneg _ _ _
    dsimp only [lRegularizedLagrangian]
    linarith
  have h := intervalIntegral.integral_mono_on hb hLag.neg (hHam.const_mul 2) hpoint
  simpa only [Pi.neg_apply, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    lRegularizedAction, lK] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lK_ge_neg_lRegularizedAction_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lK_ge_neg_lRegularizedAction_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lK_ge_neg_lRegularizedAction_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lK_ge_neg_lRegularizedAction_of_ancient

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lK_energy_eq_of_geodesic
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (alpha : ℝ → M) {b : ℝ} (hb : 0 ≤ b)
    (hgeo : IsLRegularizedGeodesicOn S T alpha (_root_.Set.Ioo 0 b))
    (hcont : ContinuousOn (lRegularizedLagrangian S T alpha) (_root_.Set.Icc 0 b))
    (hHam : IntervalIntegrable (lHamSq S T alpha) MeasureTheory.volume 0 b) :
    lK S T alpha b =
      (lRegularizedAction S T alpha 0 b - b * lRegularizedLagrangian S T alpha b) / 2 := by
  have h := integral_lHamSq_eq_boundary_of_geodesic S hS T alpha hb hgeo hcont hHam
  simp only [_root_.MulZeroClass.zero_mul, sub_zero] at h
  dsimp only [lK]
  linarith only [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lK_energy_eq_of_geodesic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lK_energy_eq_of_geodesic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lK_energy_eq_of_geodesic ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lK_energy_eq_of_geodesic

theorem lRegularizedLagrangian_mul_le_three_mul_action_of_ancient
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : ℝ, _root_.Set.Icc a b ⊆ D.regular →
      ∃ C : ℝ, ∀ t ∈ _root_.Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (T : ℝ) (alpha : ℝ → M) {b : ℝ} (hb : 0 ≤ b)
    (hregular : ∀ s ∈ _root_.Set.Ioo 0 b, _root_.Set.Iic (T - s ^ 2) ⊆ D.regular)
    (hgeo : IsLRegularizedGeodesicOn S T alpha (_root_.Set.Ioo 0 b))
    (hcont : ContinuousOn (lRegularizedLagrangian S T alpha) (_root_.Set.Icc 0 b)) :
    b * lRegularizedLagrangian S T alpha b ≤ 3 * lRegularizedAction S T alpha 0 b := by
  let G : ℝ → ℝ := fun s => s * lRegularizedLagrangian S T alpha s -
    3 * lRegularizedAction S T alpha 0 s
  have hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) MeasureTheory.volume 0 b :=
    hcont.intervalIntegrable_of_Icc hb
  have hactionCont : ContinuousOn (fun s => lRegularizedAction S T alpha 0 s) (_root_.Set.Icc 0 b) := by
    simpa only [lRegularizedAction, _root_.Set.uIcc_of_le hb] using
      intervalIntegral.continuousOn_primitive_interval' hLag (a := 0) _root_.Set.left_mem_uIcc
  have hGcont : ContinuousOn G (_root_.Set.Icc 0 b) :=
    (continuousOn_id.mul hcont).sub (continuousOn_const.mul hactionCont)
  have hcurve : IsLRegularizedCurveOn S T alpha (_root_.Set.Ioo 0 b) (alpha 0)
      ((1 / 2 : ℝ) • lVelocity (I := I) alpha 0) := by
    refine ⟨rfl, ?_, hgeo⟩
    rw [two_smul, ← add_smul]
    norm_num
  have hderiv (s : ℝ) (hs : s ∈ _root_.Set.Ioo 0 b) :
      HasDerivAt G (-2 * lRegularizedLagrangian S T alpha s - 4 * lHamSq S T alpha s) s := by
    have hscc : s ∈ _root_.Set.Icc 0 b := ⟨hs.1.le, hs.2.le⟩
    let _ : Fact (s ∈ _root_.Set.Icc 0 b) := ⟨hscc⟩
    have hhead : IntervalIntegrable (lRegularizedLagrangian S T alpha) MeasureTheory.volume 0 s :=
      hLag.mono_set (by rw [_root_.Set.uIcc_of_le hs.1.le, _root_.Set.uIcc_of_le hb]; exact _root_.Set.Icc_subset_Icc le_rfl hs.2.le)
    have hFTC : HasDerivWithinAt
        (fun r => ∫ q in (0 : ℝ)..r, lRegularizedLagrangian S T alpha q)
        (lRegularizedLagrangian S T alpha s) (_root_.Set.Icc 0 b) s :=
      intervalIntegral.integral_hasDerivWithinAt_right hhead
      (hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s) (hcont s hscc)
    have ha : HasDerivAt (fun r => lRegularizedAction S T alpha 0 r)
        (lRegularizedLagrangian S T alpha s) s :=
      hFTC.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have h := (lLagMul_deriv S hS T hcurve hs).sub (ha.const_mul 3)
    apply h.congr_deriv
    ring
  have hnonpos (s : ℝ) (hs : s ∈ _root_.Set.Ioo 0 b) :
      -2 * lRegularizedLagrangian S T alpha s - 4 * lHamSq S T alpha s ≤ 0 := by
    have hHam := lHamSq_ge_neg_sq_mul_scalar_of_ancient S hS hcomplete hcurv hR T
      alpha (ne_of_gt hs.1) (hregular s hs)
    have hspeed := metric_inner_self_nonneg (S.base.metric (T - s ^ 2)) (alpha s)
      (lVelocity (I := I) alpha s)
    dsimp only [lRegularizedLagrangian]
    linarith
  have hanti : AntitoneOn G (_root_.Set.Icc 0 b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 b) hGcont
    · intro s hs
      have hs' : s ∈ _root_.Set.Ioo 0 b := by simpa only [interior_Icc] using hs
      exact (hderiv s hs').differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ _root_.Set.Ioo 0 b := by simpa only [interior_Icc] using hs
      rw [(hderiv s hs').deriv]
      exact hnonpos s hs'
  have h := hanti ⟨le_rfl, hb⟩ ⟨hb, le_rfl⟩ hb
  dsimp only [G] at h
  have hzero : lRegularizedAction S T alpha 0 0 = 0 := intervalIntegral.integral_same
  rw [hzero, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.mul_zero, sub_zero] at h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_mul_le_three_mul_action_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_mul_le_three_mul_action_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_mul_le_three_mul_action_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_mul_le_three_mul_action_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman
