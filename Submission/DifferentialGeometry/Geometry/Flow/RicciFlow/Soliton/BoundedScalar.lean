import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Canonical

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]

theorem metricScalarAt_eq_zero_of_canonicalMetricFamily_scalar_bounded
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    {sigma C : ℝ} (hsigma : 0 < sigma)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hbound : ∀ᶠ t in 𝓝[<] sigma⁻¹, ∀ x : M,
      |metricScalarAt (canonicalMetricFamily g f sigma hcomplete hsol t) x| ≤ C)
    (x : M) : metricScalarAt (I := I) g x = 0 := by
  have htime : _root_.Filter.Tendsto (fun c : ℝ => (1 - c) / sigma)
      (𝓝[>] (0 : ℝ)) (𝓝[<] sigma⁻¹) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : _root_.Filter.Tendsto (fun c : ℝ => c) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hconst : _root_.Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
        tendsto_const_nhds
      simpa only [sub_zero, one_div] using (hconst.sub hc).div_const sigma
    · filter_upwards [self_mem_nhdsWithin] with c hc
      change (1 - c) / sigma < sigma⁻¹
      rw [inv_eq_one_div]
      exact div_lt_div_of_pos_right (sub_lt_self 1 hc) hsigma
  have hsmall : ∀ᶠ c in 𝓝[>] (0 : ℝ), |metricScalarAt (I := I) g x| ≤ c * C := by
    filter_upwards [self_mem_nhdsWithin, htime.eventually hbound] with c hc hboundc
    let t := (1 - c) / sigma
    have hscale : 1 - sigma * t = c := by
      dsimp only [t]
      field_simp [hsigma.ne']
      ring
    have ht : t ∈ canonicalTimeDomain sigma := by
      change 0 < 1 - sigma * t
      rwa [hscale]
    let Phi := canonicalFlowDiffeomorph g f sigma hcomplete hsol
      (canonicalFlowParameter sigma t)
    have hPhi : canonicalFlowMap g f sigma hcomplete hsol
        (canonicalFlowParameter sigma t) (Phi.symm x) = x := by
      rw [← canonicalFlowDiffeomorph_apply]
      exact Phi.apply_symm_apply x
    have h := hboundc (Phi.symm x)
    rw [canonicalMetricFamily_eq g f sigma hcomplete hsol ht,
      canonicalMetric_scalar, hscale, hPhi, abs_mul,
      abs_of_pos (inv_pos.mpr hc)] at h
    have hdiv : |metricScalarAt (I := I) g x| / c ≤ C := by
      simpa only [div_eq_mul_inv, mul_comm] using h
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hdiv
  have hlim : _root_.Filter.Tendsto (fun c : ℝ => c * C) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc : _root_.Filter.Tendsto (fun c : ℝ => c) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [_root_.MulZeroClass.zero_mul] using hc.mul_const C
  have hzero : |metricScalarAt (I := I) g x| ≤ 0 := ge_of_tendsto hlim hsmall
  exact abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Soliton.metricScalarAt_eq_zero_of_canonicalMetricFamily_scalar_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Soliton.metricScalarAt_eq_zero_of_canonicalMetricFamily_scalar_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Soliton.metricScalarAt_eq_zero_of_canonicalMetricFamily_scalar_bounded ``Submission.DifferentialGeometry.PDE.RicciFlow.Soliton.metricScalarAt_eq_zero_of_canonicalMetricFamily_scalar_bounded

end DifferentialGeometry.PDE.RicciFlow.Soliton
