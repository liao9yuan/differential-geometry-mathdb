import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.FiniteProduct
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.MetricSpace.Pseudo.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

private abbrev HsPi (q : ℝ) := PiLp 2 (fun _ : ι => TensorHs g r s q)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.HsPi
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.HsPi target :: scope.openDecls } }

private local instance vectorTensorHsNormedSpace (q : ℝ) :
    NormedSpace ℝ (PiLp 2 (fun _ : ι => TensorHs g r s q)) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.vectorTensorHsNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.vectorTensorHsNormedSpace target :: scope.openDecls } }

theorem norm_sub_le_of_continuousOn_duhamel_representatives
    (hT : 0 < T)
    (F G : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T)
    (W V : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1))
    (hW : ContinuousOn W (_root_.Set.Icc (0 : ℝ) T))
    (hV : ContinuousOn V (_root_.Set.Icc (0 : ℝ) T))
    (hWF : W =ᵐ[timeMeasure T] fun t =>
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith)))
        (maximalRegularityDuhamelVectorField hT 0 F t))
    (hVG : V =ᵐ[timeMeasure T] fun t =>
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith)))
        (maximalRegularityDuhamelVectorField hT 0 G t)) :
    ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ‖W t - V t‖ ≤ Real.sqrt (1 + T) * ‖F - G‖ := by
  let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
  have hsub : maximalRegularityDuhamelVectorField hT 0 F -
      maximalRegularityDuhamelVectorField hT 0 G =
      maximalRegularityDuhamelVectorField hT 0 (F - G) := by
    rw [← maximalRegularityVectorFieldL_eq_duhamel hT F,
      ← maximalRegularityVectorFieldL_eq_duhamel hT G,
      ← maximalRegularityVectorFieldL_eq_duhamel hT (F - G), map_sub]
  have hsubae := Lp.coeFn_sub (maximalRegularityDuhamelVectorField hT 0 F)
    (maximalRegularityDuhamelVectorField hT 0 G)
  rw [hsub] at hsubae
  have hbound := maximalRegularityDuhamelVectorField_Ha1_ae_pointwise_le hT (F - G)
  have hae : ∀ᵐ t ∂timeMeasure T,
      ‖W t - V t‖ ≤ Real.sqrt (1 + T) * ‖F - G‖ := by
    filter_upwards [hWF, hVG, hsubae, hbound] with t hwt hvt hst ht
    change ‖J (maximalRegularityDuhamelVectorField hT 0 (F - G) t)‖ ≤ _ at ht
    change W t = J (maximalRegularityDuhamelVectorField hT 0 F t) at hwt
    change V t = J (maximalRegularityDuhamelVectorField hT 0 G t) at hvt
    simp only [Pi.sub_apply] at hst
    rw [hwt, hvt, ← map_sub, ← hst]
    exact ht
  have hnorm : ContinuousOn (fun t => ‖W t - V t‖) (_root_.Set.Icc (0 : ℝ) T) :=
    (hW.sub hV).norm
  have hmin : (fun t => _root_.Min.min ‖W t - V t‖ (Real.sqrt (1 + T) * ‖F - G‖))
      =ᵐ[timeMeasure T] fun t => ‖W t - V t‖ :=
    hae.mono fun t ht => min_eq_left ht
  intro t ht
  exact min_eq_left_iff.mp
    (Measure.eqOn_Icc_of_ae_eq (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) hT.ne hmin
      (hnorm.inf continuousOn_const) hnorm ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.norm_sub_le_of_continuousOn_duhamel_representatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.norm_sub_le_of_continuousOn_duhamel_representatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.norm_sub_le_of_continuousOn_duhamel_representatives ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.norm_sub_le_of_continuousOn_duhamel_representatives

theorem tendstoUniformlyOn_continuousOn_duhamel_representatives
    {P : Type*} {l : Filter P} (hT : 0 < T)
    (F₀ : timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T)
    (F : P → timeL2 (HsPi (ι := ι) (g := g) (r := r) (s := s) a) T)
    (W₀ : ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1))
    (W : P → ℝ → HsPi (ι := ι) (g := g) (r := r) (s := s) (a + 1))
    (hW₀ : ContinuousOn W₀ (_root_.Set.Icc (0 : ℝ) T))
    (hW : ∀ p, ContinuousOn (W p) (_root_.Set.Icc (0 : ℝ) T))
    (hpin₀ : W₀ =ᵐ[timeMeasure T] fun t =>
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith)))
        (maximalRegularityDuhamelVectorField hT 0 F₀ t))
    (hpin : ∀ p, W p =ᵐ[timeMeasure T] fun t =>
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith)))
        (maximalRegularityDuhamelVectorField hT 0 (F p) t))
    (hF : _root_.Filter.Tendsto F l (𝓝 F₀)) :
    TendstoUniformlyOn W W₀ l (_root_.Set.Icc (0 : ℝ) T) := by
  have hnorm : _root_.Filter.Tendsto (fun p => ‖F p - F₀‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hF
  have hsmall : _root_.Filter.Tendsto (fun p => Real.sqrt (1 + T) * ‖F p - F₀‖) l (𝓝 0) := by
    simpa only [_root_.MulZeroClass.mul_zero] using hnorm.const_mul (Real.sqrt (1 + T))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with p hp
  intro t ht
  have hle := norm_sub_le_of_continuousOn_duhamel_representatives hT
    (F p) F₀ (W p) W₀ (hW p) hW₀ (hpin p) hpin₀ t ht
  rw [dist_comm, dist_eq_norm]
  exact hle.trans_lt hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tendstoUniformlyOn_continuousOn_duhamel_representatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tendstoUniformlyOn_continuousOn_duhamel_representatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tendstoUniformlyOn_continuousOn_duhamel_representatives ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tendstoUniformlyOn_continuousOn_duhamel_representatives

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
