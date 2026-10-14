import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.Smooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def chartPulledWeightedMeasure (g : SmoothRiemannianMetric I M) (α : M) :
    Measure EuclN :=
  (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).withDensity
    (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.chartPulledWeightedMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.chartPulledWeightedMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.chartPulledWeightedMeasure ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.chartPulledWeightedMeasure

structure ChartBilinearH1ComplData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) where
  uChart : EuclN → ℝ
  fChart : EuclN → ℝ
  weakPartial : Fin (Module.finrank ℝ E) → EuclN → ℝ
  u_chart_memLp_weighted :
    _root_.MeasureTheory.MemLp uChart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
  f_chart_memLp_weighted :
    _root_.MeasureTheory.MemLp fChart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
  weak_partial_locally_memLp :
    ∀ i, ∀ K : Set EuclN, IsCompact K → K ⊆ chartTargetEuclid (I := I) (M := M) α →
      _root_.MeasureTheory.MemLp (weakPartial i) 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K)
  weak_partial_isWeakPartial :
    ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (weakPartial i) uChart
      (chartTargetEuclid (I := I) (M := M) α)
  variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              weakPartial i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * uChart y * ψ y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * fChart y * ψ y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.ChartBilinearH1ComplData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.ChartBilinearH1ComplData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.ChartBilinearH1ComplData ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.ChartBilinearH1ComplData

omit [NeZero (Module.finrank ℝ E)] in
theorem chart_bilinear_identity_h1Compl
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.uChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.fChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
  D.variational_identity ψ hψ hψ_cs hψ_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.chart_bilinear_identity_h1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.chart_bilinear_identity_h1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.chart_bilinear_identity_h1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.chart_bilinear_identity_h1Compl

omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclid_bounded_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c_min c_max : ℝ, 0 < c_min ∧ c_min ≤ c_max ∧
      ∀ y ∈ K, c_min ≤ densityOnEuclid (I := I) g α y ∧
        densityOnEuclid (I := I) g α y ≤ c_max := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨1, 1, by norm_num, le_refl _, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_dens_contOn : ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (densityOnEuclid_contDiffOn (I := I) g α).continuousOn
  have h_dens_contOn_K : ContinuousOn (densityOnEuclid (I := I) g α) K :=
    h_dens_contOn.mono hK_in
  have h_dens_pos : ∀ y ∈ K, 0 < densityOnEuclid (I := I) g α y :=
    fun y hy => densityOnEuclid_pos (I := I) g α (hK_in hy)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  obtain ⟨y_min, hy_min, h_min_eq⟩ := hK.exists_isMinOn h_K_ne h_dens_contOn_K
  obtain ⟨y_max, hy_max, h_max_eq⟩ := hK.exists_isMaxOn h_K_ne h_dens_contOn_K
  set c_min : ℝ := densityOnEuclid (I := I) g α y_min with hcmin_def
  set c_max : ℝ := densityOnEuclid (I := I) g α y_max with hcmax_def
  have hc_min_pos : 0 < c_min := h_dens_pos y_min hy_min
  have hc_min_le_max : c_min ≤ c_max := by
    have h := h_min_eq hy_max
    exact h
  refine ⟨c_min, c_max, hc_min_pos, hc_min_le_max, ?_⟩
  intro y hy
  refine ⟨h_min_eq hy, h_max_eq hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.densityOnEuclid_bounded_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.densityOnEuclid_bounded_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.densityOnEuclid_bounded_on_compact ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.densityOnEuclid_bounded_on_compact

omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclid_continuousOn (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densityOnEuclid_contDiffOn (I := I) g α).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.densityOnEuclid_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.densityOnEuclid_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.densityOnEuclid_continuousOn ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.densityOnEuclid_continuousOn

omit [NeZero (Module.finrank ℝ E)] in
lemma volume_restrict_compact_le_chartPulledWeightedMeasure
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c : ℝ, 0 < c ∧
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K ≤
        ENNReal.ofReal c •
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  obtain ⟨c_min, _c_max, hc_min_pos, _hc_le, h_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  refine ⟨1 / c_min, by positivity, ?_⟩
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.restrict_apply hA]
  rw [Measure.smul_apply, Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [_root_.MeasureTheory.withDensity_apply _ (hA.inter (chartTargetEuclid_isOpen
    (I := I) (M := M) α).measurableSet)]
  have h_subset : A ∩ K ⊆ A ∩ chartTargetEuclid (I := I) (M := M) α :=
    Set.inter_subset_inter_right A hK_in
  have h_setmono :
      ∫⁻ y in A ∩ K, ENNReal.ofReal (densityOnEuclid (I := I) g α y) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      ∫⁻ y in A ∩ chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal (densityOnEuclid (I := I) g α y) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    apply MeasureTheory.lintegral_mono_set h_subset
  have h_pointwise_bd :
      ∫⁻ y in A ∩ K, ENNReal.ofReal c_min ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      ∫⁻ y in A ∩ K, ENNReal.ofReal (densityOnEuclid (I := I) g α y) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    apply MeasureTheory.setLIntegral_mono_ae'
    · exact hA.inter hK_meas
    · refine Filter.Eventually.of_forall fun y hy => ?_
      apply ENNReal.ofReal_le_ofReal
      exact (h_bd y hy.2).1
  have h_const_eval :
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_min ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ENNReal.ofReal c_min * (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) (A ∩ K) := by
    rw [MeasureTheory.setLIntegral_const]
  have h_step1 : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) (A ∩ K) =
      ENNReal.ofReal (1 / c_min) *
        (ENNReal.ofReal c_min * (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) (A ∩ K)) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    rw [show (1 / c_min) * c_min = 1 from by field_simp]
    rw [ENNReal.ofReal_one, one_mul]
  rw [h_step1]
  rw [smul_eq_mul]
  gcongr
  exact le_trans (le_of_eq h_const_eval.symm) (h_pointwise_bd.trans h_setmono)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.volume_restrict_compact_le_chartPulledWeightedMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.volume_restrict_compact_le_chartPulledWeightedMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.volume_restrict_compact_le_chartPulledWeightedMeasure ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.volume_restrict_compact_le_chartPulledWeightedMeasure

omit [NeZero (Module.finrank ℝ E)] in
lemma memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {α : M} {w : EuclN → ℝ}
    (hw : _root_.MeasureTheory.MemLp w 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp w 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
  classical
  obtain ⟨c, _hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      α hK_compact hK_meas hK_in
  exact hw.of_measure_le_smul (c := ENNReal.ofReal c) ENNReal.ofReal_ne_top h_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure

end ChartBilinearH1Compl
end Laplacian
end Analysis
end DifferentialGeometry
