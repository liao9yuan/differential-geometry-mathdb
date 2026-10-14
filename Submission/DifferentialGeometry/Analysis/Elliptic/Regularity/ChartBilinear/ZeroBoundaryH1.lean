import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl

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

omit [NeZero (Module.finrank ℝ E)] in
private lemma weightedInvGramOnEuclid_bounded_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |weightedInvGramOnEuclid (I := I) g α i j y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, le_refl _, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_pull : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have h_pull_K : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j) K :=
    h_pull.mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |weightedInvGramOnEuclid (I := I) g α i j y|) K :=
    continuous_abs.comp_continuousOn h_pull_K
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  obtain ⟨y_max, hy_max, h_max_eq⟩ := hK.exists_isMaxOn hKne h_abs_K
  refine ⟨|weightedInvGramOnEuclid (I := I) g α i j y_max|, abs_nonneg _, ?_⟩
  intro y hy
  exact h_max_eq hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.weightedInvGramOnEuclid_bounded_on_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.weightedInvGramOnEuclid_bounded_on_compact target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma densityOnEuclid_bounded_above_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, densityOnEuclid (I := I) g α y ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, le_refl _, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_cont : ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (densityOnEuclid_contDiffOn (I := I) g α).continuousOn
  have h_cont_K : ContinuousOn (densityOnEuclid (I := I) g α) K :=
    h_cont.mono hK_in
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  obtain ⟨y_max, hy_max, h_max_eq⟩ := hK.exists_isMaxOn hKne h_cont_K
  set C : ℝ := densityOnEuclid (I := I) g α y_max with hC_def
  have hC_nn : 0 ≤ C :=
    le_of_lt (densityOnEuclid_pos (I := I) g α (hK_in hy_max))
  refine ⟨C, hC_nn, ?_⟩
  intro y hy
  exact h_max_eq hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.densityOnEuclid_bounded_above_on_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.densityOnEuclid_bounded_above_on_compact target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma tendsto_setIntegral_mul_of_eLpNorm_tendsto_zero_l2
    {μ : _root_.MeasureTheory.Measure EuclN} {Y : EuclN → ℝ} {ψ_n : ℕ → EuclN → ℝ} {ψ : EuclN → ℝ}
    (hY : _root_.MeasureTheory.MemLp Y 2 μ)
    (hψ_n_lp : ∀ n, _root_.MeasureTheory.MemLp (ψ_n n) 2 μ)
    (hψ_lp : _root_.MeasureTheory.MemLp ψ 2 μ)
    (h_tendsto :
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => ψ_n n x - ψ x) 2 μ) _root_.Filter.atTop (𝓝 0)) :
    _root_.Filter.Tendsto (fun n => ∫ x, Y x * ψ_n n x ∂μ) _root_.Filter.atTop
      (𝓝 (∫ x, Y x * ψ x ∂μ)) := by
  classical
  have hpqT : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := by
    refine ⟨?_⟩
    rw [inv_one]
    rw [show ((2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹) = 2 * (2 : ℝ≥0∞)⁻¹ from by ring]
    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have h_diff_lp : ∀ n, _root_.MeasureTheory.MemLp (fun x => ψ_n n x - ψ x) 2 μ := fun n =>
    (hψ_n_lp n).sub hψ_lp
  have h_bound_pointwise : ∀ n,
      ENNReal.ofReal |∫ x, Y x * (ψ_n n x - ψ x) ∂μ|
        ≤ _root_.MeasureTheory.eLpNorm Y 2 μ * _root_.MeasureTheory.eLpNorm (fun x => ψ_n n x - ψ x) 2 μ := by
    intro n
    have h_abs_le_lintegral :
        ENNReal.ofReal |∫ x, Y x * (ψ_n n x - ψ x) ∂μ| ≤
          ∫⁻ x, ‖Y x * (ψ_n n x - ψ x)‖ₑ ∂μ := by
      rw [← Real.norm_eq_abs]
      have hint : ‖∫ x, Y x * (ψ_n n x - ψ x) ∂μ‖ₑ ≤
          ∫⁻ x, ‖Y x * (ψ_n n x - ψ x)‖ₑ ∂μ :=
        _root_.MeasureTheory.enorm_integral_le_lintegral_enorm _
      have hofreal :
          ENNReal.ofReal ‖∫ x, Y x * (ψ_n n x - ψ x) ∂μ‖ =
            ‖∫ x, Y x * (ψ_n n x - ψ x) ∂μ‖ₑ :=
        ofReal_norm _
      rw [hofreal]
      exact hint
    have h_lintegral_eq :
        ∫⁻ x, ‖Y x * (ψ_n n x - ψ x)‖ₑ ∂μ =
          eLpNorm (fun x => (ψ_n n x - ψ x) * Y x) 1 μ := by
      rw [_root_.MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      refine _root_.MeasureTheory.lintegral_congr (fun x => ?_)
      simp [enorm_mul, mul_comm]
    have h_smul_bound :
        _root_.MeasureTheory.eLpNorm (fun x => (ψ_n n x - ψ x) * Y x) 1 μ ≤
          eLpNorm (fun x => ψ_n n x - ψ x) 2 μ * _root_.MeasureTheory.eLpNorm Y 2 μ := by
      have h_mul_eq :
          (fun x => (ψ_n n x - ψ x) * Y x) =
            (fun x => ψ_n n x - ψ x) • (Y : EuclN → ℝ) := by
        funext x
        simp [smul_eq_mul]
      rw [h_mul_eq]
      exact _root_.MeasureTheory.eLpNorm_smul_le_mul_eLpNorm hY.aestronglyMeasurable
        (h_diff_lp n).aestronglyMeasurable
    calc
      ENNReal.ofReal |∫ x, Y x * (ψ_n n x - ψ x) ∂μ|
          ≤ ∫⁻ x, ‖Y x * (ψ_n n x - ψ x)‖ₑ ∂μ := h_abs_le_lintegral
      _ = _root_.MeasureTheory.eLpNorm (fun x => (ψ_n n x - ψ x) * Y x) 1 μ := h_lintegral_eq
      _ ≤ _root_.MeasureTheory.eLpNorm (fun x => ψ_n n x - ψ x) 2 μ * _root_.MeasureTheory.eLpNorm Y 2 μ := h_smul_bound
      _ = _root_.MeasureTheory.eLpNorm Y 2 μ * _root_.MeasureTheory.eLpNorm (fun x => ψ_n n x - ψ x) 2 μ := mul_comm _ _
  have h_diff_int_tendsto :
      Tendsto (fun n => ∫ x, Y x * (ψ_n n x - ψ x) ∂μ) _root_.Filter.atTop (𝓝 0) := by
    have h_eLpNorm_Y_lt_top : _root_.MeasureTheory.eLpNorm Y 2 μ < (∞ : ℝ≥0∞) := hY.eLpNorm_lt_top
    have h_rhs_tendsto :
        _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm Y 2 μ *
            eLpNorm (fun x => ψ_n n x - ψ x) 2 μ) _root_.Filter.atTop (𝓝 0) := by
      have htm := ENNReal.Tendsto.const_mul (a := _root_.MeasureTheory.eLpNorm Y 2 μ) h_tendsto
        (Or.inr h_eLpNorm_Y_lt_top.ne)
      simpa using htm
    have h_le_real : ∀ n,
        |∫ x, Y x * (ψ_n n x - ψ x) ∂μ| ≤
          (_root_.MeasureTheory.eLpNorm Y 2 μ * _root_.MeasureTheory.eLpNorm (fun x => ψ_n n x - ψ x) 2 μ).toReal := by
      intro n
      have h_finite : _root_.MeasureTheory.eLpNorm Y 2 μ * _root_.MeasureTheory.eLpNorm (fun x => ψ_n n x - ψ x) 2 μ ≠ (∞ : ℝ≥0∞) :=
        ENNReal.mul_ne_top h_eLpNorm_Y_lt_top.ne (h_diff_lp n).eLpNorm_lt_top.ne
      have h_ofreal := h_bound_pointwise n
      have h_toReal : (ENNReal.ofReal |∫ x, Y x * (ψ_n n x - ψ x) ∂μ|).toReal ≤
          (_root_.MeasureTheory.eLpNorm Y 2 μ * _root_.MeasureTheory.eLpNorm (fun x => ψ_n n x - ψ x) 2 μ).toReal :=
        ENNReal.toReal_mono h_finite h_ofreal
      have hnn : 0 ≤ |∫ x, Y x * (ψ_n n x - ψ x) ∂μ| := abs_nonneg _
      simpa [ENNReal.toReal_ofReal hnn] using h_toReal
    have h_ge : ∀ n, 0 ≤ |∫ x, Y x * (ψ_n n x - ψ x) ∂μ| := fun _ => abs_nonneg _
    have h_rhs_real_tendsto :
        _root_.Filter.Tendsto (fun n => (_root_.MeasureTheory.eLpNorm Y 2 μ *
            eLpNorm (fun x => ψ_n n x - ψ x) 2 μ).toReal) _root_.Filter.atTop (𝓝 0) := by
      have hcomp := (ENNReal.tendsto_toReal_zero_iff (f := fun n =>
        _root_.MeasureTheory.eLpNorm Y 2 μ * _root_.MeasureTheory.eLpNorm (fun x => ψ_n n x - ψ x) 2 μ)
        (fun n => ENNReal.mul_ne_top h_eLpNorm_Y_lt_top.ne
          (h_diff_lp n).eLpNorm_lt_top.ne)).mpr h_rhs_tendsto
      exact hcomp
    have h_abs_tendsto :
        Tendsto (fun n => |∫ x, Y x * (ψ_n n x - ψ x) ∂μ|) _root_.Filter.atTop (𝓝 0) :=
      squeeze_zero h_ge h_le_real h_rhs_real_tendsto
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 h_abs_tendsto
  have h_eq : ∀ n,
      ∫ x, Y x * ψ_n n x ∂μ =
        (∫ x, Y x * ψ x ∂μ) + ∫ x, Y x * (ψ_n n x - ψ x) ∂μ := by
    intro n
    have hY_psi : _root_.MeasureTheory.Integrable (fun x => Y x * ψ x) μ := by
      have h := MemLp.integrable_mul (μ := μ) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        hY hψ_lp
      have heq : (Y * ψ) = (fun x => Y x * ψ x) := rfl
      rw [heq] at h
      exact h
    have hY_diff : _root_.MeasureTheory.Integrable (fun x => Y x * (ψ_n n x - ψ x)) μ := by
      have h := MemLp.integrable_mul (μ := μ) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        hY (h_diff_lp n)
      have heq : (Y * (fun x => ψ_n n x - ψ x)) =
          (fun x => Y x * (ψ_n n x - ψ x)) := rfl
      rw [heq] at h
      exact h
    calc
      ∫ x, Y x * ψ_n n x ∂μ
          = ∫ x, (Y x * ψ x) + Y x * (ψ_n n x - ψ x) ∂μ := by
              congr with x
              ring
      _ = (∫ x, Y x * ψ x ∂μ) + ∫ x, Y x * (ψ_n n x - ψ x) ∂μ :=
            _root_.MeasureTheory.integral_add hY_psi hY_diff
  have h_aux :
      _root_.Filter.Tendsto
        (fun n => (∫ x, Y x * ψ x ∂μ) + ∫ x, Y x * (ψ_n n x - ψ x) ∂μ)
        atTop (𝓝 ((∫ x, Y x * ψ x ∂μ) + 0)) :=
    Tendsto.const_add _ h_diff_int_tendsto
  have h_aux' :
      _root_.Filter.Tendsto (fun n => ∫ x, Y x * ψ_n n x ∂μ) _root_.Filter.atTop
        (𝓝 ((∫ x, Y x * ψ x ∂μ) + 0)) := by
    simpa [h_eq] using h_aux
  simpa [add_zero] using h_aux'

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.tendsto_setIntegral_mul_of_eLpNorm_tendsto_zero_l2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.tendsto_setIntegral_mul_of_eLpNorm_tendsto_zero_l2 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma uChart_memLp_volume_restrict_compact
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp D.uChart 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) :=
  memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    (D.u_chart_memLp_weighted) hK_compact hK_meas hK_in

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.uChart_memLp_volume_restrict_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.uChart_memLp_volume_restrict_compact target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma fChart_memLp_volume_restrict_compact
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp D.fChart 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) :=
  memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    (D.f_chart_memLp_weighted) hK_compact hK_meas hK_in

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.fChart_memLp_volume_restrict_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.fChart_memLp_volume_restrict_compact target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem chart_bilinear_identity_h1_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    (ψ : EuclN → ℝ)
    (weak_partial_ψ : Fin (Module.finrank ℝ E) → EuclN → ℝ)
    (hψ_l2 : _root_.MeasureTheory.MemLp ψ 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0))
    (hψ_grad_l2 : ∀ j : Fin (Module.finrank ℝ E),
      _root_.MeasureTheory.MemLp (weak_partial_ψ j) 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0))
    (ψ_seq : ℕ → EuclN → ℝ)
    (hψ_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ_seq n))
    (hψ_seq_cs : ∀ n, HasCompactSupport (ψ_seq n))
    (hψ_seq_support : ∀ n, tsupport (ψ_seq n) ⊆ K_0)
    (hψ_seq_l2 :
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => ψ_seq n x - ψ x) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0)) _root_.Filter.atTop (𝓝 0))
    (hψ_seq_grad_l2 : ∀ j : Fin (Module.finrank ℝ E),
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm
        (fun x => (fderiv ℝ (ψ_seq n) x) (EuclideanSpace.single j 1) -
          weak_partial_ψ j x) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0)) _root_.Filter.atTop (𝓝 0)) :
    (∫ y in K_0,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            weak_partial_ψ j y)
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
    (∫ y in K_0,
      densityOnEuclid (I := I) g α y * D.uChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
    ∫ y in K_0,
      densityOnEuclid (I := I) g α y * D.fChart y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have hpqT : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := by
    refine ⟨?_⟩
    rw [inv_one]
    rw [show ((2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹) = 2 * (2 : ℝ≥0∞)⁻¹ from by ring]
    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have hK_0_meas : MeasurableSet K_0 := hK_0_compact.isClosed.measurableSet
  set μ : _root_.MeasureTheory.Measure EuclN := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K_0 with hμ_def
  have h_dens_cont : ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (densityOnEuclid_contDiffOn (I := I) g α).continuousOn
  have h_dens_cont_K : ContinuousOn (densityOnEuclid (I := I) g α) K_0 :=
    h_dens_cont.mono hK_0_in
  have h_wig_cont : ∀ i j, ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro i j
    exact (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have h_wig_cont_K : ∀ i j, ContinuousOn
      (weightedInvGramOnEuclid (I := I) g α i j) K_0 := by
    intro i j
    exact (h_wig_cont i j).mono hK_0_in
  obtain ⟨C_dens, hC_dens_nn, h_dens_bd⟩ :=
    densityOnEuclid_bounded_above_on_compact (I := I) (M := M) g α
      hK_0_compact hK_0_in
  have hD_u_lp : _root_.MeasureTheory.MemLp D.uChart 2 μ :=
    uChart_memLp_volume_restrict_compact (I := I) (M := M) D
      hK_0_compact hK_0_meas hK_0_in
  have hD_f_lp : _root_.MeasureTheory.MemLp D.fChart 2 μ :=
    fChart_memLp_volume_restrict_compact (I := I) (M := M) D
      hK_0_compact hK_0_meas hK_0_in
  have hD_wp_lp : ∀ i, _root_.MeasureTheory.MemLp (D.weakPartial i) 2 μ := fun i =>
    D.weak_partial_locally_memLp i K_0 hK_0_compact hK_0_in
  have hψ_lp : _root_.MeasureTheory.MemLp ψ 2 μ := hψ_l2
  have hψ_grad_lp : ∀ j, _root_.MeasureTheory.MemLp (weak_partial_ψ j) 2 μ := hψ_grad_l2
  have hψ_seq_lp : ∀ n, _root_.MeasureTheory.MemLp (ψ_seq n) 2 μ := by
    intro n
    have h_cont : Continuous (ψ_seq n) := (hψ_seq_smooth n).continuous
    exact (h_cont.memLp_of_hasCompactSupport (hψ_seq_cs n)).restrict _
  have hψ_seq_grad_lp : ∀ n j,
      MemLp (fun x => (fderiv ℝ (ψ_seq n) x) (EuclideanSpace.single j 1)) 2 μ := by
    intro n j
    have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
      decide
    have h_cont : Continuous
        (fun x => (fderiv ℝ (ψ_seq n) x) (EuclideanSpace.single j 1)) := by
      have h_fderiv_cont : Continuous (fderiv ℝ (ψ_seq n)) :=
        (hψ_seq_smooth n).continuous_fderiv h_top_ne_zero
      exact h_fderiv_cont.clm_apply continuous_const
    have h_cs : HasCompactSupport
        (fun x => (fderiv ℝ (ψ_seq n) x) (EuclideanSpace.single j 1)) :=
      (hψ_seq_cs n).fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
    exact (h_cont.memLp_of_hasCompactSupport h_cs).restrict _
  have h_dens_K_aestronglyMeasurable :
      AEStronglyMeasurable (densityOnEuclid (I := I) g α) μ := by
    have h_cont' := h_dens_cont_K
    exact h_cont'.aestronglyMeasurable hK_0_meas
  have h_wig_K_aestronglyMeasurable : ∀ i j,
      AEStronglyMeasurable (weightedInvGramOnEuclid (I := I) g α i j) μ := by
    intro i j
    have h_cont' := h_wig_cont_K i j
    exact h_cont'.aestronglyMeasurable hK_0_meas
  have hY_dens_u_lp :
      MemLp (fun y => densityOnEuclid (I := I) g α y * D.uChart y) 2 μ := by
    have h_aestronglyMeasurable :
        _root_.MeasureTheory.AEStronglyMeasurable
          (fun y => densityOnEuclid (I := I) g α y * D.uChart y) μ :=
      h_dens_K_aestronglyMeasurable.mul hD_u_lp.aestronglyMeasurable
    have h_pt_bd : ∀ᵐ y ∂μ,
        ‖densityOnEuclid (I := I) g α y * D.uChart y‖ ≤
          ‖C_dens * D.uChart y‖ := by
      rw [hμ_def, _root_.MeasureTheory.ae_restrict_iff' hK_0_meas]
      refine Filter.Eventually.of_forall ?_
      intro y hy
      have h_dens_le : densityOnEuclid (I := I) g α y ≤ C_dens := h_dens_bd y hy
      have h_dens_nn : 0 ≤ densityOnEuclid (I := I) g α y :=
        le_of_lt (densityOnEuclid_pos (I := I) g α (hK_0_in hy))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_dens_nn]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC_dens_nn]
      exact mul_le_mul_of_nonneg_right h_dens_le (abs_nonneg _)
    refine MemLp.mono (hD_u_lp.const_mul C_dens) h_aestronglyMeasurable h_pt_bd
  have hY_dens_f_lp :
      MemLp (fun y => densityOnEuclid (I := I) g α y * D.fChart y) 2 μ := by
    have h_aestronglyMeasurable :
        _root_.MeasureTheory.AEStronglyMeasurable
          (fun y => densityOnEuclid (I := I) g α y * D.fChart y) μ :=
      h_dens_K_aestronglyMeasurable.mul hD_f_lp.aestronglyMeasurable
    have h_pt_bd : ∀ᵐ y ∂μ,
        ‖densityOnEuclid (I := I) g α y * D.fChart y‖ ≤
          ‖C_dens * D.fChart y‖ := by
      rw [hμ_def, _root_.MeasureTheory.ae_restrict_iff' hK_0_meas]
      refine Filter.Eventually.of_forall ?_
      intro y hy
      have h_dens_le : densityOnEuclid (I := I) g α y ≤ C_dens := h_dens_bd y hy
      have h_dens_nn : 0 ≤ densityOnEuclid (I := I) g α y :=
        le_of_lt (densityOnEuclid_pos (I := I) g α (hK_0_in hy))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_dens_nn]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC_dens_nn]
      exact mul_le_mul_of_nonneg_right h_dens_le (abs_nonneg _)
    refine MemLp.mono (hD_f_lp.const_mul C_dens) h_aestronglyMeasurable h_pt_bd
  have hY_ij_lp : ∀ i j, _root_.MeasureTheory.MemLp
      (fun y => weightedInvGramOnEuclid (I := I) g α i j y * D.weakPartial i y) 2 μ := by
    intro i j
    obtain ⟨C_ij, hC_ij_nn, h_wig_bd⟩ :=
      weightedInvGramOnEuclid_bounded_on_compact (I := I) (M := M) g α i j
        hK_0_compact hK_0_in
    have h_aestronglyMeasurable :
        _root_.MeasureTheory.AEStronglyMeasurable
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y) μ :=
      (h_wig_K_aestronglyMeasurable i j).mul (hD_wp_lp i).aestronglyMeasurable
    have h_pt_bd : ∀ᵐ y ∂μ,
        ‖weightedInvGramOnEuclid (I := I) g α i j y * D.weakPartial i y‖ ≤
          ‖C_ij * D.weakPartial i y‖ := by
      rw [hμ_def, _root_.MeasureTheory.ae_restrict_iff' hK_0_meas]
      refine Filter.Eventually.of_forall ?_
      intro y hy
      rw [Real.norm_eq_abs, abs_mul]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC_ij_nn]
      have h_wig_abs := h_wig_bd y hy
      exact mul_le_mul_of_nonneg_right h_wig_abs (abs_nonneg _)
    refine MemLp.mono ((hD_wp_lp i).const_mul C_ij) h_aestronglyMeasurable h_pt_bd
  have h_id_seq :
      ∀ n, (∫ y in K_0,
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  weightedInvGramOnEuclid (I := I) g α i j y *
                    D.weakPartial i y *
                    (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1))
              ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
            (∫ y in K_0,
              densityOnEuclid (I := I) g α y * D.uChart y * ψ_seq n y
              ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
            ∫ y in K_0,
              densityOnEuclid (I := I) g α y * D.fChart y * ψ_seq n y
              ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    intro n
    have hψ_seq_support_chart : tsupport (ψ_seq n) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
      (hψ_seq_support n).trans hK_0_in
    have h_id_chart :=
      chart_bilinear_identity_h1Compl (I := I) (M := M) D
        (hψ_seq_smooth n) (hψ_seq_cs n) hψ_seq_support_chart
    have hChart_meas : MeasurableSet
        (chartTargetEuclid (I := I) (M := M) α) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    have h_int_lhs1_chart_to_K0 :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y in K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      apply _root_.MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hChart_meas
        (hK_0_in.trans (subset_refl _))
      intro y hy
      have hy_notin_support : y ∉ tsupport (ψ_seq n) := fun hin =>
        hy.2 ((hψ_seq_support n) hin)
      have h_fderiv_zero :
          ∀ v : EuclN, (fderiv ℝ (ψ_seq n) y) v = 0 := by
        have h_fderiv_eq_zero : fderiv ℝ (ψ_seq n) y = 0 := by
          have h_open_compl : IsOpen (tsupport (ψ_seq n))ᶜ :=
            (isClosed_tsupport (ψ_seq n)).isOpen_compl
          have hpsi_eq_zero : ψ_seq n =ᶠ[𝓝 y] (0 : EuclN → ℝ) := by
            refine (h_open_compl.eventually_mem hy_notin_support).mono ?_
            intro z hz
            exact image_eq_zero_of_notMem_tsupport hz
          have hf_eq : fderiv ℝ (ψ_seq n) y = fderiv ℝ (0 : EuclN → ℝ) y :=
            hpsi_eq_zero.fderiv_eq
          rw [hf_eq, fderiv_zero]
          rfl
        intro v
        rw [h_fderiv_eq_zero]; rfl
      have hsum_zero : (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        apply Finset.sum_eq_zero
        intro j _
        rw [h_fderiv_zero (EuclideanSpace.single j 1)]
        ring
      exact hsum_zero
    have h_int_lhs2_chart_to_K0 :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y * D.uChart y * ψ_seq n y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.uChart y * ψ_seq n y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      apply _root_.MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hChart_meas
        (hK_0_in.trans (subset_refl _))
      intro y hy
      have hy_notin_support : y ∉ tsupport (ψ_seq n) := fun hin =>
        hy.2 ((hψ_seq_support n) hin)
      have hpsi_y : ψ_seq n y = 0 :=
        image_eq_zero_of_notMem_tsupport hy_notin_support
      rw [hpsi_y]; ring
    have h_int_rhs_chart_to_K0 :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y * D.fChart y * ψ_seq n y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.fChart y * ψ_seq n y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      apply _root_.MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hChart_meas
        (hK_0_in.trans (subset_refl _))
      intro y hy
      have hy_notin_support : y ∉ tsupport (ψ_seq n) := fun hin =>
        hy.2 ((hψ_seq_support n) hin)
      have hpsi_y : ψ_seq n y = 0 :=
        image_eq_zero_of_notMem_tsupport hy_notin_support
      rw [hpsi_y]; ring
    rw [← h_int_lhs1_chart_to_K0, ← h_int_lhs2_chart_to_K0,
      ← h_int_rhs_chart_to_K0]
    exact h_id_chart
  have h_lhs_principal_n_converges : ∀ i j,
      _root_.Filter.Tendsto
        (fun n => ∫ y in K_0,
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
        _root_.Filter.atTop
        (𝓝 (∫ y in K_0,
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            weak_partial_ψ j y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) := by
    intro i j
    have h_int_n :
        ∀ n, ∫ y in K_0,
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1)
              ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
            ∫ y, (weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y) *
                (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1) ∂μ := by
      intro n
      rfl
    have h_int_lim :
        ∫ y in K_0,
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            weak_partial_ψ j y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y, (weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y) *
            weak_partial_ψ j y ∂μ := by
      rfl
    rw [h_int_lim]
    have h_helper :=
      tendsto_setIntegral_mul_of_eLpNorm_tendsto_zero_l2 (μ := μ)
        (Y := fun y => weightedInvGramOnEuclid (I := I) g α i j y *
          D.weakPartial i y)
        (ψ_n := fun n y => (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1))
        (ψ := weak_partial_ψ j)
        (hY_ij_lp i j)
        (fun n => hψ_seq_grad_lp n j)
        (hψ_grad_lp j)
        (hψ_seq_grad_l2 j)
    have h_tendsto_match :
        (fun n => ∫ y in K_0,
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (fun n => ∫ y, (weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y) *
            (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1) ∂μ) := by
      funext n; exact h_int_n n
    rw [h_tendsto_match]
    exact h_helper
  have h_lhs_principal_converges :
      _root_.Filter.Tendsto
        (fun n => ∫ y in K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
        _root_.Filter.atTop
        (𝓝 (∫ y in K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                weak_partial_ψ j y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) := by
    have h_summand_int_n : ∀ n i j,
        _root_.MeasureTheory.Integrable
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1)) μ := by
      intro n i j
      have h_factored :
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1)) =
          (fun y => (weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y) *
            (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1)) := by
        funext y; ring
      rw [h_factored]
      have h := MemLp.integrable_mul (μ := μ) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (hY_ij_lp i j) (hψ_seq_grad_lp n j)
      have h_eq :
          ((fun y => weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y) *
            (fun y => (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1))) =
          (fun y => (weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y) *
            (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1)) := rfl
      rw [h_eq] at h
      exact h
    have h_summand_int_lim : ∀ i j,
        _root_.MeasureTheory.Integrable
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            weak_partial_ψ j y) μ := by
      intro i j
      have h_factored :
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y *
            weak_partial_ψ j y) =
          (fun y => (weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y) *
            weak_partial_ψ j y) := by
        funext y; ring
      rw [h_factored]
      have h := MemLp.integrable_mul (μ := μ) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (hY_ij_lp i j) (hψ_grad_lp j)
      have h_eq :
          ((fun y => weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y) *
            (fun y => weak_partial_ψ j y)) =
          (fun y => (weightedInvGramOnEuclid (I := I) g α i j y *
            D.weakPartial i y) *
            weak_partial_ψ j y) := rfl
      rw [h_eq] at h
      exact h
    have h_int_swap_n : ∀ n,
        ∫ y in K_0, (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in K_0,
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1)
              ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      intro n
      simp only [hμ_def] at h_summand_int_n
      rw [_root_.MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [_root_.MeasureTheory.integral_finsetSum]
        intro j _
        exact h_summand_int_n n i j
      · intro i _
        exact _root_.MeasureTheory.integrable_finsetSum _ (fun j _ => h_summand_int_n n i j)
    have h_int_swap_lim :
        ∫ y in K_0, (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                weak_partial_ψ j y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in K_0,
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                weak_partial_ψ j y
              ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      simp only [hμ_def] at h_summand_int_lim
      rw [_root_.MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [_root_.MeasureTheory.integral_finsetSum]
        intro j _
        exact h_summand_int_lim i j
      · intro i _
        exact _root_.MeasureTheory.integrable_finsetSum _ (fun j _ => h_summand_int_lim i j)
    have h_per_ij_tendsto :
        _root_.Filter.Tendsto
          (fun n => ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in K_0,
                weightedInvGramOnEuclid (I := I) g α i j y *
                  D.weakPartial i y *
                  (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1)
                ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
          _root_.Filter.atTop
          (𝓝 (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in K_0,
                weightedInvGramOnEuclid (I := I) g α i j y *
                  D.weakPartial i y *
                  weak_partial_ψ j y
                ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) := by
      apply tendsto_finsetSum
      intro i _
      apply tendsto_finsetSum
      intro j _
      exact h_lhs_principal_n_converges i j
    have h_eq_n :
        (fun n => ∫ y in K_0,
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α i j y *
                  D.weakPartial i y *
                  (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1))
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
          (fun n => ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in K_0,
                weightedInvGramOnEuclid (I := I) g α i j y *
                  D.weakPartial i y *
                  (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1)
                ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by
      funext n; exact h_int_swap_n n
    rw [h_eq_n]
    rw [h_int_swap_lim]
    exact h_per_ij_tendsto
  have h_lhs_lower_converges :
      _root_.Filter.Tendsto
        (fun n => ∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.uChart y * ψ_seq n y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
        _root_.Filter.atTop
        (𝓝 (∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.uChart y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) := by
    have h_int_n : ∀ n,
        ∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.uChart y * ψ_seq n y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y, (densityOnEuclid (I := I) g α y * D.uChart y) * ψ_seq n y ∂μ := by
      intro n; rfl
    have h_int_lim :
        ∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.uChart y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y, (densityOnEuclid (I := I) g α y * D.uChart y) * ψ y ∂μ := by
      rfl
    rw [h_int_lim]
    have h_helper :=
      tendsto_setIntegral_mul_of_eLpNorm_tendsto_zero_l2 (μ := μ)
        (Y := fun y => densityOnEuclid (I := I) g α y * D.uChart y)
        (ψ_n := ψ_seq) (ψ := ψ)
        hY_dens_u_lp
        hψ_seq_lp
        hψ_lp
        hψ_seq_l2
    have h_tendsto_match :
        (fun n => ∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.uChart y * ψ_seq n y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (fun n => ∫ y, (densityOnEuclid (I := I) g α y * D.uChart y) *
          ψ_seq n y ∂μ) := by
      funext n; exact h_int_n n
    rw [h_tendsto_match]
    exact h_helper
  have h_rhs_converges :
      _root_.Filter.Tendsto
        (fun n => ∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.fChart y * ψ_seq n y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
        _root_.Filter.atTop
        (𝓝 (∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.fChart y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) := by
    have h_int_n : ∀ n,
        ∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.fChart y * ψ_seq n y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y, (densityOnEuclid (I := I) g α y * D.fChart y) * ψ_seq n y ∂μ := by
      intro n; rfl
    have h_int_lim :
        ∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.fChart y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y, (densityOnEuclid (I := I) g α y * D.fChart y) * ψ y ∂μ := by
      rfl
    rw [h_int_lim]
    have h_helper :=
      tendsto_setIntegral_mul_of_eLpNorm_tendsto_zero_l2 (μ := μ)
        (Y := fun y => densityOnEuclid (I := I) g α y * D.fChart y)
        (ψ_n := ψ_seq) (ψ := ψ)
        hY_dens_f_lp
        hψ_seq_lp
        hψ_lp
        hψ_seq_l2
    have h_tendsto_match :
        (fun n => ∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.fChart y * ψ_seq n y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (fun n => ∫ y, (densityOnEuclid (I := I) g α y * D.fChart y) *
          ψ_seq n y ∂μ) := by
      funext n; exact h_int_n n
    rw [h_tendsto_match]
    exact h_helper
  have h_lhs_converges :
      _root_.Filter.Tendsto
        (fun n => (∫ y in K_0,
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α i j y *
                  D.weakPartial i y *
                  (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1))
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
          ∫ y in K_0,
            densityOnEuclid (I := I) g α y * D.uChart y * ψ_seq n y
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
        _root_.Filter.atTop
        (𝓝 ((∫ y in K_0,
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α i j y *
                  D.weakPartial i y *
                  weak_partial_ψ j y)
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
          ∫ y in K_0,
            densityOnEuclid (I := I) g α y * D.uChart y * ψ y
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) :=
    h_lhs_principal_converges.add h_lhs_lower_converges
  have h_lhs_eq_rhs_n :
      (fun n => (∫ y in K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                (fderiv ℝ (ψ_seq n) y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        ∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.uChart y * ψ_seq n y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
      (fun n => ∫ y in K_0,
          densityOnEuclid (I := I) g α y * D.fChart y * ψ_seq n y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by
    funext n
    exact h_id_seq n
  rw [h_lhs_eq_rhs_n] at h_lhs_converges
  exact tendsto_nhds_unique h_lhs_converges h_rhs_converges

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.chart_bilinear_identity_h1_0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.chart_bilinear_identity_h1_0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.chart_bilinear_identity_h1_0 ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.chart_bilinear_identity_h1_0

end ChartBilinearH1Compl
end Laplacian
end Analysis
end DifferentialGeometry
