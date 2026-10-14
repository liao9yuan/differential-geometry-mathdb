import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Differentiated.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.TensorRSNabla
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma eLpNorm_volume_restrict_contDiffOn_mul_le
    (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (w : EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      _root_.MeasureTheory.eLpNorm (fun y => c y * w y) 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K)
        ≤ ENNReal.ofReal C *
          eLpNorm w 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
  classical
  set μ : _root_.MeasureTheory.Measure EuclN := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K with hμ_def
  have hcontOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hcontOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  refine ⟨C, hC_nn, ?_⟩
  have h_dom : ∀ᵐ y ∂μ, ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    rw [hμ_def, _root_.MeasureTheory.ae_restrict_iff' hK_meas]
    refine Filter.Eventually.of_forall (fun y hyK => ?_)
    have hlhs : ‖c y * w y‖ = ‖c y‖ * ‖w y‖ := norm_mul _ _
    have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right (hC_bd y hyK) (norm_nonneg _)
  have h_mono :
      eLpNorm (fun y => c y * w y) 2 μ ≤ _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μ :=
    eLpNorm_mono_ae (μ := μ) h_dom
  have h_smul :
      _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μ
        = ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μ := by
    have h := _root_.MeasureTheory.eLpNorm_const_smul (μ := μ) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    change _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μ =
      ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μ at h
    exact h
  calc
    _root_.MeasureTheory.eLpNorm (fun y => c y * w y) 2 μ
        ≤ _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μ := h_mono
    _ = ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μ := h_smul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_volume_restrict_contDiffOn_mul_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_volume_restrict_contDiffOn_mul_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_volume_restrict_contDiffOn_mul_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_volume_restrict_contDiffOn_mul_le

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
lemma eLpNorm_sum_le_const_mul_aggregate
    {ι : Type*} [Fintype ι] {μ : _root_.MeasureTheory.Measure EuclN} (F : ι → EuclN → ℝ)
    (A : ℝ≥0∞)
    (hF : ∀ j : ι, _root_.MeasureTheory.MemLp (F j) 2 μ)
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧ _root_.MeasureTheory.eLpNorm (F j) 2 μ ≤ ENNReal.ofReal C * A) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => ∑ j : ι, F j y) 2 μ ≤ ENNReal.ofReal C * A := by
  classical
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity), ?_⟩
  have h_fun : (fun y => ∑ j : ι, F j y) = ∑ j : ι, F j := by
    funext y
    exact (Finset.sum_apply y Finset.univ F).symm
  rw [h_fun]
  have h_tri : _root_.MeasureTheory.eLpNorm (∑ j : ι, F j) 2 μ ≤ ∑ j : ι, _root_.MeasureTheory.eLpNorm (F j) 2 μ :=
    _root_.MeasureTheory.eLpNorm_sum_le (fun j _ => (hF j).aestronglyMeasurable) (by norm_num)
  have h_step : ∑ j : ι, _root_.MeasureTheory.eLpNorm (F j) 2 μ
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_cast : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)
      = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) := by
    rw [mul_comm (∑ j : ι, Cf j), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc
    _root_.MeasureTheory.eLpNorm (∑ j : ι, F j) 2 μ
        ≤ ∑ j : ι, _root_.MeasureTheory.eLpNorm (F j) 2 μ := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A := by
        rw [h_cast]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sum_le_const_mul_aggregate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sum_le_const_mul_aggregate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sum_le_const_mul_aggregate ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sum_le_const_mul_aggregate

section MainBoundUniform

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
omit [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EuclN → ℝ,
      _root_.MeasureTheory.eLpNorm (fun y => c y * w y) 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K)
        ≤ ENNReal.ofReal C *
          eLpNorm w 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
  classical
  set μ : _root_.MeasureTheory.Measure EuclN := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K with hμ_def
  have hcontOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hcontOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  refine ⟨C, hC_nn, fun w => ?_⟩
  have h_dom : ∀ᵐ y ∂μ, ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    rw [hμ_def, _root_.MeasureTheory.ae_restrict_iff' hK_meas]
    refine Filter.Eventually.of_forall (fun y hyK => ?_)
    have hlhs : ‖c y * w y‖ = ‖c y‖ * ‖w y‖ := norm_mul _ _
    have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right (hC_bd y hyK) (norm_nonneg _)
  have h_mono :
      eLpNorm (fun y => c y * w y) 2 μ ≤ _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μ :=
    eLpNorm_mono_ae (μ := μ) h_dom
  have h_smul :
      _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μ
        = ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μ := by
    have h := _root_.MeasureTheory.eLpNorm_const_smul (μ := μ) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    change _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μ =
      ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μ at h
    exact h
  calc
    _root_.MeasureTheory.eLpNorm (fun y => c y * w y) 2 μ
        ≤ _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μ := h_mono
    _ = ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μ := h_smul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_volume_restrict_contDiffOn_mul_le_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_volume_restrict_contDiffOn_mul_le_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_volume_restrict_contDiffOn_mul_le_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_volume_restrict_contDiffOn_mul_le_uniform

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma eLpNorm_sum_le_const_mul_aggregate_uniform
    {ι : Type*} [Fintype ι] {ν : Type*} {μ : _root_.MeasureTheory.Measure EuclN}
    (F : ι → ν → EuclN → ℝ) (A : ν → ℝ≥0∞)
    (hF : ∀ (j : ι) (n : ν), _root_.MeasureTheory.MemLp (F j n) 2 μ)
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν, _root_.MeasureTheory.eLpNorm (F j n) 2 μ ≤ ENNReal.ofReal C * A n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν,
        eLpNorm (fun y => ∑ j : ι, F j n y) 2 μ ≤ ENNReal.ofReal C * A n := by
  classical
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity),
    fun n => ?_⟩
  have h_fun : (fun y => ∑ j : ι, F j n y) = ∑ j : ι, F j n := by
    funext y
    exact (Finset.sum_apply y Finset.univ (fun j => F j n)).symm
  rw [h_fun]
  have h_tri : _root_.MeasureTheory.eLpNorm (∑ j : ι, F j n) 2 μ ≤ ∑ j : ι, _root_.MeasureTheory.eLpNorm (F j n) 2 μ :=
    _root_.MeasureTheory.eLpNorm_sum_le (fun j _ => (hF j n).aestronglyMeasurable) (by norm_num)
  have h_step : ∑ j : ι, _root_.MeasureTheory.eLpNorm (F j n) 2 μ
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j n).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_cast : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)
      = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) := by
    rw [mul_comm (∑ j : ι, Cf j), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc
    _root_.MeasureTheory.eLpNorm (∑ j : ι, F j n) 2 μ
        ≤ ∑ j : ι, _root_.MeasureTheory.eLpNorm (F j n) 2 μ := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A n := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A n := by
        rw [h_cast]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sum_le_const_mul_aggregate_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sum_le_const_mul_aggregate_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sum_le_const_mul_aggregate_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_sum_le_const_mul_aggregate_uniform

end MainBoundUniform

section SharpAtomBounds

omit [CompleteSpace E] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chosenWp_memLp_volume_restrict
    (b : Fin (Module.finrank ℝ E)) (w : EuclN → ℝ) {Ω K : Set EuclN}
    (hK_meas : MeasurableSet K) (hK_in : K ⊆ Ω) :
    MemLp (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 b w Ω) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
  classical
  have h_global : _root_.MeasureTheory.MemLp (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 b w Ω)
      2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω) := by
    by_cases hw : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 w Ω
    · exact chosenWeakPartialOrZero_memLp_of_mem hw b
    · rw [chosenWeakPartialOrZero_of_not_mem hw b]
      exact MemLp.zero
  have h_eq : ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω).restrict K =
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    exact congrArg _ (Set.inter_eq_self_of_subset_left hK_in)
  exact h_eq ▸ h_global.restrict K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWp_memLp_volume_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWp_memLp_volume_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWp_memLp_volume_restrict ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWp_memLp_volume_restrict

end SharpAtomBounds

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
