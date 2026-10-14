import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.PartitionOfUnityChartKernel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.ENNReal _root_.NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma memLp_bdd_mul
    (α : M) {c : EuclN → ℝ} {C : ℝ} (hC : 0 ≤ C) (hc_bd : ∀ y, ‖c y‖ ≤ C)
    (hc_meas : _root_.MeasureTheory.AEStronglyMeasurable c (chartLebesgueMeasure (I := I) (M := M) α))
    {f : EuclN → ℝ}
    (hf : _root_.MeasureTheory.MemLp f 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    MemLp (fun y => c y * f y) 2 (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  refine ⟨hc_meas.mul hf.1, ?_⟩
  have hpt : ∀ y : EuclN, ‖c y * f y‖ ≤ ‖(C : ℝ) • f y‖ := by
    intro y
    have h1 : ‖c y * f y‖ = ‖c y‖ * ‖f y‖ := norm_mul _ _
    have h2 : ‖(C : ℝ) • f y‖ = C * ‖f y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (hc_bd y) (norm_nonneg _)
  have hmono := _root_.MeasureTheory.eLpNorm_mono (μ := chartLebesgueMeasure (I := I) (M := M) α)
    (p := 2) hpt
  calc _root_.MeasureTheory.eLpNorm (fun y => c y * f y) 2 (chartLebesgueMeasure (I := I) (M := M) α)
      ≤ _root_.MeasureTheory.eLpNorm ((C : ℝ) • f) 2 (chartLebesgueMeasure (I := I) (M := M) α) := hmono
    _ = ‖(C : ℝ)‖ₑ * _root_.MeasureTheory.eLpNorm f 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
        _root_.MeasureTheory.eLpNorm_const_smul (C : ℝ) f 2 _
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hf.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_bdd_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_bdd_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_bdd_mul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_bdd_mul

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma eLpNorm_bdd_mul_le
    (α : M) {c : EuclN → ℝ} {C : ℝ} (hC : 0 ≤ C) (hc_bd : ∀ y, ‖c y‖ ≤ C)
    (f : EuclN → ℝ) :
    eLpNorm (fun y => c y * f y) 2 (chartLebesgueMeasure (I := I) (M := M) α) ≤
      ENNReal.ofReal C *
        eLpNorm f 2 (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  have hpt : ∀ y : EuclN, ‖c y * f y‖ ≤ ‖(C : ℝ) • f y‖ := by
    intro y
    have h1 : ‖c y * f y‖ = ‖c y‖ * ‖f y‖ := norm_mul _ _
    have h2 : ‖(C : ℝ) • f y‖ = C * ‖f y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (hc_bd y) (norm_nonneg _)
  calc _root_.MeasureTheory.eLpNorm (fun y => c y * f y) 2 (chartLebesgueMeasure (I := I) (M := M) α)
      ≤ _root_.MeasureTheory.eLpNorm ((C : ℝ) • f) 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
        _root_.MeasureTheory.eLpNorm_mono hpt
    _ = ‖(C : ℝ)‖ₑ * _root_.MeasureTheory.eLpNorm f 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
        _root_.MeasureTheory.eLpNorm_const_smul (C : ℝ) f 2 _
    _ = ENNReal.ofReal C *
          eLpNorm f 2 (chartLebesgueMeasure (I := I) (M := M) α) := by
        rw [Real.enorm_eq_ofReal hC]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_bdd_mul_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_bdd_mul_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_bdd_mul_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_bdd_mul_le

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tendsto_bdd_mul
    (α : M) {c : EuclN → ℝ} {C : ℝ} (hC : 0 ≤ C) (hc_bd : ∀ y, ‖c y‖ ≤ C)
    (hc_meas : _root_.MeasureTheory.AEStronglyMeasurable c (chartLebesgueMeasure (I := I) (M := M) α))
    {F : ℕ → _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)}
    {Flim : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)}
    (hF : Filter.Tendsto F _root_.Filter.atTop (𝓝 Flim)) :
    Filter.Tendsto
      (fun n => (memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
        (Lp.memLp (F n))).toLp (fun y => c y * (F n : EuclN → ℝ) y))
      _root_.Filter.atTop
      (𝓝 ((memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
        (Lp.memLp Flim)).toLp (fun y => c y * (Flim : EuclN → ℝ) y))) := by
  classical
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have hCpos : (0 : ℝ) < C + 1 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hF (ε / (C + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hdist_eq :
      _root_.Dist.dist
        ((memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
          (Lp.memLp (F n))).toLp (fun y => c y * (F n : EuclN → ℝ) y))
        ((memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
          (Lp.memLp Flim)).toLp (fun y => c y * (Flim : EuclN → ℝ) y)) =
      (_root_.MeasureTheory.eLpNorm
        (fun y => c y * (F n : EuclN → ℝ) y -
          c y * (Flim : EuclN → ℝ) y) 2
        (chartLebesgueMeasure (I := I) (M := M) α)).toReal := by
    rw [Lp.dist_def]
    refine congrArg ENNReal.toReal (_root_.MeasureTheory.eLpNorm_congr_ae ?_)
    filter_upwards [MemLp.coeFn_toLp (memLp_bdd_mul (I := I) (M := M) α hC
        hc_bd hc_meas (Lp.memLp (F n))),
      MemLp.coeFn_toLp (memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
        (Lp.memLp Flim))] with y hy₁ hy₂
    rw [Pi.sub_apply, hy₁, hy₂]
  rw [hdist_eq]
  have hsub_eq :
      (fun y => c y * (F n : EuclN → ℝ) y - c y * (Flim : EuclN → ℝ) y) =
        (fun y => c y * ((F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)) := by
    funext y; ring
  rw [hsub_eq]
  have hle := eLpNorm_bdd_mul_le (I := I) (M := M) α hC hc_bd
    (fun y => (F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)
  have hsub_ae :
      (fun y => (F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      (((F n) - Flim : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
        EuclN → ℝ) :=
    (Lp.coeFn_sub (F n) Flim).symm
  have hdist_F :
      _root_.MeasureTheory.eLpNorm (fun y => (F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y) 2
          (chartLebesgueMeasure (I := I) (M := M) α) =
        ENNReal.ofReal (_root_.Dist.dist (F n) Flim) := by
    have hfin : _root_.MeasureTheory.eLpNorm
        (((F n) - Flim : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
          EuclN → ℝ) 2 (chartLebesgueMeasure (I := I) (M := M) α) ≠ ⊤ :=
      (Lp.memLp ((F n) - Flim)).2.ne
    rw [_root_.MeasureTheory.eLpNorm_congr_ae hsub_ae, Lp.dist_def,
      ENNReal.ofReal_toReal ((_root_.MeasureTheory.eLpNorm_congr_ae hsub_ae) ▸ hfin)]
    exact (_root_.MeasureTheory.eLpNorm_congr_ae hsub_ae).symm
  rw [hdist_F] at hle
  have hfin : (ENNReal.ofReal C * ENNReal.ofReal (_root_.Dist.dist (F n) Flim)) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
  have hreal :
      (_root_.MeasureTheory.eLpNorm (fun y => c y *
          ((F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)) 2
        (chartLebesgueMeasure (I := I) (M := M) α)).toReal ≤
        C * _root_.Dist.dist (F n) Flim := by
    refine (ENNReal.toReal_mono hfin hle).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
      ENNReal.toReal_ofReal dist_nonneg]
  refine lt_of_le_of_lt hreal ?_
  have hd : _root_.Dist.dist (F n) Flim < ε / (C + 1) := hN n hn
  calc C * _root_.Dist.dist (F n) Flim
      ≤ (C + 1) * _root_.Dist.dist (F n) Flim :=
        mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < (C + 1) * (ε / (C + 1)) :=
        mul_lt_mul_of_pos_left hd hCpos
    _ = ε := by field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_bdd_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_bdd_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_bdd_mul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_bdd_mul

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma tensorChartComponent_contDiff_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) :=
  (contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mp
    (tensorChartComponent_contMDiff (I := I) (M := M) g r s S α Idx Jdx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_contDiff_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_contDiff_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_contDiff_top ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_contDiff_top

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tensorChartComponent_tsupport_subset_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α := by
  classical
  have hsupp : Function.support
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α := by
    intro z hz
    by_contra hzk
    exact hz (tensorChartComponent_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s S α Idx Jdx hzk)
  exact closure_minimal hsupp
    (chartPouKernel_isCompact (I := I) (M := M) α).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_tsupport_subset_chartPouKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_tsupport_subset_chartPouKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_tsupport_subset_chartPouKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_tsupport_subset_chartPouKernel

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma chosenWeakPartialOrZero_tensorChartComponent_ae_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      euclidPartial (E := E) k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  set u : EuclN → ℝ :=
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx with hu_def
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u :=
    tensorChartComponent_contDiff_top (I := I) (M := M) g r s S α Idx Jdx
  have hu_compact : HasCompactSupport u :=
    tensorChartComponent_hasCompactSupport (I := I) (M := M) g r s S α Idx Jdx
  have hu_tsupp : tsupport u ⊆ chartTargetEuclid (I := I) (M := M) α :=
    (tensorChartComponent_tsupport_subset_chartPouKernel
      (I := I) (M := M) g r s S α Idx Jdx).trans
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hu_W1 : MemWkp (d := Module.finrank ℝ E) 1 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_of_smooth_compactSupport (d := Module.finrank ℝ E) hΩ_open
      hu_smooth hu_compact hu_tsupp hp_one 1
  have hu_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.one_iff_memW1p.mp hu_W1
  have h_ae := chosenWeakPartial_smooth_ae_eq (d := Module.finrank ℝ E)
    hp_one hΩ_open hu_smooth hu_W1p k
  rw [chartLebesgueMeasure]
  refine h_ae.trans (Filter.EventuallyEq.of_eq ?_)
  funext y; rw [euclidPartial_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_tensorChartComponent_ae_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_tensorChartComponent_ae_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_tensorChartComponent_ae_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_tensorChartComponent_ae_eq

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma coeFn_finsetSum_lp
    (α : M) {ι : Type*} (s : Finset ι)
    (G : ι → _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    (((∑ a ∈ s, G a) : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
        EuclN → ℝ)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, ((G a : EuclN → ℝ) y) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero _ _ _
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      refine (Lp.coeFn_add (G a) (∑ b ∈ t, G b)).trans ?_
      filter_upwards [ih] with y hy
      rw [Pi.add_apply, hy, Finset.sum_insert ha]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coeFn_finsetSum_lp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coeFn_finsetSum_lp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coeFn_finsetSum_lp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coeFn_finsetSum_lp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma coeFn_finsetSum_toLp
    (α : M) {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ}
    (hf : ∀ a : ι, _root_.MeasureTheory.MemLp (f a) 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    (((∑ a ∈ s, (hf a).toLp (f a)) :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, f a y := by
  classical
  refine (coeFn_finsetSum_lp (I := I) (M := M) α s
    (fun a => (hf a).toLp (f a))).trans ?_
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      filter_upwards [ih, MemLp.coeFn_toLp (hf a)] with y hy hya
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hya, hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coeFn_finsetSum_toLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coeFn_finsetSum_toLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coeFn_finsetSum_toLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coeFn_finsetSum_toLp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma toLp_finsetSum_congr
    (α : M) {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ}
    (hf : ∀ a : ι, _root_.MeasureTheory.MemLp (f a) 2 (chartLebesgueMeasure (I := I) (M := M) α))
    {F : EuclN → ℝ}
    (hF : _root_.MeasureTheory.MemLp F 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (hFeq : F =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, f a y) :
    hF.toLp F = ∑ a ∈ s, (hf a).toLp (f a) := by
  classical
  apply Lp.ext
  exact (MemLp.coeFn_toLp hF).trans
    (hFeq.trans (coeFn_finsetSum_toLp (I := I) (M := M) α s hf).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toLp_finsetSum_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toLp_finsetSum_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toLp_finsetSum_congr ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toLp_finsetSum_congr

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tendsto_toLp_finsetSum
    (α : M) {ι : Type*} (s : Finset ι)
    {f : ι → ℕ → EuclN → ℝ} {flim : ι → EuclN → ℝ}
    (hf : ∀ (a : ι) (n : ℕ),
      MemLp (f a n) 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (hflim : ∀ a : ι, _root_.MeasureTheory.MemLp (flim a) 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (h_tendsto : ∀ a : ι,
      Filter.Tendsto (fun n => (hf a n).toLp (f a n)) _root_.Filter.atTop
        (𝓝 ((hflim a).toLp (flim a))))
    {Fn : ℕ → EuclN → ℝ} {Flim : EuclN → ℝ}
    (hFn : ∀ n : ℕ, _root_.MeasureTheory.MemLp (Fn n) 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (hFlim : _root_.MeasureTheory.MemLp Flim 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (hFn_eq : ∀ n : ℕ, Fn n =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, f a n y)
    (hFlim_eq : Flim =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, flim a y) :
    Filter.Tendsto (fun n => (hFn n).toLp (Fn n)) _root_.Filter.atTop
      (𝓝 (hFlim.toLp Flim)) := by
  classical
  have h_n : ∀ n : ℕ,
      (hFn n).toLp (Fn n) =
        ∑ a ∈ s, (hf a n).toLp (f a n) :=
    fun n => toLp_finsetSum_congr (I := I) (M := M) α s
      (fun a => hf a n) (hFn n) (hFn_eq n)
  have h_lim :
      hFlim.toLp Flim = ∑ a ∈ s, (hflim a).toLp (flim a) :=
    toLp_finsetSum_congr (I := I) (M := M) α s hflim hFlim hFlim_eq
  rw [show (fun n => (hFn n).toLp (Fn n)) =
      (fun n => ∑ a ∈ s, (hf a n).toLp (f a n)) from funext h_n, h_lim]
  exact tendsto_finsetSum s (fun a _ => h_tendsto a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_toLp_finsetSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_toLp_finsetSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_toLp_finsetSum ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_toLp_finsetSum

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma memLp_indicatorFactor_mul_lp
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (G : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    _root_.MeasureTheory.MemLp
      (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        (G : EuclN → ℝ) y) 2 (chartLebesgueMeasure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  exact memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd
    (aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc) (Lp.memLp G)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_indicatorFactor_mul_lp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_indicatorFactor_mul_lp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_indicatorFactor_mul_lp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_indicatorFactor_mul_lp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tendsto_sumToLp
    (α : M) {ι : Type*} [Fintype ι]
    {f : ι → ℕ → EuclN → ℝ} {flim : ι → EuclN → ℝ}
    (hf : ∀ (a : ι) (n : ℕ),
      MemLp (f a n) 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (hflim : ∀ a : ι, _root_.MeasureTheory.MemLp (flim a) 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (h_tendsto : ∀ a : ι,
      Filter.Tendsto (fun n => (hf a n).toLp (f a n)) _root_.Filter.atTop
        (𝓝 ((hflim a).toLp (flim a)))) :
    Filter.Tendsto
      (fun n => (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
        Finset.univ (fun a _ => hf a n)).toLp (fun y => ∑ a, f a n y))
      _root_.Filter.atTop
      (𝓝 ((_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
        Finset.univ (fun a _ => hflim a)).toLp (fun y => ∑ a, flim a y))) :=
  tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ hf hflim h_tendsto
    (fun n => _root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
      Finset.univ (fun a _ => hf a n))
    (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
      Finset.univ (fun a _ => hflim a))
    (fun _ => Filter.EventuallyEq.rfl) Filter.EventuallyEq.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_sumToLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_sumToLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_sumToLp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_sumToLp

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma euclidPartial_finsetSum
    (l : Fin (Module.finrank ℝ E)) {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ} {y : EuclN}
    (hf : ∀ a ∈ s, DifferentiableAt ℝ (f a) y) :
    euclidPartial (E := E) l (fun z => ∑ a ∈ s, f a z) y =
      ∑ a ∈ s, euclidPartial (E := E) l (f a) y := by
  classical
  rw [euclidPartial_def, fderiv_fun_sum hf, sum_apply]
  exact Finset.sum_congr rfl (fun a _ => by rw [euclidPartial_def])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_finsetSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_finsetSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_finsetSum ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_finsetSum

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tendsto_sum4
    (α : M) {κ₁ κ₂ κ₃ κ₄ : Type*}
    [Fintype κ₁] [Fintype κ₂] [Fintype κ₃] [Fintype κ₄]
    {f : κ₁ → κ₂ → κ₃ → κ₄ → ℕ → EuclN → ℝ}
    {flim : κ₁ → κ₂ → κ₃ → κ₄ → EuclN → ℝ}
    (hf : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (n : ℕ),
      MemLp (f a b c d n) 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (hflim : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄),
      MemLp (flim a b c d) 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (h_tendsto : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄),
      Filter.Tendsto (fun n => (hf a b c d n).toLp (f a b c d n)) _root_.Filter.atTop
        (𝓝 ((hflim a b c d).toLp (flim a b c d)))) :
    Filter.Tendsto
      (fun n => (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun a _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun b _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun c _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun d _ => hf a b c d n))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, f a b c d n y))
      _root_.Filter.atTop
      (𝓝 ((_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun a _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun b _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun c _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun d _ => hflim a b c d))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, flim a b c d y))) :=
  tendsto_sumToLp (I := I) (M := M) α
    (f := fun a => fun n y => ∑ b, ∑ c, ∑ d, f a b c d n y)
    (flim := fun a => fun y => ∑ b, ∑ c, ∑ d, flim a b c d y)
    (fun a n => _root_.MeasureTheory.memLp_finsetSum Finset.univ
      (fun b _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
        (fun c _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ (fun d _ => hf a b c d n))))
    (fun a => _root_.MeasureTheory.memLp_finsetSum Finset.univ
      (fun b _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
        (fun c _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ (fun d _ => hflim a b c d))))
    (fun a => tendsto_sumToLp (I := I) (M := M) α
      (f := fun b => fun n y => ∑ c, ∑ d, f a b c d n y)
      (flim := fun b => fun y => ∑ c, ∑ d, flim a b c d y)
      (fun b n => _root_.MeasureTheory.memLp_finsetSum Finset.univ
        (fun c _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ (fun d _ => hf a b c d n)))
      (fun b => _root_.MeasureTheory.memLp_finsetSum Finset.univ
        (fun c _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ (fun d _ => hflim a b c d)))
      (fun b => tendsto_sumToLp (I := I) (M := M) α
        (f := fun c => fun n y => ∑ d, f a b c d n y)
        (flim := fun c => fun y => ∑ d, flim a b c d y)
        (fun c n => _root_.MeasureTheory.memLp_finsetSum Finset.univ (fun d _ => hf a b c d n))
        (fun c => _root_.MeasureTheory.memLp_finsetSum Finset.univ (fun d _ => hflim a b c d))
        (fun c => tendsto_sumToLp (I := I) (M := M) α
          (hf := fun d n => hf a b c d n) (hflim := fun d => hflim a b c d)
          (h_tendsto a b c))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_sum4 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_sum4"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_sum4 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_sum4

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tendsto_sum5
    (α : M) {κ₁ κ₂ κ₃ κ₄ κ₅ : Type*}
    [Fintype κ₁] [Fintype κ₂] [Fintype κ₃] [Fintype κ₄] [Fintype κ₅]
    {f : κ₁ → κ₂ → κ₃ → κ₄ → κ₅ → ℕ → EuclN → ℝ}
    {flim : κ₁ → κ₂ → κ₃ → κ₄ → κ₅ → EuclN → ℝ}
    (hf : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (e : κ₅) (n : ℕ),
      MemLp (f a b c d e n) 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (hflim : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (e : κ₅),
      MemLp (flim a b c d e) 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (h_tendsto : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (e : κ₅),
      Filter.Tendsto (fun n => (hf a b c d e n).toLp (f a b c d e n)) _root_.Filter.atTop
        (𝓝 ((hflim a b c d e).toLp (flim a b c d e)))) :
    Filter.Tendsto
      (fun n => (_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun a _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun b _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun c _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun d _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                  (fun e _ => hf a b c d e n)))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e n y))
      _root_.Filter.atTop
      (𝓝 ((_root_.MeasureTheory.memLp_finsetSum (μ := chartLebesgueMeasure (I := I) (M := M) α)
          Finset.univ (fun a _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun b _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
              (fun c _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                (fun d _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
                  (fun e _ => hflim a b c d e)))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, flim a b c d e y))) :=
  tendsto_sumToLp (I := I) (M := M) α
    (f := fun a => fun n y => ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e n y)
    (flim := fun a => fun y => ∑ b, ∑ c, ∑ d, ∑ e, flim a b c d e y)
    (fun a n => _root_.MeasureTheory.memLp_finsetSum Finset.univ
      (fun b _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
        (fun c _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
          (fun d _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun e _ => hf a b c d e n)))))
    (fun a => _root_.MeasureTheory.memLp_finsetSum Finset.univ
      (fun b _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
        (fun c _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
          (fun d _ => _root_.MeasureTheory.memLp_finsetSum Finset.univ
            (fun e _ => hflim a b c d e)))))
    (fun a => tendsto_sum4 (I := I) (M := M) α
      (f := fun b c d e n => f a b c d e n)
      (flim := fun b c d e => flim a b c d e)
      (fun b c d e n => hf a b c d e n)
      (fun b c d e => hflim a b c d e)
      (fun b c d e => h_tendsto a b c d e))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_sum5 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_sum5"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_sum5 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_sum5

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
lemma differentiableAt_of_contDiffOn_chartTarget
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    DifferentiableAt ℝ c y := by
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  exact (hc.contDiffAt (hopen.mem_nhds hy)).differentiableAt (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_of_contDiffOn_chartTarget then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_of_contDiffOn_chartTarget"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_of_contDiffOn_chartTarget ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_of_contDiffOn_chartTarget

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma differentiableAt_tensorChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (y : EuclN) :
    DifferentiableAt ℝ
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y :=
  ((tensorChartComponent_contDiff_top (I := I) (M := M) g r s S α Idx Jdx).differentiable
    (by simp)).differentiableAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_tensorChartComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_tensorChartComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_tensorChartComponent ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.differentiableAt_tensorChartComponent

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma toLp_add_eq
    (α : M) {f₁ f₂ F : EuclN → ℝ}
    (hf₁ : _root_.MeasureTheory.MemLp f₁ 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (hf₂ : _root_.MeasureTheory.MemLp f₂ 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (hF : _root_.MeasureTheory.MemLp F 2 (chartLebesgueMeasure (I := I) (M := M) α))
    (hFeq : F =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      fun y => f₁ y + f₂ y) :
    hF.toLp F = hf₁.toLp f₁ + hf₂.toLp f₂ := by
  classical
  apply Lp.ext
  refine (MemLp.coeFn_toLp hF).trans (hFeq.trans ?_)
  refine Filter.EventuallyEq.symm ?_
  refine (Lp.coeFn_add (hf₁.toLp f₁) (hf₂.toLp f₂)).trans ?_
  filter_upwards [MemLp.coeFn_toLp hf₁, MemLp.coeFn_toLp hf₂] with y hy₁ hy₂
  rw [Pi.add_apply, hy₁, hy₂]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toLp_add_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toLp_add_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toLp_add_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toLp_add_eq

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
