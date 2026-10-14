import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.GradientEnergyBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.CoefficientLimits
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.RightDivergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Spectral
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
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

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
private lemma eigenvalue_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm :
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ = 1 :=
        (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s)).norm_eq_one i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvalue_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvalue_pos target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma eLpNorm_lpClass_eq_ofReal_norm
    (α : M) (w : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
    _root_.MeasureTheory.eLpNorm ((w : EuclN → ℝ)) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      = ENNReal.ofReal ‖w‖ := by
  have h_eq : _root_.MeasureTheory.eLpNorm ((w : EuclN → ℝ)) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm ((w : EuclN → ℝ)) 2 (chartLebesgueMeasure (I := I) (M := M) α) := rfl
  rw [h_eq, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top w)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_lpClass_eq_ofReal_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_lpClass_eq_ofReal_norm target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
private lemma partialLpLimit_eq_clm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    partialLpLimit (I := I) (M := M) g r s i α P k =
      eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k
        (eigenvectorResolvent (I := I) (M := M) g r s i) := by
  rw [partialLpLimit, eigenvectorChartPartialLp,
    smul_smul,
    mul_inv_cancel₀ (eigenvalue_pos (I := I) (M := M) g r s i).ne',
    one_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialLpLimit_eq_clm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialLpLimit_eq_clm target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
private lemma partialLpLimit_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ‖partialLpLimit (I := I) (M := M) g r s i α P k‖ ≤
      ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
        ‖eigenvectorResolvent (I := I) (M := M) g r s i‖ := by
  rw [partialLpLimit_eq_clm (I := I) (M := M) g r s i α P k]
  exact (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k).le_opNorm _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialLpLimit_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialLpLimit_norm_le target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
theorem partialLpLimit_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm ((partialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal
            (C * Real.sqrt (i.fst.val)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
  classical
  refine ⟨‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖,
    norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k),
    fun i => ?_⟩
  rw [eLpNorm_lpClass_eq_ofReal_norm (I := I) (M := M) α
    (partialLpLimit (I := I) (M := M) g r s i α P k)]
  have h_bound :
      ‖partialLpLimit (I := I) (M := M) g r s i α P k‖ ≤
        ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            Real.sqrt (i.fst.val) *
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    calc ‖partialLpLimit (I := I) (M := M) g r s i α P k‖
        ≤ ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            ‖eigenvectorResolvent (I := I) (M := M) g r s i‖ :=
          partialLpLimit_norm_le (I := I) (M := M) g r s i α P k
      _ ≤ ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            (Real.sqrt (i.fst.val) *
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) :=
          mul_le_mul_of_nonneg_left
            (eigenvectorResolvent_h1Norm_le (I := I) (M := M)
              g r s i)
            (norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M)
              g r s α P k))
      _ = ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            Real.sqrt (i.fst.val) *
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
          ring
  have h_factor_nn :
      0 ≤ ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
        Real.sqrt (i.fst.val) :=
    mul_nonneg
      (norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k))
      (Real.sqrt_nonneg _)
  rw [← ENNReal.ofReal_mul h_factor_nn]
  exact ENNReal.ofReal_le_ofReal h_bound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialLpLimit_eLpNorm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialLpLimit_eLpNorm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialLpLimit_eLpNorm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialLpLimit_eLpNorm_le

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
private lemma cutoffPartialLpLimit_eq_clm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    cutoffPartialLpLimit (I := I) (M := M) g r s i α P k =
      eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k
        (eigenvectorResolvent (I := I) (M := M) g r s i) := by
  rw [cutoffPartialLpLimit,
    eigenvectorCutoffChartPartialLp, smul_smul,
    mul_inv_cancel₀ (eigenvalue_pos (I := I) (M := M) g r s i).ne',
    one_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffPartialLpLimit_eq_clm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffPartialLpLimit_eq_clm target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
private lemma cutoffPartialLpLimit_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ‖cutoffPartialLpLimit (I := I) (M := M) g r s i α P k‖ ≤
      ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k‖ *
        ‖eigenvectorResolvent (I := I) (M := M) g r s i‖ := by
  rw [cutoffPartialLpLimit_eq_clm (I := I) (M := M) g r s i α P k]
  exact (eigenvectorCutoffChartPartialCLM (I := I) (M := M)
    g r s α P k).le_opNorm _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffPartialLpLimit_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffPartialLpLimit_norm_le target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
theorem cutoffPartialLpLimit_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal
            (C * Real.sqrt (i.fst.val)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
  classical
  refine ⟨‖eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k‖,
    norm_nonneg (eigenvectorCutoffChartPartialCLM (I := I) (M := M)
      g r s α P k),
    fun i => ?_⟩
  rw [eLpNorm_lpClass_eq_ofReal_norm (I := I) (M := M) α
    (cutoffPartialLpLimit (I := I) (M := M) g r s i α P k)]
  have h_bound :
      ‖cutoffPartialLpLimit (I := I) (M := M) g r s i α P k‖ ≤
        ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            Real.sqrt (i.fst.val) *
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    calc ‖cutoffPartialLpLimit (I := I) (M := M) g r s i α P k‖
        ≤ ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M)
              g r s α P k‖ *
            ‖eigenvectorResolvent (I := I) (M := M) g r s i‖ :=
          cutoffPartialLpLimit_norm_le (I := I) (M := M)
            g r s i α P k
      _ ≤ ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M)
              g r s α P k‖ *
            (Real.sqrt (i.fst.val) *
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) :=
          mul_le_mul_of_nonneg_left
            (eigenvectorResolvent_h1Norm_le (I := I) (M := M)
              g r s i)
            (norm_nonneg (eigenvectorCutoffChartPartialCLM (I := I) (M := M)
              g r s α P k))
      _ = ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M)
              g r s α P k‖ *
            Real.sqrt (i.fst.val) *
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
          ring
  have h_factor_nn :
      0 ≤ ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M)
          g r s α P k‖ * Real.sqrt (i.fst.val) :=
    mul_nonneg
      (norm_nonneg (eigenvectorCutoffChartPartialCLM (I := I) (M := M)
        g r s α P k))
      (Real.sqrt_nonneg _)
  rw [← ENNReal.ofReal_mul h_factor_nn]
  exact ENNReal.ofReal_le_ofReal h_bound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffPartialLpLimit_eLpNorm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffPartialLpLimit_eLpNorm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffPartialLpLimit_eLpNorm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffPartialLpLimit_eLpNorm_le

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
