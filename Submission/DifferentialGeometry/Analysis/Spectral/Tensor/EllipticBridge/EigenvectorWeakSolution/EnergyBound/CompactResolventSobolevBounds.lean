import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Differentiated.Defs
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.PartitionOfUnitySobolev.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.SmoothRepresentative.Approximation
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Chart.WeightedLpBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

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

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity

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

omit [CompleteSpace E] in
private lemma mu_mul_inv_pow_le_inv_pow
    {μ : ℝ} (hμ_pos : 0 < μ) (hμ_le_one : μ ≤ 1) (eN : ℕ) :
    μ * μ⁻¹ ^ eN ≤ μ⁻¹ ^ eN := by
  have hμ_inv_nn : 0 ≤ μ⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_pow_nn : 0 ≤ μ⁻¹ ^ eN := pow_nonneg hμ_inv_nn _
  have h : μ * μ⁻¹ ^ eN ≤ 1 * μ⁻¹ ^ eN :=
    mul_le_mul_of_nonneg_right hμ_le_one hμ_inv_pow_nn
  simpa using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mu_mul_inv_pow_le_inv_pow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mu_mul_inv_pow_le_inv_pow target :: scope.openDecls } }

section MainResults


omit [CompleteSpace E] in
private lemma vec_norm_eq_one_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ = 1 :=
  (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (tensorResolventL2_isCompactOperator (I := I) (M := M)
      g r s)).norm_eq_one i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.vec_norm_eq_one_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.vec_norm_eq_one_local target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenval_pos_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one_local
        (I := I) (M := M) g r s i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenval_pos_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenval_pos_local target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenval_le_one_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    i.fst.val ≤ 1 :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one_local
        (I := I) (M := M) g r s i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenval_le_one_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenval_le_one_local target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem eigenvector_chartComponent_perK_from_uniform_β
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (N : ℕ)
    (CN : ℝ) (eN : ℕ)
    (hCN_bd : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ (K' : ℕ), K' ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  intro K' hK' i
  have h_mono : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_mono_order (d := Module.finrank ℝ E) hK'
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)
  exact h_mono.trans (hCN_bd α P₀ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvector_chartComponent_perK_from_uniform_β then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvector_chartComponent_perK_from_uniform_β"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvector_chartComponent_perK_from_uniform_β ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvector_chartComponent_perK_from_uniform_β

omit [CompleteSpace E] in
private lemma resolvent_eq_mul_eigenvector
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i) =
      i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i := by
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rw [eigenvector_eq_resolvent_smul (I := I) (M := M) g r s i,
    smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.resolvent_eq_mul_eigenvector
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.resolvent_eq_mul_eigenvector target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma resolvent_chartComponent_eq_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q =
      i.fst.val •
        tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) β Q := by
  rw [resolvent_eq_mul_eigenvector (I := I) (M := M) g r s i]
  exact tensorL2ChartComponent_smul (I := I) (M := M) g r s i.fst.val
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i) β Q

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.resolvent_chartComponent_eq_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.resolvent_chartComponent_eq_smul target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma resolvent_chartComponent_coe_ae_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) β)]
      (fun y => i.fst.val *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s i β Q y) := by
  have h_smul := Lp.coeFn_smul i.fst.val
    (tensorL2ChartComponent (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i) β Q)
  have h_eq : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) β]
      (fun y => i.fst.val •
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s i β Q y) := by
    rw [resolvent_chartComponent_eq_smul
      (I := I) (M := M) g r s i β Q]
    exact h_smul
  filter_upwards [h_eq] with y hy
  rw [hy, smul_eq_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.resolvent_chartComponent_coe_ae_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.resolvent_chartComponent_coe_ae_eq target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma eigenvectorChartComponentFun_memWkp_of_resolv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ)
    (h_resolv : MemWkp (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s i β Q)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_scaled : MemWkp (d := Module.finrank ℝ E) K' 2
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
            EuclN → ℝ) y) Ω :=
    MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_resolv (i.fst.val)⁻¹
  have h_ae : (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω]
      (fun y => eigenvectorChartComponentFun (I := I) (M := M)
        g r s i β Q y) := by
    have h_resc := resolvent_chartComponent_coe_ae_eq
      (I := I) (M := M) g r s i β Q
    have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
    filter_upwards [h_resc] with y hy
    rw [hy]
    field_simp
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mp h_scaled

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentFun_memWkp_of_resolv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentFun_memWkp_of_resolv target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem eigenvector_resolventHigh_perK_from_uniform_β
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (N : ℕ)
    (CN : ℝ) (hCN_nn : 0 ≤ CN) (eN : ℕ)
    (hCN_bd : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (resolventComponentRegularity : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
        (β : M) (Q : TensorCompIdx (E := E) r s),
      K' + 1 ≤ N →
      MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∀ (K' : ℕ), K' + 1 ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  intro K' hK' i β Q
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have hμ_pos : 0 < i.fst.val := eigenval_pos_local
    (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 := eigenval_le_one_local
    (I := I) (M := M) g r s i
  have h_resolv_mem : MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
      Ω :=
    resolventComponentRegularity i K' β Q hK'
  have h_eig_mem : MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s i β Q) Ω :=
    eigenvectorChartComponentFun_memWkp_of_resolv
      (I := I) (M := M) g r s i β Q (K' + 1) h_resolv_mem
  have h_ae := resolvent_chartComponent_coe_ae_eq
    (I := I) (M := M) g r s i β Q
  have h_norm_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      = iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
        (fun y => i.fst.val *
          eigenvectorChartComponentFun (I := I) (M := M)
            g r s i β Q y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae
  have h_smul_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (fun y => i.fst.val *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s i β Q y) Ω
      = ‖i.fst.val‖ₑ *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i β Q) Ω :=
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_eig_mem i.fst.val
  have h_eig_bd : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s i β Q) Ω
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ :=
    eigenvector_chartComponent_perK_from_uniform_β
      (I := I) (M := M) g r s N CN eN hCN_bd β Q (K' + 1) hK' i
  rw [h_norm_eq, h_smul_eq]
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  have h_step1 :
      ENNReal.ofReal i.fst.val *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i β Q) Ω
      ≤ ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) :=
    mul_le_mul_of_nonneg_left h_eig_bd (zero_le)
  have h_mul_assoc :
      ENNReal.ofReal i.fst.val *
        (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) =
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hμ_pos.le]
  have h_step2 :
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (zero_le)
    refine ENNReal.ofReal_le_ofReal ?_
    have h_reorder : i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)
        = CN * (i.fst.val * (i.fst.val)⁻¹ ^ eN) := by ring
    rw [h_reorder]
    have h_mu_bd := mu_mul_inv_pow_le_inv_pow hμ_pos hμ_le_one eN
    exact mul_le_mul_of_nonneg_left h_mu_bd hCN_nn
  calc
    ENNReal.ofReal i.fst.val *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i β Q) Ω
        ≤ ENNReal.ofReal i.fst.val *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖) :=
      h_step1
    _ = ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
      h_mul_assoc
    _ ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
      h_step2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvector_resolventHigh_perK_from_uniform_β then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvector_resolventHigh_perK_from_uniform_β"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvector_resolventHigh_perK_from_uniform_β ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvector_resolventHigh_perK_from_uniform_β

omit [CompleteSpace E] in
theorem eigenvector_resolventLow_perK_from_uniform_β
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (N : ℕ)
    (CN : ℝ) (hCN_nn : 0 ≤ CN) (eN : ℕ)
    (hCN_bd : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (resolventComponentRegularity : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
        (β : M) (Q : TensorCompIdx (E := E) r s),
      K' ≤ N →
      MemWkp (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∀ (K' : ℕ), K' ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  intro K' hK' i β Q
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have hμ_pos : 0 < i.fst.val := eigenval_pos_local
    (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 := eigenval_le_one_local
    (I := I) (M := M) g r s i
  have h_resolv_mem : MemWkp (d := Module.finrank ℝ E) K' 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
      Ω :=
    resolventComponentRegularity i K' β Q hK'
  have h_eig_mem : MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s i β Q) Ω :=
    eigenvectorChartComponentFun_memWkp_of_resolv
      (I := I) (M := M) g r s i β Q K' h_resolv_mem
  have h_ae := resolvent_chartComponent_coe_ae_eq
    (I := I) (M := M) g r s i β Q
  have h_norm_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      = iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
        (fun y => i.fst.val *
          eigenvectorChartComponentFun (I := I) (M := M)
            g r s i β Q y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae
  have h_smul_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
      (fun y => i.fst.val *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s i β Q y) Ω
      = ‖i.fst.val‖ₑ *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i β Q) Ω :=
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_eig_mem i.fst.val
  have h_eig_bd : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s i β Q) Ω
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ :=
    eigenvector_chartComponent_perK_from_uniform_β
      (I := I) (M := M) g r s N CN eN hCN_bd β Q K' hK' i
  rw [h_norm_eq, h_smul_eq]
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  have h_step1 :
      ENNReal.ofReal i.fst.val *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i β Q) Ω
      ≤ ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) :=
    mul_le_mul_of_nonneg_left h_eig_bd (zero_le)
  have h_mul_assoc :
      ENNReal.ofReal i.fst.val *
        (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) =
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hμ_pos.le]
  have h_step2 :
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (zero_le)
    refine ENNReal.ofReal_le_ofReal ?_
    have h_reorder : i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)
        = CN * (i.fst.val * (i.fst.val)⁻¹ ^ eN) := by ring
    rw [h_reorder]
    have h_mu_bd := mu_mul_inv_pow_le_inv_pow hμ_pos hμ_le_one eN
    exact mul_le_mul_of_nonneg_left h_mu_bd hCN_nn
  calc
    ENNReal.ofReal i.fst.val *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i β Q) Ω
        ≤ ENNReal.ofReal i.fst.val *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖) :=
      h_step1
    _ = ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
      h_mul_assoc
    _ ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
      h_step2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvector_resolventLow_perK_from_uniform_β then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvector_resolventLow_perK_from_uniform_β"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvector_resolventLow_perK_from_uniform_β ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvector_resolventLow_perK_from_uniform_β

end MainResults

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
