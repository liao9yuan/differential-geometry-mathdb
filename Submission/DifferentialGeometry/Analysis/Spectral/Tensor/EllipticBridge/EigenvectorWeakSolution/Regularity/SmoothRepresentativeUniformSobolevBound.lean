import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.ArbitraryOrderSobolevBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.SmoothRepresentativeSecondOrderSobolev
import Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.Chart.Locality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor

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

section MainResults


namespace EigenvectorManifoldAggregate

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)

private noncomputable def perChartCompConstant
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : ℝ :=
  Classical.choose
    (eigenvector_chartComponent_wkpNorm_arbitrary (I := I) (M := M)
      g r s (2 * k) α (Idx, Jdx))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenvectorManifoldAggregate.perChartCompConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenvectorManifoldAggregate.perChartCompConstant target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma perChartCompConstant_nonneg
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    0 ≤ perChartCompConstant (I := I) (M := M) g r s k α Idx Jdx :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_arbitrary (I := I) (M := M)
      g r s (2 * k) α (Idx, Jdx))).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenvectorManifoldAggregate.perChartCompConstant_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenvectorManifoldAggregate.perChartCompConstant_nonneg target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma perChartCompConstant_bound
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α (Idx, Jdx))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          (perChartCompConstant (I := I) (M := M)
              g r s k α Idx Jdx *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec
            (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_arbitrary (I := I) (M := M)
      g r s (2 * k) α (Idx, Jdx))).2 i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenvectorManifoldAggregate.perChartCompConstant_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenvectorManifoldAggregate.perChartCompConstant_bound target :: scope.openDecls } }

private noncomputable def aggregateConstant : ℝ :=
  ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        perChartCompConstant (I := I) (M := M) g r s k α Idx Jdx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenvectorManifoldAggregate.aggregateConstant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenvectorManifoldAggregate.aggregateConstant target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma aggregateConstant_nonneg :
    0 ≤ aggregateConstant (I := I) (M := M) g r s k := by
  classical
  unfold aggregateConstant
  refine Finset.sum_nonneg fun α _ => ?_
  refine Finset.sum_nonneg fun Idx _ => ?_
  refine Finset.sum_nonneg fun Jdx _ => ?_
  exact perChartCompConstant_nonneg
    (I := I) (M := M) g r s k α Idx Jdx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenvectorManifoldAggregate.aggregateConstant_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenvectorManifoldAggregate.aggregateConstant_nonneg target :: scope.openDecls } }

end EigenvectorManifoldAggregate

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenvectorManifoldAggregate

omit [CompleteSpace E] in
private lemma tensorChartComp_eigenvectorSmooth_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s i) α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          (perChartCompConstant (I := I) (M := M)
              g r s k α Idx Jdx *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec
            (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
  have h_ae :
      tensorChartComp (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s i) α Idx Jdx
        =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun (I := I) (M := M) g r s i α
        (Idx, Jdx) :=
    eigenvectorSmooth_tensorChartComp_aeEq_chartComponentFun
      (I := I) (M := M) g r s i α Idx Jdx
  have h_eq :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s
            (eigenvectorSmooth (I := I) (M := M) g r s i)
            α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) =
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α (Idx, Jdx))
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae
  rw [h_eq]
  exact perChartCompConstant_bound
    (I := I) (M := M) g r s k α Idx Jdx i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComp_eigenvectorSmooth_wkpNorm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComp_eigenvectorSmooth_wkpNorm_le target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma chartTerm_eigenvectorSmooth_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) (α : M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s
              (eigenvectorSmooth (I := I) (M := M) g r s i)
              α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal
          ((∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                perChartCompConstant (I := I) (M := M)
                  g r s k α Idx Jdx)
            * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec
            (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
  classical
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    le_trans zero_le_one
      (sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s i)
  have hμ_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ (2 * k + 1) :=
    pow_nonneg hμ_inv_nn _
  have h_double_le :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∀ _hIdx : Idx ∈ (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))),
        (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
              (tensorChartComp (I := I) (M := M) g r s
                (eigenvectorSmooth (I := I) (M := M) g r s i)
                α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ENNReal.ofReal
                (perChartCompConstant
                  (I := I) (M := M) g r s k α Idx Jdx *
                    (i.fst.val)⁻¹ ^ (2 * k + 1))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i‖ := by
    intro Idx _hIdx
    refine le_trans (Finset.sum_le_sum (fun Jdx _ =>
      tensorChartComp_eigenvectorSmooth_wkpNorm_le
        (I := I) (M := M) g r s k α Idx Jdx i)) ?_
    rw [← Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum h_double_le) ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le)
  have h_inner :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∀ _hIdx : Idx ∈ (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))),
        (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (perChartCompConstant (I := I) (M := M)
                  g r s k α Idx Jdx *
                (i.fst.val)⁻¹ ^ (2 * k + 1))) =
          ENNReal.ofReal
            ((∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              perChartCompConstant (I := I) (M := M)
                g r s k α Idx Jdx) *
              (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
    intro Idx _hIdx
    rw [Finset.sum_mul]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun Jdx _ =>
      mul_nonneg (perChartCompConstant_nonneg
        (I := I) (M := M) g r s k α Idx Jdx) hμ_pow_nn)]
  rw [Finset.sum_congr rfl h_inner]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun Idx _ =>
    mul_nonneg
      (Finset.sum_nonneg (fun Jdx _ =>
        perChartCompConstant_nonneg
          (I := I) (M := M) g r s k α Idx Jdx)) hμ_pow_nn)]
  have h_eq :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            perChartCompConstant (I := I) (M := M)
              g r s k α Idx Jdx) *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) =
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            perChartCompConstant (I := I) (M := M)
              g r s k α Idx Jdx) *
          (i.fst.val)⁻¹ ^ (2 * k + 1) := by
    rw [Finset.sum_mul]
  rw [h_eq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTerm_eigenvectorSmooth_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTerm_eigenvectorSmooth_le target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem eigenvectorSmooth_wtwokTwoNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
        wtwokTwoNorm (I := I) (M := M) g k
            (eigenvectorSmooth (I := I) (M := M) g r s i)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  refine ⟨aggregateConstant (I := I) (M := M) g r s k,
    aggregateConstant_nonneg (I := I) (M := M) g r s k,
    fun i => ?_⟩
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    le_trans zero_le_one
      (sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s i)
  have hμ_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ (2 * k + 1) :=
    pow_nonneg hμ_inv_nn _
  rw [wtwokTwoNorm_eq_finset_sum (I := I) (M := M) g k
    (eigenvectorSmooth (I := I) (M := M) g r s i)]
  refine le_trans (Finset.sum_le_sum
    (fun α _hα => chartTerm_eigenvectorSmooth_le
      (I := I) (M := M) g r s k α i)) ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ =>
    mul_nonneg
      (Finset.sum_nonneg (fun Idx _ =>
        Finset.sum_nonneg (fun Jdx _ =>
          perChartCompConstant_nonneg
            (I := I) (M := M) g r s k α Idx Jdx))) hμ_pow_nn)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.sum_mul]
  exact le_of_eq rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_wtwokTwoNorm_le_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_wtwokTwoNorm_le_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_wtwokTwoNorm_le_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_wtwokTwoNorm_le_uniform

end MainResults

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
