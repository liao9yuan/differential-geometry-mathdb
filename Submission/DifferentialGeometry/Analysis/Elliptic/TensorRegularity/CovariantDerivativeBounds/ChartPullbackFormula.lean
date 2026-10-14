import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


open _root_.Submission.DifferentialGeometry.Integral.L2 (SmoothCcTensor)

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
private lemma good_set_mem_baseSet_rs
    (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet := by
  classical
  change b ∈ ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
    ((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).baseSet)
  refine ⟨?_, ?_⟩
  · change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  · change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.good_set_mem_baseSet_rs
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.good_set_mem_baseSet_rs target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chart_pulled_covApply_explicit_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T :
      letI _h_top : TopologicalSpace
          (_root_.Bundle.TotalSpace (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x)) :=
        tensorRSBundleTopology r s
      letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) :=
        tensorRSBundleFiber r s
      Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        fun b => TensorRSSpace r s I b⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorRSChartESectionRepr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) B.toFun T.toFun) b =
      fderiv ℝ
        (tensorRSChartESectionRepr (I := I) r s α T.toFun ∘
          (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (B.toFun b))
      + ∑ k : Fin r,
          (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              T.toFun B.toFun b k)
      - ∑ l : Fin s,
          (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              T.toFun B.toFun b l) := by
  classical
  let _h_top : TopologicalSpace
      (_root_.Bundle.TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundleTopology r s
  let _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundleFiber r s
  have hb_baseRS : b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet :=
    good_set_mem_baseSet_rs (I := I) r s α hb
  have hb_baseT : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hAgree :=
    chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet (I := I) (M := M)
      g r s α T B (b := b) hb
  have hLHS_eq :
      tensorRSChartESectionRepr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) B.toFun T.toFun) b =
        (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSCovariantDerivative (I := I) r s g α
            T.toFun B.toFun b) := by
    change (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) B.toFun T.toFun) b) = _
    change (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T.toFun b (B.toFun b)) = _
    rw [hAgree.symm]
  rw [hLHS_eq]
  rw [chartTensorRSCovariantDerivative_def (I := I) r s g α T.toFun B.toFun b]
  rw [map_sub, map_add]
  rw [show (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (∑ k : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α
            T.toFun B.toFun b k) =
      ∑ k : Fin r,
        (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            T.toFun B.toFun b k) from
    map_sum ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b) _ _]
  rw [show (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (∑ l : Fin s,
          chartTensorRSOutputSlotCorrection (I := I) r s g α
            T.toFun B.toFun b l) =
      ∑ l : Fin s,
        (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            T.toFun B.toFun b l) from
    map_sum ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b) _ _]
  rw [tensorRSIntrinsicChartCLM_apply (I := I) r s α T.toFun b (B.toFun b)]
  unfold tensorRSChartFiberFromModel
  rw [(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt_symmL
      (R := ℝ) hb_baseRS]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chart_pulled_covApply_explicit_formula then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chart_pulled_covApply_explicit_formula"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chart_pulled_covApply_explicit_formula ``Submission.DifferentialGeometry.Analysis.Elliptic.chart_pulled_covApply_explicit_formula

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem chart_pulled_covApply_explicit_formula_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T :
      letI _h_top : TopologicalSpace
          (_root_.Bundle.TotalSpace (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x)) :=
        tensorRSBundleTopology r s
      letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) :=
        tensorRSBundleFiber r s
      Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        fun b => TensorRSSpace r s I b⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {y : E} (hy_target : y ∈ (extChartAt I α).target)
    (hy_good : (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α) :
    (tensorRSChartESectionRepr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) B.toFun T.toFun) ∘
          (extChartAt I α).symm) y =
      fderiv ℝ
        (tensorRSChartESectionRepr (I := I) r s α T.toFun ∘
          (extChartAt I α).symm) y
        (trivToE (I := I) α ((extChartAt I α).symm y)
          (B.toFun ((extChartAt I α).symm y)))
      + ∑ k : Fin r,
          (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
            ℝ ((extChartAt I α).symm y)
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              T.toFun B.toFun ((extChartAt I α).symm y) k)
      - ∑ l : Fin s,
          (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
            ℝ ((extChartAt I α).symm y)
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              T.toFun B.toFun ((extChartAt I α).symm y) l) := by
  classical
  have h := chart_pulled_covApply_explicit_formula (I := I) (M := M)
    g r s α T B (b := (extChartAt I α).symm y) hy_good
  have hround : extChartAt I α ((extChartAt I α).symm y) = y :=
    (extChartAt I α).right_inv hy_target
  simp only [Function.comp_apply]
  rw [hround] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chart_pulled_covApply_explicit_formula_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chart_pulled_covApply_explicit_formula_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chart_pulled_covApply_explicit_formula_target ``Submission.DifferentialGeometry.Analysis.Elliptic.chart_pulled_covApply_explicit_formula_target

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem chart_pulled_covApply_explicit_formula_target_smoothCc
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {y : E} (hy_target : y ∈ (extChartAt I α).target)
    (hy_good : (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α) :
    (tensorRSChartESectionRepr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) B.toFun
          (fun b : M => T.toSection b)) ∘
          (extChartAt I α).symm) y =
      fderiv ℝ
        (tensorRSChartESectionRepr (I := I) r s α
          (fun b : M => T.toSection b) ∘
          (extChartAt I α).symm) y
        (trivToE (I := I) α ((extChartAt I α).symm y)
          (B.toFun ((extChartAt I α).symm y)))
      + ∑ k : Fin r,
          (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
            ℝ ((extChartAt I α).symm y)
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b : M => T.toSection b) B.toFun
              ((extChartAt I α).symm y) k)
      - ∑ l : Fin s,
          (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
            ℝ ((extChartAt I α).symm y)
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b : M => T.toSection b) B.toFun
              ((extChartAt I α).symm y) l) :=
  chart_pulled_covApply_explicit_formula_target (I := I) (M := M)
    g r s α T.toSection B hy_target hy_good

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chart_pulled_covApply_explicit_formula_target_smoothCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chart_pulled_covApply_explicit_formula_target_smoothCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chart_pulled_covApply_explicit_formula_target_smoothCc ``Submission.DifferentialGeometry.Analysis.Elliptic.chart_pulled_covApply_explicit_formula_target_smoothCc

end Elliptic
end Analysis
end DifferentialGeometry

end
