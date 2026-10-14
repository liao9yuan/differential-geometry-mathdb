import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.WeightedSecondCovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

noncomputable def chartInvGramPrincipalSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) : ℝ :=
  ∑ k : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g α b k l *
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k)
                (fun z : M => T₀.toSection z)) b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l b)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartInvGramPrincipalSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartInvGramPrincipalSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartInvGramPrincipalSum ``Submission.DifferentialGeometry.Analysis.Elliptic.chartInvGramPrincipalSum

noncomputable def chartFrameCoordMatrixWeightedDoubleSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                (fun z : M => T₀.toSection z)) b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l b)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartFrameCoordMatrixWeightedDoubleSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartFrameCoordMatrixWeightedDoubleSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartFrameCoordMatrixWeightedDoubleSum ``Submission.DifferentialGeometry.Analysis.Elliptic.chartFrameCoordMatrixWeightedDoubleSum

noncomputable def chartLeibnizRemainder
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) : ℝ :=
  chartFrameCoordMatrixWeightedDoubleSum (I := I) (M := M) g r s α T₀ Idx Jdx b -
    chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartLeibnizRemainder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartLeibnizRemainder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartLeibnizRemainder ``Submission.DifferentialGeometry.Analysis.Elliptic.chartLeibnizRemainder

noncomputable def chartFrameTraceΓCorrection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    tensorChartComponentProjection (E := E) r s Idx Jdx
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
          (fun z : M => T₀.toSection z) b
          ((LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓCorrection ``Submission.DifferentialGeometry.Analysis.Elliptic.chartFrameTraceΓCorrection

omit [I.Boundaryless] in
lemma chartInvGramPrincipal_plus_LeibnizRemainder_eq_frameWeighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) :
    chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b +
        chartLeibnizRemainder (I := I) (M := M) g r s α T₀ Idx Jdx b =
      chartFrameCoordMatrixWeightedDoubleSum (I := I) (M := M)
        g r s α T₀ Idx Jdx b := by
  classical
  unfold chartLeibnizRemainder
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartInvGramPrincipal_plus_LeibnizRemainder_eq_frameWeighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartInvGramPrincipal_plus_LeibnizRemainder_eq_frameWeighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartInvGramPrincipal_plus_LeibnizRemainder_eq_frameWeighted ``Submission.DifferentialGeometry.Analysis.Elliptic.chartInvGramPrincipal_plus_LeibnizRemainder_eq_frameWeighted

omit [I.Boundaryless] in
theorem chartPushed_rawConnLap_chart_α_proj_eq_chartInvGram_secondCovDeriv_plus_corrections
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
      (chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b +
        chartLeibnizRemainder (I := I) (M := M) g r s α T₀ Idx Jdx b) -
      chartFrameTraceΓCorrection (I := I) (M := M) g r s α T₀ Idx Jdx b := by
  classical
  have hPred :=
    chartPushed_rawConnLap_chart_α_proj_eq_weighted_secondCovDeriv_minus_frameTraceΓ
      (I := I) (M := M) g r s α T₀ Idx Jdx (b := b) hb
  rw [hPred]
  have hFrameWeighted_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                    (fun z : M => T₀.toSection z)) b
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α l b)))) =
        chartFrameCoordMatrixWeightedDoubleSum (I := I) (M := M)
          g r s α T₀ Idx Jdx b := rfl
  rw [hFrameWeighted_eq]
  have hΓ_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))) =
        chartFrameTraceΓCorrection (I := I) (M := M) g r s α T₀ Idx Jdx b := rfl
  rw [hΓ_eq]
  have hSplit :=
    chartInvGramPrincipal_plus_LeibnizRemainder_eq_frameWeighted
      (I := I) (M := M) g r s α T₀ Idx Jdx b
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLap_chart_α_proj_eq_chartInvGram_secondCovDeriv_plus_corrections then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLap_chart_α_proj_eq_chartInvGram_secondCovDeriv_plus_corrections"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLap_chart_α_proj_eq_chartInvGram_secondCovDeriv_plus_corrections ``Submission.DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLap_chart_α_proj_eq_chartInvGram_secondCovDeriv_plus_corrections

end Elliptic
end Analysis
end DifferentialGeometry

end
