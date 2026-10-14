import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Reconstruction.TensorHilbertSobolev
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.SlotCorrectionComponent
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.RealInnerProductSpace _root_.InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace DeTurckCoefficients

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]


omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem chartGramMatrix_realize_apply
    (g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    (α x : M) (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ) α x a b =
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g_bg α x a b +
        ccTensorBilinSymm (I := I) g_bg T x
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α a x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α b x) := by
  rw [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
    tensorSectionRealizeMetric_inner (I := I) g_bg T hδ_lt hδ x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartGramMatrix_realize_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartGramMatrix_realize_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartGramMatrix_realize_apply ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartGramMatrix_realize_apply

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem chartGramOnE_realize_sub_eq_symm_rawComponent
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ)
    (α : M) (a b : Fin (Module.finrank ℝ E)) (y : E)
    (hp : (extChartAt I α).symm y ∈ (chartAt H α).source) :
    chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ) α a b y -
        chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T' hδ_lt hδ') α a b y =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α
            ![] ![a, b] ((extChartAt I α).symm y) +
          tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α
            ![] ![b, a] ((extChartAt I α).symm y)) := by
  classical
  set p : M := (extChartAt I α).symm y with hp_def
  rw [chartGramOnE_def, chartGramOnE_def]
  rw [chartGramMatrix_realize_apply (I := I) g_bg T hδ_lt hδ α p a b,
    chartGramMatrix_realize_apply (I := I) g_bg T' hδ_lt hδ' α p a b]
  rw [show (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g_bg α p a b +
        ccTensorBilinSymm (I := I) g_bg T p
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α a p) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α b p)) -
      (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g_bg α p a b +
        ccTensorBilinSymm (I := I) g_bg T' p
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α a p) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α b p)) =
      ccTensorBilinSymm (I := I) g_bg T p
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α a p) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α b p) -
        ccTensorBilinSymm (I := I) g_bg T' p
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α a p) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α b p) by ring]
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
  have hrawAB := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (T - T') α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![a, b] : Fin 2 → Fin (Module.finrank ℝ E))
  have hrawBA := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (T - T') α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![b, a] : Fin 2 → Fin (Module.finrank ℝ E))
  have hframe : chartFrameBasisModel (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := chartFrameBasisModel_apply (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) v
    rw [Fin.prod_univ_zero] at h
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact h
  rw [hframe] at hrawAB hrawBA
  have hbilin : ∀ (i j : Fin (Module.finrank ℝ E)),
      ((T - T').toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I p) ℝ)
          (fun k : Fin 2 =>
            DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        smoothCcTensorBilinForm (I := I) g_bg T p
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i p) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p) -
          smoothCcTensorBilinForm (I := I) g_bg T' p
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i p) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p) := by
    intro i j
    have hvecAB : (fun k : Fin 2 =>
        DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        ![DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i p, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p] := by
      funext k; fin_cases k <;> rfl
    rw [hvecAB, ccTensorBilin_apply, ccTensorBilin_apply]
    change Tensor0SSpace.toModel
        ((T - T').toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)))
        ![DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i p, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p] = _
    rw [SmoothCcTensor.toSection_sub]
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
    rfl
  rw [hrawAB, hrawBA, hbilin a b, hbilin b a]
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartGramOnE_realize_sub_eq_symm_rawComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartGramOnE_realize_sub_eq_symm_rawComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartGramOnE_realize_sub_eq_symm_rawComponent ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartGramOnE_realize_sub_eq_symm_rawComponent

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem chartGramOnE_realize_sub_eq_symm_rawComponent_two
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ')
    (α : M) (a b : Fin (Module.finrank ℝ E)) (y : E)
    (hp : (extChartAt I α).symm y ∈ (chartAt H α).source) :
    chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ) α a b y -
        chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T' hδ'_lt hδ') α a b y =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α
            ![] ![a, b] ((extChartAt I α).symm y) +
          tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α
            ![] ![b, a] ((extChartAt I α).symm y)) := by
  classical
  set p : M := (extChartAt I α).symm y with hp_def
  rw [chartGramOnE_def, chartGramOnE_def]
  rw [chartGramMatrix_realize_apply (I := I) g_bg T hδ_lt hδ α p a b,
    chartGramMatrix_realize_apply (I := I) g_bg T' hδ'_lt hδ' α p a b]
  rw [show (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g_bg α p a b +
        ccTensorBilinSymm (I := I) g_bg T p
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α a p) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α b p)) -
      (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g_bg α p a b +
        ccTensorBilinSymm (I := I) g_bg T' p
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α a p) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α b p)) =
      ccTensorBilinSymm (I := I) g_bg T p
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α a p) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α b p) -
        ccTensorBilinSymm (I := I) g_bg T' p
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α a p) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α b p) by ring]
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
  have hrawAB := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (T - T') α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![a, b] : Fin 2 → Fin (Module.finrank ℝ E))
  have hrawBA := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (T - T') α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![b, a] : Fin 2 → Fin (Module.finrank ℝ E))
  have hframe : chartFrameBasisModel (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := chartFrameBasisModel_apply (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) v
    rw [Fin.prod_univ_zero] at h
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact h
  rw [hframe] at hrawAB hrawBA
  have hbilin : ∀ (i j : Fin (Module.finrank ℝ E)),
      ((T - T').toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I p) ℝ)
          (fun k : Fin 2 =>
            DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        smoothCcTensorBilinForm (I := I) g_bg T p
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i p) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p) -
          smoothCcTensorBilinForm (I := I) g_bg T' p
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i p) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p) := by
    intro i j
    have hvecAB : (fun k : Fin 2 =>
        DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        ![DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i p, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p] := by
      funext k; fin_cases k <;> rfl
    rw [hvecAB, ccTensorBilin_apply, ccTensorBilin_apply]
    change Tensor0SSpace.toModel
        ((T - T').toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)))
        ![DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i p, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j p] = _
    rw [SmoothCcTensor.toSection_sub]
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
    rfl
  rw [hrawAB, hrawBA, hbilin a b, hbilin b a]
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartGramOnE_realize_sub_eq_symm_rawComponent_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartGramOnE_realize_sub_eq_symm_rawComponent_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartGramOnE_realize_sub_eq_symm_rawComponent_two ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartGramOnE_realize_sub_eq_symm_rawComponent_two

end DeTurckCoefficients
end Spectral
end Analysis
end DifferentialGeometry

end
