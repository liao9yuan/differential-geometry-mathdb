import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.ContractionJetTower
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.RicciTrace.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorAction.Field

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

def ricBackgroundSlotCoeff (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM
          (slotInsertEndoFib (I := I) (M := M) 2 0 x (ricEndoRaisedFib (I := I) g₀ x))
      contMDiff_toFun :=
        slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 0
          (fun x : M => ricEndoRaisedFib (I := I) g₀ x)
          (ricEndoRaisedFib_contMDiff (I := I) g₀) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ricBackgroundSlotCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ricBackgroundSlotCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ricBackgroundSlotCoeff ``Submission.DifferentialGeometry.Analysis.Spectral.ricBackgroundSlotCoeff

def ricBackgroundTermCoeffField (g₀ : SmoothRiemannianMetric I M) :
    ∀ r : ℕ, SmoothCcTensor g₀ (r + 0) (r + 0) :=
  fun r => match r with
    | 2 => ricBackgroundSlotCoeff (I := I) g₀
    | _ => 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ricBackgroundTermCoeffField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ricBackgroundTermCoeffField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ricBackgroundTermCoeffField ``Submission.DifferentialGeometry.Analysis.Spectral.ricBackgroundTermCoeffField

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ricBackgroundTerm_iteratedCovGrad_singleSum_le
    (g₀ : SmoothRiemannianMetric I M) (x₀ : M) (W : SmoothCcTensor g₀ 0 2) (a : ℕ) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x₀
        ((iteratedCovGrad g₀ 0 2 a
          ((fixedCoeffDiffOp (I := I) (M := M) g₀
            (ricBackgroundTermCoeffField (I := I) g₀)).op 0 2 W)).toSection x₀) ≤
      ((4 : ℝ) ^ a * gridWindowSum
          (fixedCoeffDiffOp (I := I) (M := M) g₀
            (ricBackgroundTermCoeffField (I := I) g₀)).kappa 0 2 a) *
        ∑ q ∈ Finset.range (a + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x₀
            ((iteratedCovGrad g₀ 0 2 q W).toSection x₀) :=
  fixedCoeffDiffOp_iteratedCovGrad_singleSum_le (I := I) (M := M) g₀
    (ricBackgroundTermCoeffField (I := I) g₀) x₀ 2 W a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ricBackgroundTerm_iteratedCovGrad_singleSum_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ricBackgroundTerm_iteratedCovGrad_singleSum_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ricBackgroundTerm_iteratedCovGrad_singleSum_le ``Submission.DifferentialGeometry.Analysis.Spectral.ricBackgroundTerm_iteratedCovGrad_singleSum_le

end Spectral
end Analysis
end DifferentialGeometry

end
