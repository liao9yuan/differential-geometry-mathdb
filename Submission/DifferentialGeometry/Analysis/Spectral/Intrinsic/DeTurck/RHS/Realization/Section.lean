import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.Symmetry
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.Naturality
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Reconstruction.TensorHilbertSobolev

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral (unitModel)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem unitModel_of_deTurckRHSSection_realize
    (g₀ g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (W : SmoothCcTensor g₀ 0 2)
    (hW : W.toSection =
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 W x v =
      deTurckRicciRHS (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) := by
  rw [unitModel]
  change Tensor0SSpace.toModel ((W.toSection x) _) v = _
  rw [hW, Tensor0SSpace.toModel_apply_model_vector]
  exact deTurckRHSSection_eval (I := I) g_bg
    (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.unitModel_of_deTurckRHSSection_realize then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.unitModel_of_deTurckRHSSection_realize"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.unitModel_of_deTurckRHSSection_realize ``Submission.DifferentialGeometry.Analysis.Spectral.unitModel_of_deTurckRHSSection_realize

end DifferentialGeometry.Analysis.Spectral
