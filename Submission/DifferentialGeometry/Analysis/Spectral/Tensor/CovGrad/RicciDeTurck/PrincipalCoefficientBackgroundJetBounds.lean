import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNorm.UniformBound
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_cometricDoubleTraceCoefficient_self_fibre_jetL2_bound
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ Λ Γ : ℝ, 0 ≤ Λ ∧ 0 ≤ Γ ∧
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₀).toSection x) ≤ Λ ^ 2) ∧
      (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₀)‖ ^ 2) ≤ Γ ^ 2 := by
  obtain ⟨K, hK_nn, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
    g₀ 4 2 (cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₀)
  refine ⟨Real.sqrt K, Real.sqrt (∑ i ∈ Finset.range (a + 1),
      ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₀)‖ ^ 2),
    Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_, ?_⟩
  · intro x
    rw [Real.sq_sqrt hK_nn]
    exact hK x
  · rw [Real.sq_sqrt (by positivity)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_cometricDoubleTraceCoefficient_self_fibre_jetL2_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_cometricDoubleTraceCoefficient_self_fibre_jetL2_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_cometricDoubleTraceCoefficient_self_fibre_jetL2_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_cometricDoubleTraceCoefficient_self_fibre_jetL2_bound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
