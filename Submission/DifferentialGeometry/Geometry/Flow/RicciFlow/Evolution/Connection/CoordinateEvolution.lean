import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.CoordinateRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem christoffel_hasDerivAt_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (x₀ : M) (t : D.RegularTime)
    {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j k : CoordinateIdx (𝕜 := ℝ) E) :
    HasDerivAt
      (fun s : ℝ => christoffelSymbolInFrame
        (S.family.connection s) (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x i j k)
      (-(∑ l : CoordinateIdx (𝕜 := ℝ) E,
        coordInv S x₀ t x k l *
          (nablaRicComp S (coordinateFrameAt (I := I) x₀) t x i j l +
            nablaRicComp S (coordinateFrameAt (I := I) x₀) t x j i l -
            nablaRicComp S (coordinateFrameAt (I := I) x₀) t x l i j))) t := by
  have h := coordGammaEvolution S hS x₀
    (coordMetricMix S hS x₀ (coordMetricDeriv S hS x₀)) t x hx i j k
  refine (h.hasDerivAt (D.regular_mem_nhds t.2)).congr_deriv ?_
  simp only [christoffelEvolutionRHSInFrame, christoffelVariationLoweredRHSInFrame,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.christoffel_hasDerivAt_of_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.christoffel_hasDerivAt_of_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.christoffel_hasDerivAt_of_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.christoffel_hasDerivAt_of_solution

end DifferentialGeometry.PDE.RicciFlow
