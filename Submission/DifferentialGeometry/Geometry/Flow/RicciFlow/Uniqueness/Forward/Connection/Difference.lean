import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Christoffel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem christoffelEvolutionDiffInFrameOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S₁ S₂ : SolutionOn (I := I) (M := M) D)
    (gInv₁ gInv₂ : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic₁ nablaRic₂ : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h₁ : ChristoffelEvolutionEquationInFrameOn
      (I := I) S₁ gInv₁ frame hframe nablaRic₁)
    (h₂ : ChristoffelEvolutionEquationInFrameOn
      (I := I) S₂ gInv₂ frame hframe nablaRic₂) :
    ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M), x ∈ u →
      ∀ i j k : Idx,
        HasDerivWithinAt
          (fun s : Real =>
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (S₁.family.connection s) frame hframe x i j k -
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (S₂.family.connection s) frame hframe x i j k)
          (christoffelEvolutionRHSInFrame (M := M) gInv₁ nablaRic₁ (t : Real) x i j k -
            christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ (t : Real) x i j k)
          D.carrier
          (t : Real) := by
  intro t x hx i j k
  exact (h₁ t x hx i j k).sub (h₂ t x hx i j k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionDiffInFrameOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionDiffInFrameOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionDiffInFrameOn ``Submission.DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionDiffInFrameOn

omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem christoffelDiff_coeff
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S₁ S₂ : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (s : Real) (x : M) (i j k : Idx) :
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S₁.family.connection s) frame hframe x i j k -
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S₂.family.connection s) frame hframe x i j k =
    hframe.coeff k x
      ((S₁.family.connection s (frame j) x) (frame i x) -
        (S₂.family.connection s (frame j) x) (frame i x)) := by
  simp [DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame, map_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.christoffelDiff_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.christoffelDiff_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.christoffelDiff_coeff ``Submission.DifferentialGeometry.PDE.RicciFlow.christoffelDiff_coeff

end Components

end DifferentialGeometry.PDE.RicciFlow

end
