import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.InitialVector.VariableEndpoint

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
theorem isBounded_range_initialVector_of_lRegularizedAction_le_fixed_parameter
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z : Nat → TangentSpace I x) (B A : Real) (hB : 0 < B)
    (hslab : Set.Icc (T - B ^ 2) T ⊆ D.regular)
    (hdom : ∀ n, B ∈ lRegularizedDomain S T x (Z n))
    (hact : ∀ n,
      lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 B ≤ A) :
    Bornology.IsBounded (Set.range Z) := by
  exact isBounded_range_initialVector_of_lRegularizedAction_le
    (I := I) S hS T x Z (fun _ ↦ B) B B A hB
      (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) hslab hdom hact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.isBounded_range_initialVector_of_lRegularizedAction_le_fixed_parameter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.isBounded_range_initialVector_of_lRegularizedAction_le_fixed_parameter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.isBounded_range_initialVector_of_lRegularizedAction_le_fixed_parameter ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.isBounded_range_initialVector_of_lRegularizedAction_le_fixed_parameter

end DifferentialGeometry.PDE.RicciFlow.Perelman
