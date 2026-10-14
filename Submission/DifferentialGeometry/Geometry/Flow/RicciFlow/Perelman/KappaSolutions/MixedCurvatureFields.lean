import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.TimeJetFields

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance mixedFieldC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedFieldC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedFieldC1 target :: scope.openDecls } }
private local instance mixedFieldC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedFieldC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedFieldC2 target :: scope.openDecls } }


theorem exists_closedWindow_mixed_curvature_fields
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Set.Icc a b) (hregular : Set.Ioo a b ⊆ D.regular) (p : ℕ) :
    ∃ A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) (4 + p),
      ∀ q : ℕ, ∀ t : ℝ, t ∈ Set.Icc c b → ∀ x : M,
        A q t x = mixedCurvatureTensor S p q t x ∧
        HasDerivWithinAt (fun s => A q s x)
          (A (q + 1) t x - covariantEndomorphismAction0S (A q t x)
            (ricciSharp (S.base.metric t) x)) (Set.Icc c b) t := by
  exact exists_mixed_curvature_fields_on_closed_interval S hS hac hcb hcarrier hregular p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_closedWindow_mixed_curvature_fields then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_closedWindow_mixed_curvature_fields"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_closedWindow_mixed_curvature_fields ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_closedWindow_mixed_curvature_fields

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
