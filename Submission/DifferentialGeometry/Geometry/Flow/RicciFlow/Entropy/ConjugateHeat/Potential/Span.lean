import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.Potential.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
theorem conjA1_on
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    {h : Real}
    (hreg : ∀ s ∈ Set.Icc (0 : Real) h, (T : Real) - s ∈ D.regular) :
    ∃ C1 : NNReal,
      ContinuousOn (fun s : Real ↦ conjA1 (I := I) (M := M) S T s)
        (Set.Icc (0 : Real) h) ∧
      ∀ s ∈ Set.Icc (0 : Real) h,
        ‖conjA1 (I := I) (M := M) S T s‖ ≤ (C1 : Real) := by
  let : SeminormedAddCommGroup
      (TensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 1 →L[Real]
        TensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 0) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  have hcont : ContinuousOn
      (fun s : Real ↦ conjA1 (I := I) (M := M) S T s)
      (Set.Icc (0 : Real) h) :=
    conjA1_cont (I := I) (M := M) S hS T hreg
  have hnorm : ContinuousOn
      (fun s : Real ↦ ‖conjA1 (I := I) (M := M) S T s‖)
      (Set.Icc (0 : Real) h) :=
    continuous_norm.comp_continuousOn hcont
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hnorm
  let C1 : NNReal := ⟨max C 0, le_max_right _ _⟩
  refine ⟨C1, hcont, ?_⟩
  intro s hs
  change ‖conjA1 (I := I) (M := M) S T s‖ ≤ _root_.Max.max C 0
  exact (hC ⟨s, hs, rfl⟩).trans (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1_on ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1_on

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem conjCoeff_span
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : Real} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t ∈ Set.Icc a b, ∀ x : M,
        |(conjCoeff (I := I) (M := M) S t : M → Real) x| ≤ C := by
  let K : Set (Real × M) := Set.Icc a b ×ˢ (Set.univ : Set M)
  have hK : IsCompact K := by
    simpa only [K] using isCompact_Icc.prod (isCompact_univ (X := M))
  have hcont : ContinuousOn
      (fun p : Real × M =>
        |(conjCoeff (I := I) (M := M) S p.1 : M → Real) p.2|) K := by
    exact ((conjCoeff_joint (I := I) S hS).continuousOn.mono
      (Set.prod_mono hab Set.Subset.rfl)).abs
  obtain ⟨C, hC⟩ := hK.bddAbove_image hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x
  exact (hC ⟨(t, x), ⟨ht, Set.mem_univ x⟩, rfl⟩).trans
    (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_span then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_span"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_span ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_span

end DifferentialGeometry.PDE.RicciFlow.Entropy

end
