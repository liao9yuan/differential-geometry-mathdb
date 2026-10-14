import Submission.DifferentialGeometry.Analysis.Spectral.Scalar.Enumeration

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

theorem exists_pos_le_nonzeroLaplacianEigenvalueSet
    (g : SmoothRiemannianMetric I M) :
    ∃ c : ℝ, 0 < c ∧
      ∀ lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g, c ≤ lam := by
  by_cases hne : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Nonempty
  · by_cases hinf : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Infinite
    · refine ⟨laplacianEigenvalueAscending (I := I) (M := M) g 0, ?_, ?_⟩
      · exact nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g
          (laplacianEigenvalueAscending_mem_of_infinite (I := I) (M := M) g hinf 0)
      · intro lam hlam
        rw [laplacianEigenvalueAscending_zero_eq_sInf (I := I) (M := M) g hne]
        exact csInf_le
          ⟨0, fun x hx => (nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g hx).le⟩ hlam
    · have hfin : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Finite := by
        simpa using hinf
      have hfinne : hfin.toFinset.Nonempty := by
        rwa [Set.Finite.toFinset_nonempty]
      refine ⟨hfin.toFinset.min' hfinne, ?_, ?_⟩
      · have hmem : hfin.toFinset.min' hfinne ∈
            nonzeroLaplacianEigenvalueSet (I := I) (M := M) g := by
          rw [← Set.Finite.mem_toFinset]
          exact Finset.min'_mem _ _
        exact nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g hmem
      · intro lam hlam
        exact Finset.min'_le _ _ (by rwa [Set.Finite.mem_toFinset])
  · exact ⟨1, one_pos, fun lam hlam => absurd ⟨lam, hlam⟩ hne⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.exists_pos_le_nonzeroLaplacianEigenvalueSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.exists_pos_le_nonzeroLaplacianEigenvalueSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.exists_pos_le_nonzeroLaplacianEigenvalueSet ``Submission.DifferentialGeometry.Analysis.Laplacian.exists_pos_le_nonzeroLaplacianEigenvalueSet

end Laplacian
end Analysis
end DifferentialGeometry

end
