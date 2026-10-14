import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSeparability
import Submission.DifferentialGeometry.Analysis.InnerProductSpace.WeakCompactness
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Measure.SeparableMeasure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ContDiff _root_.ENNReal _root_.InnerProductSpace _root_.Manifold _root_.NNReal
  RealInnerProductSpace Topology

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.I_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.I_half target :: scope.openDecls } }

theorem exists_weakly_convergent_subsequence_timeL2_H1ComplDirichlet
    (q : SmoothRiemannianMetric (I_half n) M) {T C : ℝ}
    (U : ℕ → timeL2 (H1ComplDirichlet q) T)
    (hU : ∀ m, ‖U m‖ ≤ C) :
    ∃ φ : ℕ → ℕ, ∃ u : timeL2 (H1ComplDirichlet q) T,
      StrictMono φ ∧
        ∀ z, _root_.Filter.Tendsto (fun m => _root_.Inner.inner ℝ (U (φ m)) z) _root_.Filter.atTop
          (𝓝 (_root_.Inner.inner ℝ u z)) := by
  let _ : SecondCountableTopology (H1ComplDirichlet q) :=
    UniformSpace.secondCountable_of_separable _
  let _ : _root_.MeasureTheory.IsSeparable (timeMeasure T) := inferInstance
  let _ : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let _ : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  let _ : SecondCountableTopology (timeL2 (H1ComplDirichlet q) T) :=
    Lp.SecondCountableTopology
  let _ : TopologicalSpace.SeparableSpace
      (timeL2 (H1ComplDirichlet q) T) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  exact DifferentialGeometry.Analysis.InnerProductSpace.exists_weakly_convergent_subsequence_of_norm_bounded
    U hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_weakly_convergent_subsequence_timeL2_H1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_weakly_convergent_subsequence_timeL2_H1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_weakly_convergent_subsequence_timeL2_H1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_weakly_convergent_subsequence_timeL2_H1ComplDirichlet

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
