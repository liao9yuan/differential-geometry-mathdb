import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothBasis

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.InnerProductSpace _root_.Manifold
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.I_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.I_half target :: scope.openDecls } }

noncomputable instance instSeparableSpaceH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    TopologicalSpace.SeparableSpace (H1ComplDirichlet g) := by
  let b := smoothDirichletHilbertBasis g
  have hrange : TopologicalSpace.IsSeparable (Set.range b) :=
    Set.countable_range b |>.isSeparable
  have hspan : TopologicalSpace.IsSeparable
      (Submodule.span ℝ (Set.range b) : Set
        (_root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) :=
    hrange.span
  have hclosure : closure (Submodule.span ℝ (Set.range b) : Set
      (_root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) = Set.univ := by
    change closure (Submodule.span ℝ (Set.range b) : Set
      (_root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) =
        (↑(⊤ : Submodule ℝ
          (_root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) : Set _)
    simpa only [Submodule.topologicalClosure_coe] using
      congrArg SetLike.coe b.dense_span
  let _ : TopologicalSpace.SeparableSpace
      (_root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :=
    TopologicalSpace.isSeparable_univ_iff.mp (by
      rw [← hclosure]
      exact hspan.closure)
  exact (denseRange_resolventDirichlet g).separableSpace
    (resolventDirichlet g).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instSeparableSpaceH1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instSeparableSpaceH1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instSeparableSpaceH1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instSeparableSpaceH1ComplDirichlet

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

end
