import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.InteriorSmoothBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.I_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.I_half target :: scope.openDecls } }

variable [T2Space M] [CompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

abbrev SmoothScalarDirichlet (g : SmoothRiemannianMetric (I_half n) M) :=
  InteriorSmoothScalar g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.SmoothScalarDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.SmoothScalarDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.SmoothScalarDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.SmoothScalarDirichlet

abbrev H1ComplDirichlet (g : SmoothRiemannianMetric (I_half n) M) :=
  H1ComplInterior g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichlet

theorem H1ComplDirichlet_eq_completion (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplDirichlet g = UniformSpace.Completion (SmoothScalarDirichlet g) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichlet_eq_completion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichlet_eq_completion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichlet_eq_completion ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichlet_eq_completion

noncomputable def smoothToH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    SmoothScalarDirichlet g →L[ℝ] H1ComplDirichlet g :=
  smoothToH1ComplInterior g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToH1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToH1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToH1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToH1ComplDirichlet

theorem denseRange_smoothToH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (smoothToH1ComplDirichlet g) := by
  change DenseRange (UniformSpace.Completion.toComplL :
      SmoothScalarDirichlet g →L[ℝ] H1ComplDirichlet g)
  rw [show (UniformSpace.Completion.toComplL :
      SmoothScalarDirichlet g → H1ComplDirichlet g) =
      ((↑) : SmoothScalarDirichlet g →
        UniformSpace.Completion (SmoothScalarDirichlet g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_smoothToH1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_smoothToH1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_smoothToH1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_smoothToH1ComplDirichlet

noncomputable def smoothToLpDirichlet (g : SmoothRiemannianMetric (I_half n) M) :
    SmoothScalarDirichlet g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  smoothToLpInterior g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToLpDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToLpDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToLpDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToLpDirichlet

noncomputable def H1ComplDirichletToLp (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplDirichlet g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  H1ComplInteriorToLp g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichletToLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichletToLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichletToLp ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichletToLp

@[simp] lemma H1ComplDirichletToLp_smoothToH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : SmoothScalarDirichlet g) :
    H1ComplDirichletToLp g (smoothToH1ComplDirichlet g f) =
      smoothToLpDirichlet g f :=
  H1ComplInteriorToLp_smoothToH1ComplInterior g f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichletToLp_smoothToH1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichletToLp_smoothToH1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichletToLp_smoothToH1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichletToLp_smoothToH1ComplDirichlet

noncomputable def resolventDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplDirichlet g :=
  resolventInterior g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet

theorem resolventDirichlet_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (v : H1ComplDirichlet g) :
    ⟪resolventDirichlet g f, v⟫_ℝ = ⟪H1ComplDirichletToLp g v, f⟫_ℝ :=
  resolventInterior_inner_eq_lpFunctional g f v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet_inner_eq_lpFunctional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet_inner_eq_lpFunctional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet_inner_eq_lpFunctional ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet_inner_eq_lpFunctional

theorem smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : SmoothScalarDirichlet g) :
    smoothToH1ComplDirichlet g u = resolventDirichlet g u.oneSubLapClassicalLp :=
  smoothToH1ComplInterior_eq_resolventInterior_oneSubLap u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap

theorem denseRange_resolventDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (resolventDirichlet g) := by
  apply Dense.mono _ (denseRange_smoothToH1ComplDirichlet g)
  rintro _ ⟨u, rfl⟩
  exact ⟨u.oneSubLapClassicalLp,
    smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap u |>.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_resolventDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_resolventDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_resolventDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_resolventDirichlet

theorem H1ComplDirichletToLp_injective
    (g : SmoothRiemannianMetric (I_half n) M) :
    Function.Injective (H1ComplDirichletToLp g) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  apply (denseRange_resolventDirichlet g).eq_zero_of_inner_right ℝ
  intro f
  have h := resolventDirichlet_inner_eq_lpFunctional g f v
  rw [hv, inner_zero_left] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichletToLp_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichletToLp_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichletToLp_injective ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.H1ComplDirichletToLp_injective

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
