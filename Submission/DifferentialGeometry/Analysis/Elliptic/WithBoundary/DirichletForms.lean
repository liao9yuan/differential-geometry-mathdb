import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1Compl
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Gradient
import Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.GradientContinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem (tangentSectionAction)
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Operator

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

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }

def dirichletMass
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) : ℝ :=
  ∫ x, u.toFun x * v.toFun x
    ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass

theorem dirichletMass_integrable
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) :
    _root_.MeasureTheory.Integrable (fun x : M => u.toFun x * v.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
  let _ : _root_.MeasureTheory.IsFiniteMeasure
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) h
  exact (u.smooth.continuous.mul v.smooth.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_integrable ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_integrable

theorem dirichletMass_add_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u₁ u₂ v : SmoothScalarDirichlet q) :
    dirichletMass h (u₁ + u₂) v =
      dirichletMass h u₁ v + dirichletMass h u₂ v := by
  unfold dirichletMass
  simp only [InteriorSmoothScalar.toFun_add_apply, add_mul]
  exact _root_.MeasureTheory.integral_add (dirichletMass_integrable h u₁ v)
    (dirichletMass_integrable h u₂ v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_add_left ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_add_left

theorem dirichletMass_smul_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletMass h (c • u) v = c * dirichletMass h u v := by
  unfold dirichletMass
  simp only [InteriorSmoothScalar.toFun_smul_apply, mul_assoc, _root_.MeasureTheory.integral_const_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_smul_left ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_smul_left

theorem dirichletMass_symm
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) :
    dirichletMass h u v = dirichletMass h v u := by
  unfold dirichletMass
  refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact mul_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_symm ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_symm

theorem dirichletMass_add_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v₁ v₂ : SmoothScalarDirichlet q) :
    dirichletMass h u (v₁ + v₂) =
      dirichletMass h u v₁ + dirichletMass h u v₂ := by
  rw [dirichletMass_symm, dirichletMass_add_left,
    dirichletMass_symm h v₁ u, dirichletMass_symm h v₂ u]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_add_right ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_add_right

theorem dirichletMass_smul_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletMass h u (c • v) = c * dirichletMass h u v := by
  rw [dirichletMass_symm, dirichletMass_smul_left,
    dirichletMass_symm h v u]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_smul_right ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_smul_right

def dirichletEnergy
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) : ℝ :=
  ∫ x, h.inner x
      (gradFun (I := I_half n) h u.toFun x)
      (gradFun (I := I_half n) h v.toFun x)
    ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy

theorem dirichletEnergy_integrable
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) :
    _root_.MeasureTheory.Integrable (fun x : M => h.inner x
        (gradFun (I := I_half n) h u.toFun x)
        (gradFun (I := I_half n) h v.toFun x))
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
  let gu := DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection
    (I := I_half n) h u.smooth u.interior_support
  let gv := DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection
    (I := I_half n) h v.smooth v.interior_support
  have hcont : Continuous (fun x : M => h.inner x (gu x) (gv x)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections (I := I_half n) h gu gv
  let _ : _root_.MeasureTheory.IsFiniteMeasure
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) h
  simpa only [gu, gv,
    DifferentialGeometry.Geometry.Operator.WithBoundary.grad_g_with_boundary_section_apply] using
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_integrable ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_integrable

theorem dirichletEnergy_add_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u₁ u₂ v : SmoothScalarDirichlet q) :
    dirichletEnergy h (u₁ + u₂) v =
      dirichletEnergy h u₁ v + dirichletEnergy h u₂ v := by
  unfold dirichletEnergy
  have hgrad : ∀ x : M,
      gradFun (I := I_half n) h (u₁ + u₂).toFun x =
        gradFun (I := I_half n) h u₁.toFun x +
          gradFun (I := I_half n) h u₂.toFun x := by
    intro x
    exact gradFun_add (I := I_half n) h
      (u₁.smooth.mdifferentiable (by simp) x)
      (u₂.smooth.mdifferentiable (by simp) x)
  simp_rw [hgrad, map_add]
  exact _root_.MeasureTheory.integral_add (dirichletEnergy_integrable h u₁ v)
    (dirichletEnergy_integrable h u₂ v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_add_left ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_add_left

theorem dirichletEnergy_smul_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletEnergy h (c • u) v = c * dirichletEnergy h u v := by
  unfold dirichletEnergy
  have hgrad : ∀ x : M,
      gradFun (I := I_half n) h (c • u).toFun x =
        c • gradFun (I := I_half n) h u.toFun x := by
    intro x
    change gradFun (I := I_half n) h (c • u.toFun) x =
      c • gradFun (I := I_half n) h u.toFun x
    exact DifferentialGeometry.Geometry.Connection.gradFun_const_smul
      (I := I_half n) h c (u.smooth.mdifferentiable (by simp) x)
  simp_rw [hgrad, map_smul]
  exact _root_.MeasureTheory.integral_const_mul c _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_smul_left ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_smul_left

theorem dirichletEnergy_symm
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) :
    dirichletEnergy h u v = dirichletEnergy h v u := by
  unfold dirichletEnergy
  refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact h.symm x _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_symm ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_symm

theorem dirichletEnergy_add_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v₁ v₂ : SmoothScalarDirichlet q) :
    dirichletEnergy h u (v₁ + v₂) =
      dirichletEnergy h u v₁ + dirichletEnergy h u v₂ := by
  rw [dirichletEnergy_symm, dirichletEnergy_add_left,
    dirichletEnergy_symm h v₁ u, dirichletEnergy_symm h v₂ u]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_add_right ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_add_right

theorem dirichletEnergy_smul_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletEnergy h u (c • v) = c * dirichletEnergy h u v := by
  rw [dirichletEnergy_symm, dirichletEnergy_smul_left,
    dirichletEnergy_symm h v u]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_smul_right ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_smul_right

theorem dirichletEnergy_self_nonneg
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) :
    0 ≤ dirichletEnergy h u u := by
  unfold dirichletEnergy
  exact _root_.MeasureTheory.integral_nonneg fun x =>
    SmoothRiemannianMetric_inner_self_nonneg h x _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_self_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletEnergy_self_nonneg

def dirichletDrift
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (u v : SmoothScalarDirichlet q) : ℝ :=
  ∫ x, h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) * v.toFun x
    ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift

theorem dirichletDrift_integrable
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (u v : SmoothScalarDirichlet q) :
    _root_.MeasureTheory.Integrable (fun x : M =>
      h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) * v.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
  let gu := DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection
    (I := I_half n) h u.smooth u.interior_support
  have hinner : Continuous (fun x : M => h.inner x (X x) (gu x)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections (I := I_half n) h X gu
  let _ : _root_.MeasureTheory.IsFiniteMeasure
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) h
  have hint := (hinner.mul v.smooth.continuous).integrable_of_hasCompactSupport
    (μ := riemannianVolumeMeasure (I := I_half n) (M := M) h)
    (HasCompactSupport.of_compactSpace _)
  refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [gu, Pi.mul_apply,
    DifferentialGeometry.Geometry.Operator.WithBoundary.grad_g_with_boundary_section_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_integrable ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_integrable

theorem dirichletDrift_add_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (u₁ u₂ v : SmoothScalarDirichlet q) :
    dirichletDrift h X (u₁ + u₂) v =
      dirichletDrift h X u₁ v + dirichletDrift h X u₂ v := by
  unfold dirichletDrift
  have hgrad : ∀ x : M,
      gradFun (I := I_half n) h (u₁ + u₂).toFun x =
        gradFun (I := I_half n) h u₁.toFun x +
          gradFun (I := I_half n) h u₂.toFun x := by
    intro x
    exact gradFun_add (I := I_half n) h
      (u₁.smooth.mdifferentiable (by simp) x)
      (u₂.smooth.mdifferentiable (by simp) x)
  simp_rw [hgrad, map_add, add_mul]
  exact _root_.MeasureTheory.integral_add (dirichletDrift_integrable h X u₁ v)
    (dirichletDrift_integrable h X u₂ v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_add_left ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_add_left

theorem dirichletDrift_smul_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletDrift h X (c • u) v = c * dirichletDrift h X u v := by
  unfold dirichletDrift
  have hgrad : ∀ x : M,
      gradFun (I := I_half n) h (c • u).toFun x =
        c • gradFun (I := I_half n) h u.toFun x := by
    intro x
    change gradFun (I := I_half n) h (c • u.toFun) x =
      c • gradFun (I := I_half n) h u.toFun x
    exact DifferentialGeometry.Geometry.Connection.gradFun_const_smul
      (I := I_half n) h c (u.smooth.mdifferentiable (by simp) x)
  rw [show (fun x : M =>
      h.inner x (X x) (gradFun (I := I_half n) h (c • u).toFun x) * v.toFun x) =
      fun x => c *
        (h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) * v.toFun x) by
    funext x
    rw [hgrad, map_smul, smul_eq_mul]
    ring]
  exact _root_.MeasureTheory.integral_const_mul c _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_smul_left ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_smul_left

theorem dirichletDrift_add_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (u v₁ v₂ : SmoothScalarDirichlet q) :
    dirichletDrift h X u (v₁ + v₂) =
      dirichletDrift h X u v₁ + dirichletDrift h X u v₂ := by
  unfold dirichletDrift
  simp only [InteriorSmoothScalar.toFun_add_apply, mul_add]
  exact _root_.MeasureTheory.integral_add (dirichletDrift_integrable h X u v₁)
    (dirichletDrift_integrable h X u v₂)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_add_right ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_add_right

theorem dirichletDrift_smul_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletDrift h X u (c • v) = c * dirichletDrift h X u v := by
  unfold dirichletDrift
  rw [show (fun x : M => h.inner x (X x)
      (gradFun (I := I_half n) h u.toFun x) * (c • v).toFun x) =
      fun x => c *
        (h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) * v.toFun x) by
    funext x
    rw [InteriorSmoothScalar.toFun_smul_apply]
    ring]
  exact _root_.MeasureTheory.integral_const_mul c _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_smul_right ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletDrift_smul_right

def dirichletWeakForm
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ) (u v : SmoothScalarDirichlet q) : ℝ :=
  -dirichletEnergy h u v + dirichletDrift h X u v - a * dirichletMass h u v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm

theorem dirichletWeakForm_add_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ) (u₁ u₂ v : SmoothScalarDirichlet q) :
    dirichletWeakForm h X a (u₁ + u₂) v =
      dirichletWeakForm h X a u₁ v + dirichletWeakForm h X a u₂ v := by
  unfold dirichletWeakForm
  rw [dirichletEnergy_add_left, dirichletDrift_add_left, dirichletMass_add_left]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_add_left ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_add_left

theorem dirichletWeakForm_smul_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletWeakForm h X a (c • u) v = c * dirichletWeakForm h X a u v := by
  unfold dirichletWeakForm
  rw [dirichletEnergy_smul_left, dirichletDrift_smul_left,
    dirichletMass_smul_left]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_smul_left ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_smul_left

theorem dirichletWeakForm_add_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ) (u v₁ v₂ : SmoothScalarDirichlet q) :
    dirichletWeakForm h X a u (v₁ + v₂) =
      dirichletWeakForm h X a u v₁ + dirichletWeakForm h X a u v₂ := by
  unfold dirichletWeakForm
  rw [dirichletEnergy_add_right, dirichletDrift_add_right, dirichletMass_add_right]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_add_right ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_add_right

theorem dirichletWeakForm_smul_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletWeakForm h X a u (c • v) = c * dirichletWeakForm h X a u v := by
  unfold dirichletWeakForm
  rw [dirichletEnergy_smul_right, dirichletDrift_smul_right,
    dirichletMass_smul_right]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_smul_right ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletWeakForm_smul_right

theorem dirichletMass_self_nonneg
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) :
    0 ≤ dirichletMass h u u := by
  unfold dirichletMass
  exact _root_.MeasureTheory.integral_nonneg fun x => mul_self_nonneg (u.toFun x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_self_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletMass_self_nonneg

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
