import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Preparation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

omit [TopologicalSpace Q] in
theorem initialRamp_projection_lift (γ : Surgery.Topology.Circle → Q) (x t : ℝ) :
    (initialRamp γ).projection.lift x t = γ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_projection_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_projection_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_projection_lift ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_projection_lift

omit [TopologicalSpace Q] in
theorem initialRamp_y (γ : Surgery.Topology.Circle → Q) (x t : ℝ) :
    (initialRamp γ).y x t = x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_y then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_y"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_y ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_y

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ Q] in
theorem initialRamp_X_snd (γ : Surgery.Topology.Circle → Q) (x t : ℝ) :
    ((initialRamp γ).X (I := I) x t).2 = 1 := by
  simp only [ProductCurve.X, initialRamp_y, deriv_id'']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_X_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_X_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_X_snd ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_X_snd

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ Q] in
theorem initialRamp_immersedOn (γ : Surgery.Topology.Circle → Q) :
    (initialRamp γ).ImmersedOn (I := I) (_root_.Set.univ : Set ℝ) := by
  intro x t _ h
  have h2 : ((initialRamp γ).X (I := I) x t).2 = (0 : ℝ) := by
    rw [h]; rfl
  rw [initialRamp_X_snd] at h2
  exact one_ne_zero h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_immersedOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_immersedOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_immersedOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_immersedOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem initialRamp_speed_pos (g : SmoothRiemannianMetric I Q) {lambda : ℝ}
    (hlambda : 0 < lambda) (γ : Surgery.Topology.Circle → Q) (x t : ℝ) :
    0 < (initialRamp γ).speed (fun _ : ℝ => g) lambda x t := by
  rw [ProductCurve.speed, ProductCurve.inner]
  refine Real.sqrt_pos.2 ?_
  have hX2 : ((initialRamp γ).X (I := I) x t).2 = 1 := initialRamp_X_snd γ x t
  have h1 : 0 ≤ g.inner ((initialRamp γ).projection.lift x t)
      ((initialRamp γ).X (I := I) x t).1 ((initialRamp γ).X (I := I) x t).1 :=
    metric_inner_self_nonneg g _ _
  have h2 : 0 < lambda ^ 2 * ((initialRamp γ).X (I := I) x t).2 *
      ((initialRamp γ).X (I := I) x t).2 := by
    rw [hX2]
    positivity
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_speed_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_speed_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_speed_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_speed_pos

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem initialRamp_angle (g : SmoothRiemannianMetric I Q) {lambda : ℝ}
    (hlambda : 0 < lambda) (γ : Surgery.Topology.Circle → Q) (x t : ℝ) :
    (initialRamp γ).angle (fun _ : ℝ => g) lambda x t =
      lambda * ((initialRamp γ).speed (fun _ : ℝ => g) lambda x t)⁻¹ := by
  have hX2 : ((initialRamp γ).X (I := I) x t).2 = 1 := initialRamp_X_snd γ x t
  rw [ProductCurve.angle, ProductCurve.unitTangent, ProductCurve.verticalUnit,
    ProductCurve.inner]
  simp only [Prod.smul_fst, Prod.smul_snd, hX2, mul_one, smul_eq_mul,
    ContinuousLinearMap.map_zero, zero_add]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_angle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_angle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_angle ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_angle

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem initialRamp_angle_pos (g : SmoothRiemannianMetric I Q) {lambda : ℝ}
    (hlambda : 0 < lambda) (γ : Surgery.Topology.Circle → Q) (x t : ℝ) :
    0 < (initialRamp γ).angle (fun _ : ℝ => g) lambda x t := by
  rw [initialRamp_angle g hlambda γ x t]
  exact mul_pos hlambda (inv_pos.mpr (initialRamp_speed_pos g hlambda γ x t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_angle_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_angle_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_angle_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_angle_pos

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem initialRamp_isRampOn (g : SmoothRiemannianMetric I Q) {lambda : ℝ}
    (hlambda : 0 < lambda) (γ : Surgery.Topology.Circle → Q) :
    (initialRamp γ).IsRampOn (fun _ : ℝ => g) lambda (_root_.Set.univ : Set ℝ) :=
  ⟨fun x t _ => initialRamp_immersedOn γ x t trivial,
    fun x t _ => initialRamp_angle_pos g hlambda γ x t⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_isRampOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_isRampOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_isRampOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_isRampOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ Q] in
theorem initialRamp_smoothOn {γ : Surgery.Topology.Circle → Q}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => γ (t : Surgery.Topology.Circle))) :
    (initialRamp γ).SmoothOn (I := I) (_root_.Set.univ : Set ℝ) := by
  refine ⟨?_, ?_⟩
  · change ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ (p.1 : Surgery.Topology.Circle)) (_root_.Set.univ ×ˢ (_root_.Set.univ : Set ℝ))
    have hfst : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × ℝ => p.1) :=
      contMDiff_iff_contDiff.mpr contDiff_fst
    have hcomp : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞
        ((fun t : ℝ => γ (t : Surgery.Topology.Circle)) ∘ fun p : ℝ × ℝ => p.1) :=
      hγ.comp hfst
    simpa only [Set.univ_prod_univ, Function.comp_def] using hcomp.contMDiffOn
  · change ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.1) (_root_.Set.univ ×ˢ (_root_.Set.univ : Set ℝ))
    simpa only [Set.univ_prod_univ] using
      (contDiff_fst : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1)).contDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_smoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_smoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_smoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_smoothOn

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
