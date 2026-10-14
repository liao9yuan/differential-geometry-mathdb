import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {M : Type*}

def toProductCurve (c : CurveMap M) : ProductCurve M where
  map x t := (c x t, 0)
  y _ _ := 0
  degree := 0
  lift_eq _ _ := by simp
  increment _ _ := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve

@[simp] theorem toProductCurve_projection (c : CurveMap M) : c.toProductCurve.projection = c := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_projection ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_projection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def toProductField (c : CurveMap M) (V : c.Field (I := I)) : c.toProductCurve.Field (I := I) :=
  fun x t => (V x t, 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductField ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductField

omit [IsManifold I ∞ M] in
@[simp] theorem toProductCurve_X (c : CurveMap M) :
    c.toProductCurve.X (I := I) = c.toProductField c.X := by
  funext x t
  change (c.X (I := I) x t, deriv (fun _ : ℝ => (0 : ℝ)) x) = (c.X (I := I) x t, 0)
  rw [deriv_const]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_X then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_X"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_X ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_X

omit [IsManifold I ∞ M] in
@[simp] theorem toProductCurve_velocity (c : CurveMap M) (J : Set ℝ) :
    c.toProductCurve.velocity (I := I) J = c.toProductField (c.velocity J) := by
  funext x t
  change (c.velocity (I := I) J x t, derivWithin (Function.const ℝ (0 : ℝ)) J t) =
    (c.velocity (I := I) J x t, 0)
  rw [derivWithin_const]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_velocity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_velocity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_velocity ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_velocity

@[simp] theorem toProductCurve_speed (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda x t : ℝ) : c.toProductCurve.speed g lambda x t = c.speed g x t := by
  simp only [ProductCurve.speed, toProductCurve_X, ProductCurve.inner, toProductField,
    toProductCurve_projection, _root_.MulZeroClass.mul_zero, add_zero, speed]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_speed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_speed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_speed ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_speed

@[simp] theorem toProductCurve_unitTangent (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) : c.toProductCurve.unitTangent g lambda = c.toProductField (c.unitTangent g) := by
  funext x t
  simp only [ProductCurve.unitTangent, toProductCurve_speed, toProductCurve_X, toProductField,
    unitTangent]
  apply Prod.ext
  · rfl
  · exact smul_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_unitTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_unitTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_unitTangent ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_unitTangent

variable [FiniteDimensional ℝ E]

@[simp] theorem toProductCurve_Ds (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (V : c.Field (I := I)) :
    c.toProductCurve.Ds g lambda (c.toProductField V) = c.toProductField (c.Ds g V) := by
  funext x t
  simp only [ProductCurve.Ds, toProductCurve_speed, ProductCurve.Dx, toProductField,
    toProductCurve_projection, deriv_const, Ds, Dx]
  apply Prod.ext
  · rfl
  · exact smul_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_Ds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_Ds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_Ds ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_Ds

@[simp] theorem toProductCurve_curvatureVector (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) : c.toProductCurve.curvatureVector g lambda = c.toProductField (c.curvatureVector g) := by
  rw [ProductCurve.curvatureVector, toProductCurve_unitTangent, toProductCurve_Ds]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_curvatureVector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_curvatureVector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_curvatureVector ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_curvatureVector

@[simp] theorem toProductCurve_iteratedDs (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (m : ℕ) (V : c.Field (I := I)) :
    c.toProductCurve.iteratedDs g lambda m (c.toProductField V) = c.toProductField (c.iteratedDs g m V) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [ProductCurve.iteratedDs, iteratedDs, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, toProductCurve_Ds]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_iteratedDs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_iteratedDs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_iteratedDs ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_iteratedDs

omit [FiniteDimensional ℝ E] in
@[simp] theorem toProductCurve_normSq (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (V : c.Field (I := I)) (x t : ℝ) :
    c.toProductCurve.normSq g lambda (c.toProductField V) x t = c.normSq g V x t := by
  simp only [ProductCurve.normSq, ProductCurve.inner, toProductCurve_projection, toProductField,
    _root_.MulZeroClass.mul_zero, add_zero, normSq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_normSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_normSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_normSq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_normSq

@[simp] theorem toProductCurve_curvatureSq (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda x t : ℝ) : c.toProductCurve.curvatureSq g lambda x t = c.curvatureSq g x t := by
  rw [ProductCurve.curvatureSq, toProductCurve_curvatureVector, toProductCurve_normSq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_curvatureSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_curvatureSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_curvatureSq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_curvatureSq

@[simp] theorem toProductCurve_curvature (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda x t : ℝ) : c.toProductCurve.curvature g lambda x t = c.curvature g x t := by
  simp only [ProductCurve.curvature, toProductCurve_curvatureSq, curvature]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_curvature

omit [FiniteDimensional ℝ E] in
@[simp] theorem toProductCurve_length (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda t : ℝ) : c.toProductCurve.length g lambda t = c.length g t := by
  simp only [ProductCurve.length, ProductCurve.integral, toProductCurve_speed, length, integral]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_length ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_length

@[simp] theorem toProductCurve_totalCurvature (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda t : ℝ) : c.toProductCurve.totalCurvature g lambda t = c.totalCurvature g t := by
  simp only [ProductCurve.totalCurvature, ProductCurve.integral, toProductCurve_speed,
    toProductCurve_curvature, totalCurvature, integral]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_totalCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_totalCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_totalCurvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_totalCurvature

omit [FiniteDimensional ℝ E] in
@[simp] theorem toProductCurve_arcLength (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda p q t : ℝ) : c.toProductCurve.arcLength g lambda p q t = c.arcLength g p q t := by
  simp only [ProductCurve.arcLength, toProductCurve_speed, arcLength]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_arcLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_arcLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_arcLength ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_arcLength

@[simp] theorem toProductCurve_arcTotalCurvature (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda p q t : ℝ) : c.toProductCurve.arcTotalCurvature g lambda p q t = c.arcTotalCurvature g p q t := by
  simp only [ProductCurve.arcTotalCurvature, toProductCurve_speed, toProductCurve_curvature, arcTotalCurvature]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_arcTotalCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_arcTotalCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_arcTotalCurvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_arcTotalCurvature

@[simp] theorem toProductCurve_isSolutionOn_iff (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (J : Set ℝ) : c.toProductCurve.IsSolutionOn g lambda J ↔ c.IsSolutionOn g J := by
  constructor
  · intro hc
    refine ⟨hc.smooth.1, ?_, ?_⟩
    · intro x t ht heq
      apply hc.immersed x t ht
      rw [toProductCurve_X]
      change (c.X (I := I) x t, (0 : ℝ)) = (0, 0)
      rw [heq]
    · intro x t ht
      have hh := congrArg Prod.fst (hc.equation x t ht)
      change (c.toProductCurve.velocity (I := I) J x t).1 =
        (c.toProductCurve.curvatureVector g lambda x t).1 at hh
      rw [toProductCurve_velocity, toProductCurve_curvatureVector] at hh
      exact hh
  · intro hc
    refine ⟨⟨hc.smooth, contDiffOn_const⟩, ?_, ?_⟩
    · intro x t ht heq
      apply hc.immersed x t ht
      have hh := congrArg Prod.fst heq
      rw [toProductCurve_X] at hh
      exact hh
    · intro x t ht
      simp only [toProductCurve_velocity, toProductCurve_curvatureVector, toProductField, hc.equation x t ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_isSolutionOn_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_isSolutionOn_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_isSolutionOn_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.toProductCurve_isSolutionOn_iff

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
