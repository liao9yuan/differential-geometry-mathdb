import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import Submission.DifferentialGeometry.Topology.Manifold.AddCircle
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Submission.DifferentialGeometry.Geometry.Metric.Scaling
import Submission.DifferentialGeometry.Geometry.Metric.Product
import Submission.DifferentialGeometry.Geometry.Metric.Euclidean
import Submission.DifferentialGeometry.Geometry.Metric.Quotient
import Submission.DifferentialGeometry.Topology.Manifold.OpenEmbedding
import Submission.DifferentialGeometry.Topology.Covering.AddCircleLift
import Submission.DifferentialGeometry.Geometry.Connection.ProductAlongCurveInterior
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeScaling
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Existence
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def productCoverProjection : C(M × ℝ, M × Surgery.Topology.Circle) :=
  ⟨fun p => (p.1, (p.2 : Surgery.Topology.Circle)), continuous_fst.prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.productCoverProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.productCoverProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.productCoverProjection ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.productCoverProjection

structure ProductCurve (M : Type*) where
  map : CurveMap (M × Surgery.Topology.Circle)
  y : ℝ → ℝ → ℝ
  degree : ℤ
  lift_eq : ∀ x t, (y x t : Surgery.Topology.Circle) = (map (x : Surgery.Topology.Circle) t).2
  increment : ∀ x t, y (x + 1) t = y x t + degree

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

namespace ProductCurve

variable (c : ProductCurve M)


def projection : CurveMap M := fun x t => (c.map x t).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection


def coverLift (x t : ℝ) : M × ℝ := (c.projection.lift x t, c.y x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.coverLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.coverLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.coverLift ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.coverLift

@[simp] theorem coverProjection_lift (x t : ℝ) :
    productCoverProjection (c.coverLift x t) = c.map (x : Surgery.Topology.Circle) t := by
  apply Prod.ext
  · rfl
  · exact c.lift_eq x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.coverProjection_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.coverProjection_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.coverProjection_lift ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.coverProjection_lift


abbrev Field := (x t : ℝ) → TangentSpace I (c.projection.lift x t) × ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Field ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Field


def inner (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (x t : ℝ)
    (v w : TangentSpace I (c.projection.lift x t) × ℝ) : ℝ :=
  (g t).inner (c.projection.lift x t) v.1 w.1 + lambda ^ 2 * v.2 * w.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.inner ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.inner

def X : c.Field (I := I) := fun x t =>
  (c.projection.X (I := I) x t, deriv (fun z => c.y z t) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.X then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.X"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.X ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.X

def velocity (J : Set ℝ) : c.Field (I := I) := fun x t =>
  (c.projection.velocity (I := I) J x t, derivWithin (c.y x) J t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.velocity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.velocity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.velocity ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.velocity

def speed (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (x t : ℝ) : ℝ :=
  Real.sqrt (c.inner g lambda x t (c.X x t) (c.X x t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed

def unitTangent (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) : c.Field (I := I) :=
  fun x t => (c.speed g lambda x t)⁻¹ • c.X x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.unitTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.unitTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.unitTangent ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.unitTangent


def Dx (g : ℝ → SmoothRiemannianMetric I M) (V : c.Field (I := I)) : c.Field (I := I) :=
  fun x t => (covDerivAlong (g t) (fun z => c.projection.lift z t)
      (fun z => (V z t).1) x, deriv (fun z => (V z t).2) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Dx then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Dx"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Dx ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Dx

def Ds (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (V : c.Field (I := I)) : c.Field (I := I) :=
  fun x t => (c.speed g lambda x t)⁻¹ • c.Dx g V x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Ds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Ds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Ds ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Ds

def curvatureVector (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) : c.Field (I := I) :=
  c.Ds g lambda (c.unitTangent g lambda)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureVector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureVector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureVector ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureVector

def normSq (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (V : c.Field (I := I)) (x t : ℝ) : ℝ := c.inner g lambda x t (V x t) (V x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.normSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.normSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.normSq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.normSq

def curvatureSq (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) : ℝ → ℝ → ℝ :=
  c.normSq g lambda (c.curvatureVector g lambda)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvatureSq

def curvature (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (x t : ℝ) : ℝ :=
  Real.sqrt (c.curvatureSq g lambda x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature

def iteratedDs (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (m : ℕ) (V : c.Field (I := I)) : c.Field (I := I) := (c.Ds g lambda)^[m] V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.iteratedDs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.iteratedDs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.iteratedDs ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.iteratedDs

def ds (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  (c.speed g lambda x t)⁻¹ * deriv (fun z => f z t) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.ds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.ds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.ds ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.ds

def integral (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (f : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, f x t * c.speed g lambda x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.integral ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.integral

def length (g : ℝ → SmoothRiemannianMetric I M) (lambda t : ℝ) : ℝ :=
  c.integral g lambda (fun _ _ => 1) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.length ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.length

def totalCurvature (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) : ℝ → ℝ :=
  c.integral g lambda (c.curvature g lambda)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.totalCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.totalCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.totalCurvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.totalCurvature

def energy (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) : ℝ → ℝ :=
  c.integral g lambda (c.curvatureSq g lambda)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.energy ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.energy

def arcLength (g : ℝ → SmoothRiemannianMetric I M) (lambda x₀ x₁ t : ℝ) : ℝ :=
  ∫ x in x₀..x₁, c.speed g lambda x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcLength ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcLength

def arcTotalCurvature (g : ℝ → SmoothRiemannianMetric I M) (lambda x₀ x₁ t : ℝ) : ℝ :=
  ∫ x in x₀..x₁, c.curvature g lambda x t * c.speed g lambda x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcTotalCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcTotalCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcTotalCurvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcTotalCurvature

def arcEnergy (g : ℝ → SmoothRiemannianMetric I M) (lambda x₀ x₁ t : ℝ) : ℝ :=
  ∫ x in x₀..x₁, c.curvatureSq g lambda x t * c.speed g lambda x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcEnergy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcEnergy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcEnergy ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.arcEnergy


def SmoothOn (J : Set ℝ) : Prop :=
  c.projection.SmoothOn (I := I) J ∧
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => c.y p.1 p.2) (_root_.Set.univ ×ˢ J)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.SmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.SmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.SmoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.SmoothOn

def ImmersedOn (J : Set ℝ) : Prop := ∀ x t, t ∈ J → c.X (I := I) x t ≠ 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.ImmersedOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.ImmersedOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.ImmersedOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.ImmersedOn

structure IsSolutionOn (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (J : Set ℝ) : Prop where
  smooth : c.SmoothOn (I := I) J
  immersed : c.ImmersedOn (I := I) J
  equation : ∀ x t, t ∈ J → c.velocity (I := I) J x t = c.curvatureVector g lambda x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.IsSolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.IsSolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.IsSolutionOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.IsSolutionOn


def verticalUnit (lambda : ℝ) : c.Field (I := I) := fun _ _ => (0, lambda⁻¹)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.verticalUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.verticalUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.verticalUnit ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.verticalUnit


def angle (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (x t : ℝ) : ℝ :=
  c.inner g lambda x t (c.unitTangent g lambda x t) (c.verticalUnit lambda x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.angle


def IsRampOn (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (J : Set ℝ) : Prop :=
  c.ImmersedOn (I := I) J ∧ ∀ x t, t ∈ J → 0 < c.angle g lambda x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.IsRampOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.IsRampOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.IsRampOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.IsRampOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_nonneg (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) :
    0 ≤ c.speed g lambda x t := Real.sqrt_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.speed_nonneg

omit [CompleteSpace E] in
theorem curvature_nonneg (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) :
    0 ≤ c.curvature g lambda x t := Real.sqrt_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.curvature_nonneg

end ProductCurve

def coverProductMetric [T2Space M] (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda) :
    SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) :=
  g.prod (DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) (lambda ^ 2)
    (pow_pos hlambda 2) (DifferentialGeometry.euclideanMetric (E := ℝ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverProductMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverProductMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverProductMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverProductMetric

omit [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
theorem coverProductMetric_inner [T2Space M] (g : SmoothRiemannianMetric I M) (lambda : ℝ)
    (hlambda : 0 < lambda)
    (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    (coverProductMetric g lambda hlambda).inner p v w =
      g.inner p.1 v.1 w.1 + lambda ^ 2 * v.2 * w.2 := by
  rw [coverProductMetric, SmoothRiemannianMetric.prod_inner, DifferentialGeometry.scaleMetric_inner,
    DifferentialGeometry.euclideanMetric_inner, Real.inner_apply]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverProductMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverProductMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverProductMetric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverProductMetric_inner

omit [CompleteSpace E] in
theorem exists_coverProductMetric [T2Space M] (g : SmoothRiemannianMetric I M) (lambda : ℝ)
    (hlambda : 0 < lambda) :
    ∃ ĝ : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ),
      ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
        ĝ.inner p v w = g.inner p.1 v.1 w.1 + lambda ^ 2 * v.2 * w.2 :=
  ⟨coverProductMetric g lambda hlambda, coverProductMetric_inner g lambda hlambda⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_coverProductMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_coverProductMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_coverProductMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_coverProductMetric


omit [CompleteSpace E] in
theorem coverProductMetric_unique [T2Space M]
    (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (ĝ : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hĝ : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
      ĝ.inner p v w = g.inner p.1 v.1 w.1 + lambda ^ 2 * v.2 * w.2) :
    ĝ = coverProductMetric g lambda hlambda := by
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  rw [hĝ, coverProductMetric_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverProductMetric_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverProductMetric_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverProductMetric_unique ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverProductMetric_unique

private def lineTranslation (c : ℝ) : ℝ ≃ₘ[ℝ] ℝ where
  toFun s := s + c
  invFun s := s - c
  left_inv s := add_sub_cancel_right s c
  right_inv s := sub_add_cancel s c
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.lineTranslation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.lineTranslation target :: scope.openDecls } }

private def coverShift (c : ℝ) :
    (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ) :=
  (Diffeomorph.refl I M ∞).prodCongr (lineTranslation c)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverShift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverShift target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
private theorem coverShift_apply (c : ℝ) (p : M × ℝ) :
    coverShift (I := I) c p = (p.1, p.2 + c) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverShift_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverShift_apply target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
private theorem mfderiv_coverShift (c : ℝ) (p : M × ℝ)
    (v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (coverShift (I := I) c) p v = v := by
  have hline : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (lineTranslation c) p.2 =
      ContinuousLinearMap.id ℝ ℝ := by
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => r + c) p.2 = _
    rw [mfderiv_eq_fderiv, fderiv_add_const]
    exact fderiv_id
  change mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
    (Prod.map (id : M → M) (lineTranslation c)) p v = _
  rw [mfderiv_prodMap mdifferentiableAt_id
    ((lineTranslation c).mdifferentiable (by decide) p.2),
    mfderiv_id, hline]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.mfderiv_coverShift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.mfderiv_coverShift target :: scope.openDecls } }

omit [CompleteSpace E] in
private theorem pullbackMetric_coverShift [T2Space M] (g : SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (c : ℝ) :
    Diffeomorph.pullbackMetric (coverProductMetric g lambda hlambda)
      (coverShift (I := I) c) = coverProductMetric g lambda hlambda := by
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  rw [Diffeomorph.pullbackMetric_inner, coverProductMetric_inner, coverProductMetric_inner,
    mfderiv_coverShift, mfderiv_coverShift, coverShift_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.pullbackMetric_coverShift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.pullbackMetric_coverShift target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
private theorem coe_int_period (n : ℤ) :
    (((n : ℝ) : Surgery.Topology.Circle)) = 0 := by
  rw [show (n : ℝ) = n • (1 : ℝ) by simp, AddCircle.coe_zsmul, AddCircle.coe_period]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coe_int_period
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coe_int_period target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
private theorem coverShift_fiber (n : ℤ) (p : M × ℝ) :
    productCoverProjection (coverShift (I := I) (n : ℝ) p) = productCoverProjection p := by
  apply Prod.ext
  · rfl
  · change (((p.2 + (n : ℝ)) : ℝ) : Surgery.Topology.Circle) =
      ((p.2 : ℝ) : Surgery.Topology.Circle)
    rw [AddCircle.coe_add, coe_int_period, add_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverShift_fiber
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.coverShift_fiber target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
private theorem exists_coverShift_of_fiber_eq {x y : M × ℝ}
    (h : productCoverProjection x = productCoverProjection y) :
    ∃ n : ℤ, x = coverShift (I := I) (n : ℝ) y := by
  have h1 : x.1 = y.1 := congrArg (fun z : M × Surgery.Topology.Circle => z.1) h
  have h2 : (x.2 : Surgery.Topology.Circle) = (y.2 : Surgery.Topology.Circle) :=
    congrArg (fun z : M × Surgery.Topology.Circle => z.2) h
  have hmem : x.2 - y.2 ∈ AddSubgroup.zmultiples (1 : ℝ) := by
    rw [← QuotientAddGroup.eq_iff_sub_mem]
    exact h2
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  refine ⟨n, Prod.ext h1 ?_⟩
  change x.2 = y.2 + (n : ℝ)
  rw [show (n : ℝ) = n • (1 : ℝ) by simp, hn]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_coverShift_of_fiber_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_coverShift_of_fiber_eq target :: scope.openDecls } }

omit [CompleteSpace E] in
private theorem metricFiberCompatible_of_coverShift_invariant [T2Space M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace (ModelProd H ℝ) N]
    [IsManifold (I.prod 𝓘(ℝ, ℝ)) ∞ N]
    (f : M × ℝ → N)
    (hf : IsLocalDiffeomorph (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ f)
    (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (hfiber : ∀ x y : M × ℝ, f x = f y → ∃ n : ℤ, x = coverShift (I := I) (n : ℝ) y)
    (hinv : ∀ (n : ℤ) (z : M × ℝ), f (coverShift (I := I) (n : ℝ) z) = f z) :
    metricFiberCompatible (coverProductMetric g lambda hlambda) f hf := by
  intro x y hxy
  obtain ⟨n, hn⟩ := hfiber x y hxy
  subst hn
  let Φ := coverShift (I := I) (M := M) (n : ℝ)
  have hcomp : f ∘ (Φ : M × ℝ → M × ℝ) = f := by
    funext z
    exact hinv n z
  have hmetric : Diffeomorph.pullbackMetric (coverProductMetric g lambda hlambda) Φ =
      coverProductMetric g lambda hlambda :=
    pullbackMetric_coverShift (I := I) g lambda hlambda (n : ℝ)
  exact localPushInner_eq_of_fiber_preserving_isometry
    (coverProductMetric g lambda hlambda) f hf Φ hcomp hmetric y

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.metricFiberCompatible_of_coverShift_invariant
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.metricFiberCompatible_of_coverShift_invariant target :: scope.openDecls } }

structure QuotientProductAtlas (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  charts : ChartedSpace (ModelProd H ℝ) (M × Surgery.Topology.Circle)
  smoothManifold : letI := charts
    IsManifold (I.prod 𝓘(ℝ, ℝ)) ∞ (M × Surgery.Topology.Circle)
  cover_smooth : letI := charts
    letI := smoothManifold
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (productCoverProjection (M := M))
  cover_derivative_bijective : letI := charts
    letI := smoothManifold
    ∀ p : M × ℝ, Function.Bijective
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductAtlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductAtlas ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductAtlas

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem exists_quotientProductAtlas : Nonempty (QuotientProductAtlas I M) := by
  let cs : ChartedSpace (ModelProd H ℝ) (M × Surgery.Topology.Circle) :=
    prodChartedSpace H M ℝ Surgery.Topology.Circle
  refine ⟨cs, IsManifold.prod M Surgery.Topology.Circle, ?_, ?_⟩
  · exact ContMDiff.prodMap contMDiff_id AddCircle.contMDiff_coe
  · intro p
    have hd1 : Function.Bijective (mfderiv I I (id : M → M) p.1) := by
      rw [mfderiv_id]
      exact ⟨fun a b h => h, fun a => ⟨a, rfl⟩⟩
    have hd2 : Function.Bijective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun t : ℝ => (t : Surgery.Topology.Circle)) p.2) := AddCircle.bijective_mfderiv_coe p.2
    have hprod : Function.Bijective ((mfderiv I I (id : M → M) p.1).prodMap
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : Surgery.Topology.Circle)) p.2)) := by
      refine ⟨fun a b hab => ?_, fun c => ?_⟩
      · refine Prod.ext (hd1.injective ?_) (hd2.injective ?_)
        · simpa using congrArg Prod.fst hab
        · simpa using congrArg Prod.snd hab
      · obtain ⟨a, ha⟩ := hd1.surjective c.1
        obtain ⟨b, hb⟩ := hd2.surjective c.2
        exact ⟨(a, b), Prod.ext (by simpa using ha) (by simpa using hb)⟩
    have hf : HasMFDerivAt I I (id : M → M) p.1 (ContinuousLinearMap.id ℝ E) := by
      have := (mdifferentiableAt_id (I := I) (x := p.1)).hasMFDerivAt
      rwa [mfderiv_id] at this
    have hg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun t : ℝ => (t : Surgery.Topology.Circle)) p.2
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : Surgery.Topology.Circle)) p.2) :=
      (AddCircle.contMDiff_coe.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)).hasMFDerivAt
    have hbij : Function.Bijective (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (Prod.map id (fun t : ℝ => (t : Surgery.Topology.Circle))) p) := by
      rw [(hf.prodMap hg).mfderiv]
      exact hprod
    exact hbij

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_quotientProductAtlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_quotientProductAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_quotientProductAtlas ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_quotientProductAtlas

def quotientProductAtlas : QuotientProductAtlas I M := exists_quotientProductAtlas.some

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductAtlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductAtlas ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductAtlas

structure QuotientProductGeometry (A : QuotientProductAtlas I M) [T2Space M]
    (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda) where
  metric : letI := A.charts
    letI := A.smoothManifold
    SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × Surgery.Topology.Circle)
  cover_pullback : letI := A.charts
    letI := A.smoothManifold
    ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
      metric.inner (productCoverProjection p)
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p v)
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection p w) =
          (coverProductMetric g lambda hlambda).inner p v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductGeometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.QuotientProductGeometry

omit [CompleteSpace E] in
theorem exists_quotientProductGeometry (A : QuotientProductAtlas I M) [T2Space M]
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda) :
    Nonempty (QuotientProductGeometry A g lambda hlambda) := by
  let := A.charts
  let := A.smoothManifold
  have hf : IsLocalDiffeomorph (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (productCoverProjection (M := M)) :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
      (productCoverProjection (M := M)) A.cover_smooth
      (fun p => (A.cover_derivative_bijective p).injective) rfl
  have hsurj : Function.Surjective (productCoverProjection (M := M)) := by
    intro q
    obtain ⟨s, -, hs⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) q.2
    exact ⟨(q.1, s), Prod.ext rfl hs⟩
  have hcompat : metricFiberCompatible (coverProductMetric g lambda hlambda)
      (productCoverProjection (M := M)) hf :=
    metricFiberCompatible_of_coverShift_invariant (productCoverProjection (M := M)) hf
      g lambda hlambda
      (fun x y h => exists_coverShift_of_fiber_eq (I := I) h)
      (fun n z => coverShift_fiber (I := I) n z)
  refine ⟨⟨descendedMetric (coverProductMetric g lambda hlambda)
    (productCoverProjection (M := M)) hf hsurj hcompat, ?_⟩⟩
  intro p v w
  rw [← localPullMetric_inner (descendedMetric (coverProductMetric g lambda hlambda)
      (productCoverProjection (M := M)) hf hsurj hcompat)
      (productCoverProjection (M := M)) hf p v w,
    localPullMetric_descendedMetric (coverProductMetric g lambda hlambda)
      (productCoverProjection (M := M)) hf hsurj hcompat]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_quotientProductGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_quotientProductGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_quotientProductGeometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_quotientProductGeometry


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem ProductCurve.cover_spatial_derivative (c : ProductCurve M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun z => c.coverLift z t) x (1 : ℝ) =
      c.X (I := I) x t := by
  have hmem : (x, t) ∈ (_root_.Set.univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ => (z, t)) _root_.Set.univ x :=
    contMDiffWithinAt_id.prodMk contMDiffWithinAt_const
  have hz' : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun z : ℝ => (z, t)) _root_.Set.univ x := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hz
  have hto : Set.MapsTo (fun z : ℝ => (z, t)) _root_.Set.univ ((_root_.Set.univ : Set ℝ) ×ˢ J) :=
    fun z _ => ⟨mem_univ z, ht⟩
  have h1 : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun z => c.projection.lift z t) x := by
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞
        ((fun p : ℝ × ℝ => c.projection.lift p.1 p.2) ∘ fun z : ℝ => (z, t)) _root_.Set.univ x :=
      (hc.1 (x, t) hmem).comp x hz' hto
    exact (contMDiffWithinAt_univ.mp hcomp).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => c.y z t) x := by
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        ((fun p : ℝ × ℝ => c.y p.1 p.2) ∘ fun z : ℝ => (z, t)) _root_.Set.univ x :=
      ((hc.2 (x, t) hmem).contMDiffWithinAt).comp x hz' hto
    exact (contMDiffWithinAt_univ.mp hcomp).mdifferentiableAt (by simp)
  have hpair := h1.mfderiv_prod h2
  change (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
    (fun z => (c.projection.lift z t, c.y z t)) x) (1 : ℝ) = c.X (I := I) x t
  rw [hpair]
  change (((mfderiv 𝓘(ℝ, ℝ) I (fun z => c.projection.lift z t) x).prod
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => c.y z t) x))
      (1 : TangentSpace 𝓘(ℝ, ℝ) x)) = c.X (I := I) x t
  rw [show ((mfderiv 𝓘(ℝ, ℝ) I (fun z => c.projection.lift z t) x).prod
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => c.y z t) x))
      (1 : TangentSpace 𝓘(ℝ, ℝ) x) = _ from
    ContinuousLinearMap.prod_apply (f₁ := mfderiv 𝓘(ℝ, ℝ) I (fun z => c.projection.lift z t) x)
      (f₂ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => c.y z t) x)
      (x := (1 : TangentSpace 𝓘(ℝ, ℝ) x))]
  refine Prod.ext rfl ?_
  change ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => c.y z t) x : ℝ →L[ℝ] ℝ)
      (1 : TangentSpace 𝓘(ℝ, ℝ) x)) =
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c.y x t)).symm (deriv (fun z => c.y z t) x)
  apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c.y x t)).injective
  rw [(NormedSpace.fromTangentSpace (𝕜 := ℝ) (c.y x t)).apply_symm_apply]
  change mvfderiv (I := 𝓘(ℝ, ℝ)) (fun z => c.y z t) x
      (1 : TangentSpace 𝓘(ℝ, ℝ) x) = deriv (fun z => c.y z t) x
  rw [DifferentialGeometry.mvfderiv_real_model_eq_fderiv,
    show (1 : TangentSpace 𝓘(ℝ, ℝ) x) =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1 from rfl,
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).apply_symm_apply, fderiv_apply_one_eq_deriv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.cover_spatial_derivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.cover_spatial_derivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.cover_spatial_derivative ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.cover_spatial_derivative

omit [CompleteSpace E] in
theorem ProductCurve.cover_covariantDerivative [T2Space M] (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (J : Set ℝ) (hc : c.SmoothOn (I := I) J) (V : c.Field (I := I))
    (hV : ∀ t ∈ J, ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, V x t⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))))
    (x t : ℝ) (ht : t ∈ J) (hint : I.IsInteriorPoint (c.projection.lift x t)) :
    covDerivAlong (coverProductMetric (g t) lambda hlambda) (fun z => c.coverLift z t)
      (fun z => V z t) x = c.Dx g V x t := by
  let _ := hc
  have hsec : ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun z => (⟨c.coverLift z t, V z t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) x :=
    (hV t ht).contMDiffAt
  have hprod : ContMDiffAt 𝓘(ℝ, ℝ) (I.tangent.prod 𝓘(ℝ, ℝ).tangent) ∞
      (fun z => (equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ)
        (⟨c.coverLift z t, V z t⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) x :=
    (contMDiff_equivTangentBundleProd (I := I) (I' := 𝓘(ℝ, ℝ)) (M := M) (M' := ℝ)
      (n := ∞)).contMDiffAt.comp x hsec
  have hfirst : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun z => (⟨c.projection.lift z t, (V z t).1⟩ : TangentBundle I M)) x :=
    ((contMDiff_fst (I := I.tangent) (J := 𝓘(ℝ, ℝ).tangent) (M := TangentBundle I M)
      (N := TangentBundle 𝓘(ℝ, ℝ) ℝ)).contMDiffAt.comp x hprod).mdifferentiableAt (by simp)
  have hsecond : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent
      (fun z => (⟨c.y z t, (V z t).2⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) x :=
    ((contMDiff_snd (I := I.tangent) (J := 𝓘(ℝ, ℝ).tangent) (M := TangentBundle I M)
      (N := TangentBundle 𝓘(ℝ, ℝ) ℝ)).contMDiffAt.comp x hprod).mdifferentiableAt (by simp)
  have hintReal : (𝓘(ℝ, ℝ)).IsInteriorPoint (c.y x t) := by
    simp [ModelWithCorners.IsInteriorPoint]
  have hsplit :=
    DifferentialGeometry.Geometry.Connection.covDerivAlong_prod_of_isInteriorPoint
    (I := I) (I' := 𝓘(ℝ, ℝ))
    (g := g t) (g' := DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) (lambda ^ 2)
      (pow_pos hlambda 2) (DifferentialGeometry.euclideanMetric (E := ℝ)))
    (γ := fun z => c.projection.lift z t) (γ' := fun z => c.y z t)
    (Z := fun z => (V z t).1) (Z' := fun z => (V z t).2) x hfirst hsecond hint hintReal
  have hflat := covDerivAlong_scaleEuclideanLine_eq_deriv (lambda ^ 2) (pow_pos hlambda 2)
    (fun z => c.y z t) (fun z => (V z t).2) x
  have hcongr :=
    DifferentialGeometry.Geometry.Riemannian.Variation.covDerivAlong_congr_of_eventuallyEq
      (g := coverProductMetric (g t) lambda hlambda) (γ := fun z => c.coverLift z t)
    (V := fun z => V z t)
    (W := fun u => ((fun z => (V z t).1) u, (fun z => (V z t).2) u)) (t := x)
    (Filter.Eventually.of_forall fun u => Prod.mk.eta.symm)
  have hcur : (fun z => c.coverLift z t) = fun u => (c.projection.lift u t, c.y u t) := rfl
  rw [hcongr]
  unfold coverProductMetric
  rw [hcur, ProductCurve.Dx]
  exact hsplit.trans (by rw [hflat]; rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.cover_covariantDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.cover_covariantDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.cover_covariantDerivative ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.cover_covariantDerivative

section QuotientGeometry

variable (A : QuotientProductAtlas I M)


omit [CompleteSpace E] in
theorem isLocalDiffeomorph_productCoverProjection (A : QuotientProductAtlas I M)
    [I.Boundaryless] :
    letI := A.charts
    letI := A.smoothManifold
    IsLocalDiffeomorph (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (productCoverProjection (M := M)) := by
  let := A.charts
  let := A.smoothManifold
  exact DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
    (productCoverProjection (M := M)) A.cover_smooth
    (fun p => (A.cover_derivative_bijective p).injective) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.isLocalDiffeomorph_productCoverProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.isLocalDiffeomorph_productCoverProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.isLocalDiffeomorph_productCoverProjection ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.isLocalDiffeomorph_productCoverProjection

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem surjective_productCoverProjection :
    Function.Surjective (productCoverProjection (M := M)) := by
  intro q
  obtain ⟨s, -, hs⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) q.2
  exact ⟨(q.1, s), Prod.ext rfl hs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.surjective_productCoverProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.surjective_productCoverProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.surjective_productCoverProjection ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.surjective_productCoverProjection

omit [CompleteSpace E] in
theorem metricFiberCompatible_coverProductMetric (A : QuotientProductAtlas I M) [T2Space M]
    [I.Boundaryless] (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    metricFiberCompatible (coverProductMetric g lambda hlambda)
      (productCoverProjection (M := M)) (isLocalDiffeomorph_productCoverProjection A) := by
  let := A.charts
  let := A.smoothManifold
  exact metricFiberCompatible_of_coverShift_invariant (productCoverProjection (M := M))
    (isLocalDiffeomorph_productCoverProjection A) g lambda hlambda
    (fun x y h => exists_coverShift_of_fiber_eq (I := I) h)
    (fun n z => coverShift_fiber (I := I) n z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.metricFiberCompatible_coverProductMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.metricFiberCompatible_coverProductMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.metricFiberCompatible_coverProductMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.metricFiberCompatible_coverProductMetric

def quotientProductMetric [T2Space M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × Surgery.Topology.Circle) :=
  let := A.charts
  let := A.smoothManifold
  descendedMetric (coverProductMetric g lambda hlambda) (productCoverProjection (M := M))
    (isLocalDiffeomorph_productCoverProjection A)
    (surjective_productCoverProjection (M := M))
    (metricFiberCompatible_coverProductMetric A g lambda hlambda)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductMetric

omit [CompleteSpace E] in
theorem quotientProductMetric_localPull (A : QuotientProductAtlas I M) [T2Space M]
    [I.Boundaryless] (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    DifferentialGeometry.localPullMetric (quotientProductMetric A g lambda hlambda)
      (productCoverProjection (M := M)) (isLocalDiffeomorph_productCoverProjection A) =
      coverProductMetric g lambda hlambda := by
  let := A.charts
  let := A.smoothManifold
  exact localPullMetric_descendedMetric (coverProductMetric g lambda hlambda)
    (productCoverProjection (M := M)) (isLocalDiffeomorph_productCoverProjection A)
    (surjective_productCoverProjection (M := M))
    (metricFiberCompatible_coverProductMetric A g lambda hlambda)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductMetric_localPull then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductMetric_localPull"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductMetric_localPull ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductMetric_localPull

variable [SigmaCompactSpace M] [T2Space M]

def quotientProductFamily [I.Boundaryless]
    (G : SolutionFamily (I := I) (M := M)) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    SolutionFamily (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) :=
  by
    letI := A.charts
    letI := A.smoothManifold
    exact ⟨fun t => quotientProductMetric A (G.metric t) lambda hlambda⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.quotientProductFamily

end QuotientGeometry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem exists_productCurve_lift (c : CurveMap (M × Surgery.Topology.Circle)) {a b : ℝ} (hab : a < b)
    (hbase : CurveMap.SmoothOn (I := I) (fun z t => (c z t).1) (_root_.Set.Icc a b))
    (hcircle : ∀ x t, t ∈ _root_.Set.Icc a b → ∃ localLift : ℝ × ℝ → ℝ,
      ContDiffWithinAt ℝ ∞ localLift (_root_.Set.univ ×ˢ _root_.Set.Icc a b) (x, t) ∧
      ∀ᶠ p in 𝓝[_root_.Set.univ ×ˢ _root_.Set.Icc a b] (x, t),
        (localLift p : Surgery.Topology.Circle) = (c (p.1 : Surgery.Topology.Circle) p.2).2) :
    ∃ ĉ : ProductCurve M, ĉ.SmoothOn (I := I) (_root_.Set.Icc a b) ∧
      ∀ z t, t ∈ _root_.Set.Icc a b → ĉ.map z t = c z t := by
  classical
  set s : Set ℝ := _root_.Set.Icc a b with hs
  have hane : a ∈ s := left_mem_Icc.mpr (le_of_lt hab)
  have hsconv : Convex ℝ s := convex_Icc a b
  have hne : s.Nonempty := ⟨a, hane⟩
  set f : ℝ × ℝ → Surgery.Topology.Circle :=
    fun p => (c (p.1 : Surgery.Topology.Circle) p.2).2 with hf
  have hper : ∀ p : ℝ × ℝ, f (p.1 + 1, p.2) = f p := by
    intro p
    have h1 : ((p.1 + 1 : ℝ) : Surgery.Topology.Circle) = (p.1 : Surgery.Topology.Circle) := by
      rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
    simp only [f]
    rw [h1]
  have hloc : ∀ q ∈ (_root_.Set.univ : Set ℝ) ×ˢ s, ∃ φ : ℝ × ℝ → ℝ,
      ContDiffWithinAt ℝ ∞ φ ((_root_.Set.univ : Set ℝ) ×ˢ s) q ∧
      (fun p => (φ p : Surgery.Topology.Circle)) =ᶠ[𝓝[(_root_.Set.univ : Set ℝ) ×ˢ s] q] f := by
    intro q hq
    obtain ⟨φ, hφ, hφeq⟩ := hcircle q.1 q.2 hq.2
    exact ⟨φ, hφ, hφeq⟩
  obtain ⟨g, d, hg_smooth, hg_lift, hg_inc⟩ :=
    DifferentialGeometry.Topology.exists_contDiffOn_addCircle_lift_of_periodic
      hsconv hne f hper hloc
  let map : CurveMap (M × Surgery.Topology.Circle) := fun z t => c z (if t ∈ s then t else a)
  let y : ℝ → ℝ → ℝ := fun x t => g (x, if t ∈ s then t else a)
  have hy_lift : ∀ x t,
      (y x t : Surgery.Topology.Circle) = (map (x : Surgery.Topology.Circle) t).2 := by
    intro x t
    by_cases ht : t ∈ s
    · simpa [y, map, f, ht] using hg_lift (x, t) ⟨trivial, ht⟩
    · simpa [y, map, f, ht] using hg_lift (x, a) ⟨trivial, hane⟩
  have hy_inc : ∀ x t, y (x + 1) t = y x t + d := by
    intro x t
    by_cases ht : t ∈ s
    · simpa [y, ht] using hg_inc (x, t) ⟨trivial, ht⟩
    · simpa [y, ht] using hg_inc (x, a) ⟨trivial, hane⟩
  have hmap_eq : ∀ z t, t ∈ s → map z t = c z t := by
    intro z t ht
    simp only [map, ht, if_pos]
  refine ⟨{ map := map, y := y, degree := d, lift_eq := hy_lift, increment := hy_inc }, ?_, ?_⟩
  · constructor
    · change ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
        (fun p : ℝ × ℝ => (map (p.1 : Surgery.Topology.Circle) p.2).1) (_root_.Set.univ ×ˢ s)
      refine hbase.congr fun p hp => ?_
      simp only [map, hp.2, if_pos, CurveMap.lift]
    · change ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => y p.1 p.2) (_root_.Set.univ ×ˢ s)
      refine hg_smooth.congr fun p hp => ?_
      simp [y, hp.2]
  · intro z t ht
    exact hmap_eq z t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_productCurve_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_productCurve_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_productCurve_lift ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_productCurve_lift

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
