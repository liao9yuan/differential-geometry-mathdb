import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev CurveMap (M : Type*) := AddCircle (1 : ℝ) → ℝ → M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

namespace CurveMap

def lift (c : CurveMap M) (x t : ℝ) : M := c (x : AddCircle (1 : ℝ)) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.lift ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.lift


def X (c : CurveMap M) (x t : ℝ) : TangentSpace I (c.lift x t) :=
  mfderiv 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x (1 : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.X then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.X"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.X ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.X


def velocity (c : CurveMap M) (J : Set ℝ) (x t : ℝ) :
    TangentSpace I (c.lift x t) :=
  mfderivWithin 𝓘(ℝ, ℝ) I (c.lift x) J t (1 : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.velocity

def speed (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (x t : ℝ) : ℝ :=
  Real.sqrt ((g t).inner (c.lift x t) (c.X (I := I) x t) (c.X (I := I) x t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.speed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.speed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.speed ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.speed

abbrev Field (c : CurveMap M) := (x t : ℝ) → TangentSpace I (c.lift x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Field ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Field

def unitTangent (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) : c.Field (I := I) :=
  fun x t => (c.speed g x t)⁻¹ • c.X x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.unitTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.unitTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.unitTangent ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.unitTangent


def Dx (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (V : c.Field (I := I)) : c.Field (I := I) :=
  fun x t => covDerivAlong (g t) (fun y => c.lift y t) (fun y => V y t) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Dx then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Dx"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Dx ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Dx

def Dt (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
    (V : c.Field (I := I)) : c.Field (I := I) := fun x t =>
  let γ := c.lift x
  let rep := chartRepAt (I := I) γ (V x) t
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) (γ t)).symmL ℝ (γ t)
    (derivWithin rep J t +
      chartChristoffelContraction (g t) (γ t)
        (derivWithin (chartCurve (I := I) (γ t) γ) J t) (rep t)
        (chartCurve (I := I) (γ t) γ t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Dt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Dt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Dt ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Dt

def Ds (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (V : c.Field (I := I)) : c.Field (I := I) :=
  fun x t => (c.speed g x t)⁻¹ • c.Dx g V x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Ds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Ds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Ds ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.Ds

def curvatureVector (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) :
    c.Field (I := I) := c.Ds g (c.unitTangent g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvatureVector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvatureVector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvatureVector ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvatureVector

def normSq (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (V : c.Field (I := I)) (x t : ℝ) : ℝ :=
  (g t).inner (c.lift x t) (V x t) (V x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.normSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.normSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.normSq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.normSq

def curvatureSq (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) : ℝ → ℝ → ℝ :=
  c.normSq g (c.curvatureVector g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvatureSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvatureSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvatureSq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvatureSq

def curvature (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (x t : ℝ) : ℝ :=
  Real.sqrt (c.curvatureSq g x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvature

def ds (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  (c.speed g x t)⁻¹ * deriv (fun y => f y t) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem ds_add (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (f h : ℝ → ℝ → ℝ) (x t : ℝ)
    (hf : DifferentiableAt ℝ (fun y => f y t) x) (hh : DifferentiableAt ℝ (fun y => h y t) x) :
    c.ds g (fun y τ => f y τ + h y τ) x t = c.ds g f x t + c.ds g h x t := by
  simp only [ds, deriv_fun_add hf hh, mul_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds_add ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds_add

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem ds_sub (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (f h : ℝ → ℝ → ℝ) (x t : ℝ)
    (hf : DifferentiableAt ℝ (fun y => f y t) x) (hh : DifferentiableAt ℝ (fun y => h y t) x) :
    c.ds g (fun y τ => f y τ - h y τ) x t = c.ds g f x t - c.ds g h x t := by
  simp only [ds, deriv_fun_sub hf hh, mul_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds_sub ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds_sub

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem ds_mul (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (f h : ℝ → ℝ → ℝ) (x t : ℝ)
    (hf : DifferentiableAt ℝ (fun y => f y t) x) (hh : DifferentiableAt ℝ (fun y => h y t) x) :
    c.ds g (fun y τ => f y τ * h y τ) x t = c.ds g f x t * h x t + f x t * c.ds g h x t := by
  simp only [ds, deriv_fun_mul hf hh]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds_mul ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ds_mul

def integral (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, f x t * c.speed g x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.integral ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.integral

def length (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (t : ℝ) : ℝ :=
  c.integral g (fun _ _ => 1) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.length ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.length

def totalCurvature (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) : ℝ → ℝ :=
  c.integral g (c.curvature g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.totalCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.totalCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.totalCurvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.totalCurvature

def energy (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) : ℝ → ℝ :=
  c.integral g (c.curvatureSq g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.energy ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.energy

def iteratedDs (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (m : ℕ) (V : c.Field (I := I)) : c.Field (I := I) :=
  (c.Ds g)^[m] V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.iteratedDs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.iteratedDs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.iteratedDs ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.iteratedDs


def SmoothOn (c : CurveMap M) (J : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun p => c.lift p.1 p.2) (_root_.Set.univ ×ˢ J)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.SmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.SmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.SmoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.SmoothOn

def ImmersedOn (c : CurveMap M) (J : Set ℝ) : Prop :=
  ∀ x t, t ∈ J → c.X (I := I) x t ≠ 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ImmersedOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ImmersedOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ImmersedOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.ImmersedOn


structure IsSolutionOn (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) : Prop where
  smooth : c.SmoothOn (I := I) J
  immersed : c.ImmersedOn (I := I) J
  equation : ∀ x t, t ∈ J → c.velocity (I := I) J x t = c.curvatureVector g x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsSolutionOn


structure IsGeometricSolutionOn (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (α : ℝ → ℝ → ℝ) : Prop where
  smooth : c.SmoothOn (I := I) J
  immersed : c.ImmersedOn (I := I) J
  tangentSmooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => α p.1 p.2) (_root_.Set.univ ×ˢ J)
  equation : ∀ x t, t ∈ J → c.velocity (I := I) J x t =
    c.curvatureVector g x t + α x t • c.unitTangent g x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsGeometricSolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsGeometricSolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsGeometricSolutionOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.IsGeometricSolutionOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_nonneg (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (x t : ℝ) :
    0 ≤ c.speed g x t := Real.sqrt_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.speed_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.speed_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.speed_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.speed_nonneg

omit [CompleteSpace E] in
theorem curvature_nonneg (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) (x t : ℝ) :
    0 ≤ c.curvature g x t := Real.sqrt_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvature_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvature_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvature_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvature_nonneg

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_pos (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    0 < c.speed g x t :=
  Real.sqrt_pos.2 ((g t).pos (c.lift x t) (c.X x t) (hc x t ht))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.speed_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.speed_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.speed_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.speed_pos

end CurveMap

variable [SigmaCompactSpace M] [T2Space M]

structure SmoothMetricWindow (D : RealTimeInterval) (a b : ℝ) where
  family : SolutionFamily (I := I) (M := M)
  smooth : MetricFamilySmoothOn (I := I) D family.metric
  lt : a < b
  regular : _root_.Set.Icc a b ⊆ D.regular

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothMetricWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothMetricWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothMetricWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothMetricWindow

structure RicciBackground (D : RealTimeInterval) (a b : ℝ) extends
    SmoothMetricWindow (I := I) (M := M) D a b where
  equation : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn
    (show SolutionOn (I := I) (M := M) D from ⟨family⟩)
  B₀ : ℝ
  B₁ : ℝ
  B₂ : ℝ
  B₀_nonneg : 0 ≤ B₀
  B₁_nonneg : 0 ≤ B₁
  B₂_nonneg : 0 ≤ B₂
  ricci_bound : ∀ t ∈ _root_.Set.Icc a b, ∀ p : M,
    normSq0S (family.metric t) p 2 (family.ricciAt t p) ≤ B₀ ^ 2
  riemann_bound : ∀ t ∈ _root_.Set.Icc a b, ∀ p : M,
    normSq0S (family.metric t) p 4 (family.rm04At t p) ≤ B₁ ^ 2
  nablaRicci_bound : ∀ t ∈ _root_.Set.Icc a b, ∀ p : M,
    normSq0S (family.metric t) p 3
      (totalNabla0SFun 2 (family.connection t) (family.ricci t) p) ≤ B₂ ^ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.RicciBackground then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.RicciBackground"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.RicciBackground ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.RicciBackground

def RicciBackground.C {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) : ℝ :=
  1 + 3 * B.B₀ + B.B₁ + 3 * B.B₂

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.RicciBackground
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.RicciBackground.C then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.RicciBackground.C"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.RicciBackground.C ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.RicciBackground.C

namespace CurveMap

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] in
theorem time_slice_contMDiffWithinAt (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ (fun s => c.lift x s) J t := by
  have hmem : (x, t) ∈ (_root_.Set.univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun s : ℝ => (x, s)) J t := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
  have hto : Set.MapsTo (fun s : ℝ => (x, s)) J ((_root_.Set.univ : Set ℝ) ×ˢ J) :=
    fun s _ => ⟨mem_univ x, by assumption⟩
  exact (hc (x, t) hmem).comp t hz hto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.time_slice_contMDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.time_slice_contMDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.time_slice_contMDiffWithinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.time_slice_contMDiffWithinAt

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] in
theorem time_slice_contMDiffOn (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (x : ℝ) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun s => c.lift x s) J :=
  fun t ht => time_slice_contMDiffWithinAt c J hc x t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.time_slice_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.time_slice_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.time_slice_contMDiffOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.time_slice_contMDiffOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] in
theorem space_slice_contMDiffWithinAt (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ (fun z => c.lift z t) _root_.Set.univ x := by
  have hmem : (x, t) ∈ (_root_.Set.univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun z : ℝ => (z, t)) _root_.Set.univ x := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_id.prodMk contMDiffWithinAt_const
  have hto : Set.MapsTo (fun z : ℝ => (z, t)) _root_.Set.univ ((_root_.Set.univ : Set ℝ) ×ˢ J) :=
    fun z _ => ⟨mem_univ z, ht⟩
  exact (hc (x, t) hmem).comp x hz hto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.space_slice_contMDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.space_slice_contMDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.space_slice_contMDiffWithinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.space_slice_contMDiffWithinAt

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] in
theorem space_slice_contMDiffOn (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun z => c.lift z t) univ :=
  fun x _ => space_slice_contMDiffWithinAt c J hc x t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.space_slice_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.space_slice_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.space_slice_contMDiffOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.space_slice_contMDiffOn

end CurveMap

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval} {a b : ℝ}

theorem SmoothMetricWindow.exists_right_extension
    (B : SmoothMetricWindow (I := I) (M := M) D a b) :
    ∃ b' : ℝ, b < b' ∧ ∃ B' : SmoothMetricWindow (I := I) (M := M) D a b',
      B'.family = B.family := by
  obtain ⟨l, b', hb, hregular⟩ :=
    D.exists_Icc_regular (B.regular ⟨B.lt.le, le_rfl⟩)
  refine ⟨b', hb.2, {
    family := B.family
    smooth := B.smooth
    lt := B.lt.trans hb.2
    regular := ?_ }, rfl⟩
  intro t ht
  by_cases htb : t ≤ b
  · exact B.regular ⟨ht.1, htb⟩
  · exact hregular ⟨hb.1.le.trans (lt_of_not_ge htb).le, ht.2⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothMetricWindow
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothMetricWindow.exists_right_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothMetricWindow.exists_right_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothMetricWindow.exists_right_extension ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothMetricWindow.exists_right_extension

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
