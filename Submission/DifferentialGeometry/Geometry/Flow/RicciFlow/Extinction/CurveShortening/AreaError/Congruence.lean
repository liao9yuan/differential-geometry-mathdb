import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.Curve

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ Q] in
theorem X_eq_of_slice_eq {c c' : CurveMap Q} {t : ℝ}
    (h : ∀ theta, c theta t = c' theta t) (x : ℝ) :
    c.X (I := 𝓘(ℝ, E)) x t = c'.X (I := 𝓘(ℝ, E)) x t := by
  have hfun : (fun y : ℝ => c.lift y t) = fun y : ℝ => c'.lift y t :=
    funext fun y => h (y : Surgery.Topology.Circle)
  exact congrArg (fun f : ℝ → Q => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) f x 1) hfun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.X_eq_of_slice_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.X_eq_of_slice_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.X_eq_of_slice_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.X_eq_of_slice_eq

theorem curvatureVector_eq_of_slice_eq {c c' : CurveMap Q}
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) Q) {t : ℝ}
    (h : ∀ theta, c theta t = c' theta t) (x : ℝ) :
    c.curvatureVector g x t = c'.curvatureVector g x t := by
  change riemannianCurveCurvature (g t) (fun y : ℝ => c.lift y t) x =
    riemannianCurveCurvature (g t) (fun y : ℝ => c'.lift y t) x
  congr 1
  exact funext fun y => h (y : Surgery.Topology.Circle)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvatureVector_eq_of_slice_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvatureVector_eq_of_slice_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvatureVector_eq_of_slice_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.curvatureVector_eq_of_slice_eq

theorem areaError_eq_of_eqOn {c c' : CurveMap Q}
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) Q) {J : Set ℝ}
    (h : ∀ t ∈ J, ∀ theta, c theta t = c' theta t) {t : ℝ} (ht : t ∈ J) :
    c.areaError g J t = c'.areaError g J t := by
  have hvel (x : ℝ) : c.velocity (I := 𝓘(ℝ, E)) J x t =
      c'.velocity (I := 𝓘(ℝ, E)) J x t := by
    apply congrArg (fun L : ℝ →L[ℝ] E => L 1)
    exact mfderivWithin_congr_of_mem (fun s hs => h s hs _) ht
  have hX := X_eq_of_slice_eq (E := E) (h t ht)
  have hcurv := curvatureVector_eq_of_slice_eq g (h t ht)
  have hinner (x : ℝ) : (g t).inner (c.lift x t) = (g t).inner (c'.lift x t) := by
    exact congrArg (fun p : Q => (show E →L[ℝ] E →L[ℝ] ℝ from (g t).inner p)) (h t ht (x :
      Surgery.Topology.Circle))
  have hspeed (x : ℝ) : c.speed g x t = c'.speed g x t := by
    change Real.sqrt ((g t).inner (c.lift x t) (c.X x t : E) (c.X x t : E)) =
      Real.sqrt ((g t).inner (c'.lift x t) (c'.X x t : E) (c'.X x t : E))
    rw [hinner, hX]
    rfl
  have hT (x : ℝ) : c.unitTangent g x t = c'.unitTangent g x t := by
    change (c.speed g x t)⁻¹ • (c.X x t : E) = (c'.speed g x t)⁻¹ • (c'.X x t : E)
    rw [hspeed, hX]
    rfl
  have hN (x : ℝ) : c.normalVelocityError g J x t = c'.normalVelocityError g J x t := by
    change (c.velocity J x t : E) - c.curvatureVector g x t -
      (g t).inner (c.lift x t) ((c.velocity J x t : E) - c.curvatureVector g x t)
        (c.unitTangent g x t) • (c.unitTangent g x t : E) =
      (c'.velocity J x t : E) - c'.curvatureVector g x t -
      (g t).inner (c'.lift x t) ((c'.velocity J x t : E) - c'.curvatureVector g x t)
        (c'.unitTangent g x t) • (c'.unitTangent g x t : E)
    rw [hvel, hcurv, hT, hinner]
    rfl
  simp only [areaError, integral]
  refine intervalIntegral.integral_congr fun x _ => ?_
  change Real.sqrt ((g t).inner (c.lift x t) (c.normalVelocityError g J x t : E)
      (c.normalVelocityError g J x t : E)) * c.speed g x t =
    Real.sqrt ((g t).inner (c'.lift x t) (c'.normalVelocityError g J x t : E)
      (c'.normalVelocityError g J x t : E)) * c'.speed g x t
  rw [hspeed, hN, hinner]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.areaError_eq_of_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.areaError_eq_of_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.areaError_eq_of_eqOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.areaError_eq_of_eqOn

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

end
