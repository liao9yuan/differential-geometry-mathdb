import Submission.DifferentialGeometry.Geometry.Boundary.Orientation
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Minimum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E]
variable {H : Type*} [TopologicalSpace H]

section OutwardNormalDerivative

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

def outwardNormalDerivative
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (f : M → ℝ)
    (x : BoundaryManifold I M) : ℝ :=
  g.inner (x : M) (gradientFun (I := I) g f (x : M))
    (outwardNormal (E := E) (H := H) (I := I) (M := M) g x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative

@[simp] theorem outwardNormalDerivative_apply
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (f : M → ℝ)
    (x : BoundaryManifold I M) :
    outwardNormalDerivative (M := M) g f x =
      g.inner (x : M) (gradientFun (I := I) g f (x : M))
        (outwardNormal (E := E) (H := H) (I := I) (M := M) g x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative_apply ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative_apply

theorem outwardNormalDerivative_eq_mfderiv
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (f : M → ℝ)
    (x : BoundaryManifold I M) :
    outwardNormalDerivative (M := M) g f x =
      mfderiv I (modelWithCornersSelf ℝ ℝ) f (x : M)
        (outwardNormal (E := E) (H := H) (I := I) (M := M) g x) := by
  exact inner_gradientFun (I := I) g f (x : M)
    (outwardNormal (E := E) (H := H) (I := I) (M := M) g x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative_eq_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative_eq_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative_eq_mfderiv ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative_eq_mfderiv

end OutwardNormalDerivative

section BoundaryTangentDerivative

variable [NormedSpace ℝ E]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem mfderiv_boundary_tangent_eq_zero_at_local_min
    {f : M → ℝ} {x : BoundaryManifold I M}
    (hmin : IsLocalMin (fun y : BoundaryManifold I M ↦ f (y : M)) x)
    (hf : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f (x : M))
    (w : hI.boundaryE) :
    mfderiv I (modelWithCornersSelf ℝ ℝ) f (x : M)
        (boundaryInclusionMfderiv (M := M) x w) = 0 := by
  have hinclusion : MDifferentiableAt hI.boundaryI I
      (boundaryInclusion I M) x :=
    (boundaryInclusion_contMDiff (I := I) (M := M)).mdifferentiableAt
      (by simp)
  have hcomp : MDifferentiableAt hI.boundaryI
      (modelWithCornersSelf ℝ ℝ)
      (f ∘ boundaryInclusion I M) x := by
    exact hf.comp x hinclusion
  have hmin' : IsLocalMin (f ∘ boundaryInclusion I M) x := by
    simpa [Function.comp_def] using hmin
  have hzero : mfderiv hI.boundaryI (modelWithCornersSelf ℝ ℝ)
      (f ∘ boundaryInclusion I M) x = 0 :=
    mfderiv_eq_zero_at_spatial_min (I := hI.boundaryI) hmin' hcomp
  have hchain := mfderiv_comp x hf hinclusion
  have happ := congrArg (fun L => L w) hchain
  change mfderiv hI.boundaryI (modelWithCornersSelf ℝ ℝ)
      (f ∘ boundaryInclusion I M) x w =
        mfderiv I (modelWithCornersSelf ℝ ℝ) f (x : M)
          (boundaryInclusionMfderiv (M := M) x w) at happ
  rw [hzero] at happ
  calc
    _ = (0 : TangentSpace hI.boundaryI x →L[Real]
          TangentSpace (modelWithCornersSelf ℝ ℝ) (f (x : M))) w := happ.symm
    _ = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.mfderiv_boundary_tangent_eq_zero_at_local_min then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.mfderiv_boundary_tangent_eq_zero_at_local_min"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.mfderiv_boundary_tangent_eq_zero_at_local_min ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.mfderiv_boundary_tangent_eq_zero_at_local_min

end BoundaryTangentDerivative

section GradientBoundaryTangent

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem inner_gradient_boundary_tangent_eq_zero_at_local_min
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : BoundaryManifold I M}
    (hmin : IsLocalMin (fun y : BoundaryManifold I M ↦ f (y : M)) x)
    (hf : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f (x : M))
    (w : hI.boundaryE) :
    g.inner (x : M) (gradientFun (I := I) g f (x : M))
        (boundaryInclusionMfderiv (M := M) x w) = 0 := by
  rw [inner_gradientFun]
  exact mfderiv_boundary_tangent_eq_zero_at_local_min
    (M := M) hmin hf w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_gradient_boundary_tangent_eq_zero_at_local_min then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_gradient_boundary_tangent_eq_zero_at_local_min"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_gradient_boundary_tangent_eq_zero_at_local_min ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_gradient_boundary_tangent_eq_zero_at_local_min

end GradientBoundaryTangent

section OutwardNormalSign

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem outwardNormalDerivative_neg_of_inner_gradient_inwardCoord_pos_at_local_min
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : BoundaryManifold I M}
    (hmin : IsLocalMin (fun y : BoundaryManifold I M ↦ f (y : M)) x)
    (hf : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f (x : M))
    (hinward : 0 < g.inner (x : M) (gradientFun (I := I) g f (x : M))
      (inwardCoord (M := M) x)) :
    outwardNormalDerivative (M := M) g f x < 0 := by
  have htangent : g.inner (x : M) (gradientFun (I := I) g f (x : M))
      (inwardTangentialPart (M := M) g x) = 0 := by
    rw [inwardTangentialPart_def]
    exact inner_gradient_boundary_tangent_eq_zero_at_local_min
      (M := M) g hmin hf (boundaryComponentOfInward (M := M) g x)
  have houtwardDir : g.inner (x : M) (gradientFun (I := I) g f (x : M))
      (outwardDir (M := M) g x) =
        -g.inner (x : M) (gradientFun (I := I) g f (x : M))
          (inwardCoord (M := M) x) := by
    rw [outwardDir_def, map_sub, htangent, zero_sub]
  rw [outwardNormalDerivative_apply, outwardNormal_eq, map_smul,
    houtwardDir]
  change (Real.sqrt
      (g.inner (x : M) (outwardDir (M := M) g x)
        (outwardDir (M := M) g x)))⁻¹ *
      (-g.inner (x : M) (gradientFun (I := I) g f (x : M))
        (inwardCoord (M := M) x)) < 0
  have hscale : 0 < (Real.sqrt
      (g.inner (x : M) (outwardDir (M := M) g x)
        (outwardDir (M := M) g x)))⁻¹ := by
    exact inv_pos.mpr (Real.sqrt_pos.mpr (g_inner_outwardDir_pos (M := M) g x))
  exact mul_neg_of_pos_of_neg hscale (neg_neg_of_pos hinward)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative_neg_of_inner_gradient_inwardCoord_pos_at_local_min then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative_neg_of_inner_gradient_inwardCoord_pos_at_local_min"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative_neg_of_inner_gradient_inwardCoord_pos_at_local_min ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalDerivative_neg_of_inner_gradient_inwardCoord_pos_at_local_min

end OutwardNormalSign

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
