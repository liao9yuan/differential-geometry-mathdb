import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Gram
import Submission.DifferentialGeometry.Geometry.Exponential.Variation.EndpointShape
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Matrix
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

def velocityJacobianFrame
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) {d : ℕ} (w : Fin d → TangentSpace I x) :
    Option (Fin d) →
      ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm x u t)
  | none => fun t => curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm x u) t
  | some i => fun t => intrinsicJacobi (I := I) g hEnorm x u (w i) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobianFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobianFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobianFrame ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobianFrame

@[simp] theorem velocityJacobianFrame_none
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) {d : ℕ} (w : Fin d → TangentSpace I x) :
    velocityJacobianFrame (I := I) g hEnorm x u w _root_.Option.none =
      fun t => curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm x u) t :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobianFrame_none then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobianFrame_none"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobianFrame_none ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobianFrame_none

@[simp] theorem velocityJacobianFrame_some
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) {d : ℕ} (w : Fin d → TangentSpace I x)
    (i : Fin d) :
    velocityJacobianFrame (I := I) g hEnorm x u w (_root_.Option.some i) =
      fun t => intrinsicJacobi (I := I) g hEnorm x u (w i) t :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobianFrame_some then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobianFrame_some"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobianFrame_some ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobianFrame_some

theorem velocityJacobian_gram_split
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) {d : ℕ} (w : Fin d → TangentSpace I x)
    (hperp : ∀ i, g.inner x u (w i) = 0) :
    (curveGram (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
        (velocityJacobianFrame (I := I) g hEnorm x u w) 1).det
      = g.inner x u u *
        (curveGram (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
          (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) 1).det := by
  have hsplit := curveGram_det_option (I := I) g
    (intrinsicGeodesic (I := I) g hEnorm x u)
    (velocityJacobianFrame (I := I) g hEnorm x u w) 1 (fun i => by
      simpa only [velocityJacobianFrame_none, velocityJacobianFrame_some, hperp i] using!
        intrinsicJacobi_perp (I := I) g hEnorm x u (w i))
  have hdiag :
      g.inner (intrinsicGeodesic (I := I) g hEnorm x u 1)
        (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm x u) 1)
        (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm x u) 1) =
      g.inner x u u := by
    exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x u 1
  simpa only [velocityJacobianFrame_none, velocityJacobianFrame_some, hdiag] using! hsplit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobian_gram_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobian_gram_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobian_gram_split ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobian_gram_split


theorem velocityJacobian_density_split
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) {d : ℕ} (w : Fin d → TangentSpace I x)
    (hperp : ∀ i, g.inner x u (w i) = 0) :
    curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
        (velocityJacobianFrame (I := I) g hEnorm x u w) 1
      = Real.sqrt (g.inner x u u) *
        curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
          (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) 1 := by
  rw [curveDensity, curveDensity,
    velocityJacobian_gram_split (I := I) g hEnorm x u w hperp,
    Real.sqrt_mul (metric_inner_self_nonneg (I := I) g x u)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobian_density_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobian_density_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobian_density_split ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.velocityJacobian_density_split


theorem jacobianDens_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (x : M) (u : TangentSpace I x)
    (B B' : Module.Basis ι ℝ (TangentSpace I x)) :
    curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
        (fun i t => intrinsicJacobi (I := I) g hEnorm x u (B' i) t) 1 =
      |B.det B'| *
        curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
          (fun i t => intrinsicJacobi (I := I) g hEnorm x u (B i) t) 1 := by
  classical
  let C : Matrix ι ι ℝ := B.toMatrix B'
  let hMetric : IsMetricNorm (I := I) (M := M) g := hEnorm
  let L : E →L[ℝ] TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm x u 1) :=
    mfderiv 𝓘(ℝ, E) I
      (fun b : E => expMapIntrinsic (I := I) g hMetric x
        (show TangentSpace I x from b))
      (show E from u)
  have hcoord (i : ι) : B' i = ∑ k, C k i • B k := by
    simpa only [C, Module.Basis.toMatrix_apply] using (B.sum_repr (B' i)).symm
  have hcol (w : TangentSpace I x) :
      intrinsicJacobi (I := I) g hEnorm x u w 1 =
        L (show E from w) := by
    exact intrinsic_jacobi_one (I := I) g hEnorm x u w
  have hjac (i : ι) :
      intrinsicJacobi (I := I) g hEnorm x u (B' i) 1 =
        ∑ k, C k i • intrinsicJacobi (I := I) g hEnorm x u (B k) 1 := by
    rw [hcol (B' i)]
    have hcoordE :
        (show E from B' i) = ∑ k, C k i • (show E from B k) :=
      hcoord i
    rw [hcoordE]
    calc
      L (∑ k, C k i • (show E from B k)) =
          ∑ k, L (C k i • (show E from B k)) := by
        exact map_sum L (fun k => C k i • (show E from B k)) Finset.univ
      _ = ∑ k, C k i • L (show E from B k) := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact L.map_smul _ _
      _ = ∑ k, C k i •
          intrinsicJacobi (I := I) g hEnorm x u (B k) 1 := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact congrArg (C k i • ·) (hcol (B k)).symm
  simpa only [C, Module.Basis.det_apply] using
    curveDensity_recomb (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm x u)
      (fun i t => intrinsicJacobi (I := I) g hEnorm x u (B i) t)
      (fun i t => intrinsicJacobi (I := I) g hEnorm x u (B' i) t)
      1 C hjac

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.jacobianDens_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.jacobianDens_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.jacobianDens_basis ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.jacobianDens_basis

theorem transDens_scale
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (x : M) (u : TangentSpace I x) {d : ℕ}
    (w : Fin d → TangentSpace I x) (t : ℝ) :
    curveDensity (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm x u)
        (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) t =
      |t| ^ d *
        curveDensity (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm x (t • u))
          (fun i => intrinsicJacobi (I := I) g hEnorm x (t • u) (w i)) 1 := by
  let L :=
    mfderiv 𝓘(ℝ, E) I
      (fun b : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from b))
      (t • (show E from u))
  have hcol (v : TangentSpace I x) :
      (intrinsicJacobi (I := I) g hEnorm x u v t : E) =
        t • (intrinsicJacobi (I := I) g hEnorm x (t • u) v 1 : E) := by
    have hat :
        (intrinsicJacobi (I := I) g hEnorm x u v t : E) =
          (L (t • (show E from v)) : E) := by
      exact intrinsic_jacobi_at (I := I) g hEnorm x
        (show E from u) (show E from v) t
    have hmap :
        (L (t • (show E from v)) : E) =
          t • (L (show E from v) : E) := by
      exact L.map_smul _ _
    have hone :
        (intrinsicJacobi (I := I) g hEnorm x (t • u) v 1 : E) =
          (L (show E from v) : E) := by
      exact intrinsic_jacobi_one (I := I) g hEnorm x
        (t • (show E from u)) (show E from v)
    exact hat.trans (hmap.trans (congrArg (fun z : E => t • z) hone.symm))
  let γ := intrinsicGeodesic (I := I) g hEnorm x (t • u)
  let V : Fin d → ∀ s, TangentSpace I (γ s) :=
    fun i => intrinsicJacobi (I := I) g hEnorm x (t • u) (w i)
  have hbridge :
      curveDensity (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm x u)
        (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) t =
      curveDensity (I := I) g γ (fun i => t • V i) 1 := by
    unfold curveDensity curveGram
    apply congrArg Real.sqrt
    apply congrArg Matrix.det
    ext i j
    simp only [Matrix.of_apply, Pi.smul_apply, γ, V]
    rw [intrinsicGeodesic_smul (I := I) g hEnorm x u t]
    change
      g.inner (intrinsicGeodesic (I := I) g hEnorm x u t)
        (intrinsicJacobi (I := I) g hEnorm x u (w i) t)
        (intrinsicJacobi (I := I) g hEnorm x u (w j) t) =
      g.inner (intrinsicGeodesic (I := I) g hEnorm x u t)
        (t • (intrinsicJacobi (I := I) g hEnorm x (t • u) (w i) 1 : E))
        (t • (intrinsicJacobi (I := I) g hEnorm x (t • u) (w j) 1 : E))
    rw [hcol, hcol]
  rw [hbridge, curveDensity_smul, Fintype.card_fin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.transDens_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.transDens_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.transDens_scale ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.transDens_scale

theorem radialJacobian_eq_velocity
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) :
    intrinsicJacobi (I := I) g hEnorm x u u 1
      = curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm x u) 1 := by
  set φ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x u with hφ
  have hrepar : (fun r : ℝ => intrinsicGeodesic (I := I) g hEnorm x (u + r • u) 1)
      = fun r : ℝ => φ (1 + r) := by
    funext r
    have hsmul : u + r • u = (1 + r) • u := by rw [add_smul, one_smul]
    rw [hsmul, intrinsicGeodesic_smul (I := I) g hEnorm x u (1 + r)]
  have hφ_mdiff1 : MDifferentiableAt 𝓘(ℝ, ℝ) I φ 1 :=
    ((intrinsicGeodesic_contMDiffOn (I := I) g hEnorm x u).contMDiffAt
      Filter.univ_mem).mdifferentiableAt (by norm_num)
  have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => 1 + r) 0
      (ContinuousLinearMap.id ℝ ℝ) := by
    exact (((hasFDerivAt_id (0 : ℝ)).const_add (1 : ℝ))).hasMFDerivAt
  have hφ_at : HasMFDerivAt 𝓘(ℝ, ℝ) I φ (1 + (0 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I φ 1) := by
    rw [add_zero]; exact hφ_mdiff1.hasMFDerivAt
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun r : ℝ => φ (1 + r)) 0
      ((mfderiv 𝓘(ℝ, ℝ) I φ 1).comp (ContinuousLinearMap.id ℝ ℝ)) :=
    hφ_at.comp 0 hshift
  have hJ : HasMFDerivAt 𝓘(ℝ, ℝ) I
      (fun r : ℝ => intrinsicGeodesic (I := I) g hEnorm x (u + r • u) 1) 0
      ((mfderiv 𝓘(ℝ, ℝ) I φ 1).comp (ContinuousLinearMap.id ℝ ℝ)) := by
    rw [hrepar]; exact hcomp
  change mfderiv 𝓘(ℝ, ℝ) I
      (fun r : ℝ => intrinsicGeodesic (I := I) g hEnorm x (u + r • u) 1) 0 1
    = mfderiv 𝓘(ℝ, ℝ) I φ 1 1
  rw [hJ.mfderiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialJacobian_eq_velocity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialJacobian_eq_velocity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialJacobian_eq_velocity ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.radialJacobian_eq_velocity

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
