import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Covariant.CurvatureCommutation
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.AffineReparam
import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Topology _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

def IsJacobiAt (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ) : Prop :=
  covDerivAlong (I := I) g γ
      (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
    + (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
        (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
    = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAt

def IsJacobiAlong (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) : Prop :=
  ∀ t : ℝ, IsJacobiAt (I := I) g γ J t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAlong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAlong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAlong ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAlong

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
open _root_.Submission.DifferentialGeometry.Geometry.Connection (LeviCivita) in
theorem IsJacobiAt.congr_of_eventuallyEq
    {g : SmoothRiemannianMetric I M} {γ γ' : ℝ → M}
    {J : ∀ s, TangentSpace I (γ s)} {J' : ∀ s, TangentSpace I (γ' s)} {t : ℝ}
    (hjac : IsJacobiAt (I := I) g γ J t)
    (hfield : (fun s => (TotalSpace.mk' E (γ s) (J s) : TangentBundle I M)) =ᶠ[𝓝 t]
      (fun s => (TotalSpace.mk' E (γ' s) (J' s) : TangentBundle I M))) :
    IsJacobiAt (I := I) g γ' J' t := by
  have hγ : γ =ᶠ[𝓝 t] γ' := by
    filter_upwards [hfield] with s hs
    exact congrArg TotalSpace.proj hs
  have hJ : (fun s => (J s : E)) =ᶠ[𝓝 t] (fun s => (J' s : E)) := by
    filter_upwards [hfield] with s hs
    exact congrArg (fun z : TangentBundle I M => (z.snd : E)) hs
  let D : ∀ s, TangentSpace I (γ s) := fun s => covDerivAlong (I := I) g γ J s
  let D' : ∀ s, TangentSpace I (γ' s) := fun s => covDerivAlong (I := I) g γ' J' s
  have hD : ∀ᶠ s in 𝓝 t, (D s : E) = (D' s : E) := by
    filter_upwards [hγ.eventually_nhds, hJ.eventually_nhds] with s hγs hJs
    exact covDerivAlong_congr_curve (I := I) g J J' hγs hJs
  have hD2 : (covDerivAlong (I := I) g γ D t : E) =
      (covDerivAlong (I := I) g γ' D' t : E) :=
    covDerivAlong_congr_curve (I := I) g D D' hγ hD
  have hvel : (curveVelocity (I := I) γ t : E) = (curveVelocity (I := I) γ' t : E) := by
    exact congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hγ.mfderiv_eq
  have hpoint (x y : M) (hxy : x = y) (A B C : E) :
      (riemannOp (LeviCivita (I := I) g) x A B C : E) =
        (riemannOp (LeviCivita (I := I) g) y A B C : E) := by
    subst y
    rfl
  have hcurv : (riemannOp (LeviCivita (I := I) g) (γ t)
      (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) : E) =
      (riemannOp (LeviCivita (I := I) g) (γ' t)
        (J' t) (curveVelocity (I := I) γ' t) (curveVelocity (I := I) γ' t) : E) := by
    rw [hJ.eq_of_nhds, hvel]
    exact hpoint _ _ hγ.eq_of_nhds _ _ _
  change (covDerivAlong (I := I) g γ D t : E) + _ = 0 at hjac
  change (covDerivAlong (I := I) g γ' D' t : E) + _ = 0
  rw [← hD2, ← hcurv]
  exact hjac

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAt.congr_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAt.congr_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAt.congr_of_eventuallyEq ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAt.congr_of_eventuallyEq

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem isJacobiAlong_iff (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) :
    IsJacobiAlong (I := I) g γ J ↔
      ∀ t : ℝ,
        covDerivAlong (I := I) g γ
            (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
          = - (DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
              (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := by
  constructor
  · intro hJ t
    have h : covDerivAlong (I := I) g γ
          (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
        + (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
            (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
        = 0 := hJ t
    linear_combination (norm := module) h
  · intro hJ t
    have h := hJ t
    change covDerivAlong (I := I) g γ
          (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
        + (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
            (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
        = 0
    linear_combination (norm := module) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAlong_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAlong_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAlong_iff ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAlong_iff

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem jacobi_d2_eq
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) {t : ℝ}
    (hJ : IsJacobiAt (I := I) g γ J t) :
    covDerivAlong (I := I) g γ
        (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
      = - (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := by
  change covDerivAlong (I := I) g γ
        (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
      + (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
      = 0 at hJ
  linear_combination (norm := module) hJ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_d2_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_d2_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_d2_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_d2_eq

def jacobiWronskian
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ) : ℝ :=
  g.inner (γ t) (covDerivAlong (I := I) g γ J t) (K t) -
    g.inner (γ t) (J t) (covDerivAlong (I := I) g γ K t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.jacobiWronskian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.jacobiWronskian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.jacobiWronskian ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.jacobiWronskian

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem wronskian_deriv_at
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hJdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hKdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ K t) t)
    (hDJdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hDKdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ K s) t) t)
    (hJ : IsJacobiAt (I := I) g γ J t)
    (hK : IsJacobiAt (I := I) g γ K t) :
    HasDerivAt (jacobiWronskian (I := I) g γ J K) 0 t := by
  have hleft := inner_deriv_at (I := I) hn g γ
    (fun s => covDerivAlong (I := I) g γ J s) K t hγ hDJdiff hKdiff
  have hright := inner_deriv_at (I := I) hn g γ J
    (fun s => covDerivAlong (I := I) g γ K s) t hγ hJdiff hDKdiff
  have hsub := hleft.sub hright
  have hJ2 := jacobi_d2_eq (I := I) g γ J hJ
  have hK2 := jacobi_d2_eq (I := I) g γ K hK
  have hcurv := DifferentialGeometry.Geometry.Curvature.riemannOp_diag_symm
    (I := I) g (γ t) (curveVelocity (I := I) γ t) (J t) (K t)
  refine (hsub.congr_deriv ?_)
  rw [hJ2, hK2]
  simp only [map_neg, neg_apply]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.wronskian_deriv_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.wronskian_deriv_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.wronskian_deriv_at ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.wronskian_deriv_at

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem hasDerivAt_wronsk
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (hJdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hKdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ K t) t)
    (hDJdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hDKdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ K s) t) t)
    (hJ : IsJacobiAt (I := I) g γ J t)
    (hK : IsJacobiAt (I := I) g γ K t) :
    HasDerivAt (jacobiWronskian (I := I) g γ J K) 0 t :=
  wronskian_deriv_at (I := I) hn g γ J K t hγ.contMDiffAt
    hJdiff hKdiff hDJdiff hDKdiff hJ hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.hasDerivAt_wronsk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.hasDerivAt_wronsk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.hasDerivAt_wronsk ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.hasDerivAt_wronsk

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem jacobiWronskian_eq_of_isJacobiAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t, TangentSpace I (γ t)) {s : Set ℝ} (hs : Convex ℝ s)
    (hγ : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t)
    (hJ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (J r) : TangentBundle I M)) t)
    (hK : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (K r) : TangentBundle I M)) t)
    (hDJ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (covDerivAlong (I := I) g γ J r) :
        TangentBundle I M)) t)
    (hDK : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (covDerivAlong (I := I) g γ K r) :
        TangentBundle I M)) t)
    (hJacJ : ∀ t ∈ interior s, IsJacobiAt (I := I) g γ J t)
    (hJacK : ∀ t ∈ interior s, IsJacobiAt (I := I) g γ K t)
    {a t : ℝ} (ha : a ∈ s) (ht : t ∈ s) :
    jacobiWronskian (I := I) g γ J K t = jacobiWronskian (I := I) g γ J K a := by
  have hJdiff r (hr : r ∈ s) := (mdifferentiableAt_tangentField_iff.mp (hJ r hr)).2
  have hKdiff r (hr : r ∈ s) := (mdifferentiableAt_tangentField_iff.mp (hK r hr)).2
  have hDJdiff r (hr : r ∈ s) := (mdifferentiableAt_tangentField_iff.mp (hDJ r hr)).2
  have hDKdiff r (hr : r ∈ s) := (mdifferentiableAt_tangentField_iff.mp (hDK r hr)).2
  have hcont : ContinuousOn (jacobiWronskian (I := I) g γ J K) s := by
    intro r hr
    have hleft := inner_deriv_at (I := I) (n := 1) le_rfl g γ
      (fun u => covDerivAlong (I := I) g γ J u) K r (hγ r hr) (hDJdiff r hr) (hKdiff r hr)
    have hright := inner_deriv_at (I := I) (n := 1) le_rfl g γ J
      (fun u => covDerivAlong (I := I) g γ K u) r (hγ r hr) (hJdiff r hr) (hDKdiff r hr)
    exact (hleft.sub hright).continuousAt.continuousWithinAt
  have hderiv r (hr : r ∈ interior s) :
      HasDerivAt (jacobiWronskian (I := I) g γ J K) 0 r := by
    have hr' := interior_subset hr
    exact wronskian_deriv_at (I := I) (n := 1) le_rfl g γ J K r (hγ r hr')
      (hJdiff r hr') (hKdiff r hr') (hDJdiff r hr') (hDKdiff r hr') (hJacJ r hr) (hJacK r hr)
  have hmono := monotoneOn_of_deriv_nonneg hs hcont
    (fun r hr => (hderiv r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hderiv r hr).deriv.ge)
  have hanti := antitoneOn_of_deriv_nonpos hs hcont
    (fun r hr => (hderiv r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hderiv r hr).deriv.le)
  rcases le_total a t with hat | hta
  · exact le_antisymm (hanti ha ht hat) (hmono ha ht hat)
  · exact le_antisymm (hmono ht ha hta) (hanti ht ha hta)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.jacobiWronskian_eq_of_isJacobiAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.jacobiWronskian_eq_of_isJacobiAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.jacobiWronskian_eq_of_isJacobiAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.jacobiWronskian_eq_of_isJacobiAt

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem jacobiWronskian_eq_zero_of_isJacobiAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t, TangentSpace I (γ t)) {s : Set ℝ} (hs : Convex ℝ s)
    (hγ : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t)
    (hJ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (J r) : TangentBundle I M)) t)
    (hK : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (K r) : TangentBundle I M)) t)
    (hDJ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (covDerivAlong (I := I) g γ J r) :
        TangentBundle I M)) t)
    (hDK : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (covDerivAlong (I := I) g γ K r) :
        TangentBundle I M)) t)
    (hJacJ : ∀ t ∈ interior s, IsJacobiAt (I := I) g γ J t)
    (hJacK : ∀ t ∈ interior s, IsJacobiAt (I := I) g γ K t)
    {a t : ℝ} (ha : a ∈ s) (ht : t ∈ s) (hJa : J a = 0) (hKa : K a = 0) :
    jacobiWronskian (I := I) g γ J K t = 0 := by
  rw [jacobiWronskian_eq_of_isJacobiAt g γ J K hs hγ hJ hK hDJ hDK hJacJ hJacK ha ht]
  simp only [jacobiWronskian, hJa, hKa, map_zero, zero_apply, sub_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.jacobiWronskian_eq_zero_of_isJacobiAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.jacobiWronskian_eq_zero_of_isJacobiAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.jacobiWronskian_eq_zero_of_isJacobiAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.jacobiWronskian_eq_zero_of_isJacobiAt

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem wronskian_zero_on
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) {b : ℝ}
    (hγ : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hJdiff : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hKdiff : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ K t) t)
    (hDJdiff : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hDKdiff : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ K s) t) t)
    (hJacobianJ : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ J t)
    (hJacobianK : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ K t)
    (hJ0 : J 0 = 0) (hK0 : K 0 = 0) :
    ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, jacobiWronskian (I := I) g γ J K t = 0 := by
  intro t ht
  exact jacobiWronskian_eq_zero_of_isJacobiAt (I := I) g γ J K (convex_Icc _ _)
    (fun r hr => (hγ r hr).of_le hn)
    (fun r hr => mdifferentiableAt_tangentField_iff.mpr
      ⟨((hγ r hr).of_le hn).mdifferentiableAt (by norm_num), hJdiff r hr⟩)
    (fun r hr => mdifferentiableAt_tangentField_iff.mpr
      ⟨((hγ r hr).of_le hn).mdifferentiableAt (by norm_num), hKdiff r hr⟩)
    (fun r hr => mdifferentiableAt_tangentField_iff.mpr
      ⟨((hγ r hr).of_le hn).mdifferentiableAt (by norm_num), hDJdiff r hr⟩)
    (fun r hr => mdifferentiableAt_tangentField_iff.mpr
      ⟨((hγ r hr).of_le hn).mdifferentiableAt (by norm_num), hDKdiff r hr⟩)
    (fun r hr => hJacobianJ r (interior_subset hr))
    (fun r hr => hJacobianK r (interior_subset hr))
    ⟨le_rfl, ht.1.trans ht.2⟩ ht hJ0 hK0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.wronskian_zero_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.wronskian_zero_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.wronskian_zero_on ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.wronskian_zero_on

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem wronskian_eq_zero
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) {b : ℝ}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (hJdiff : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hKdiff : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ K t) t)
    (hDJdiff : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hDKdiff : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ K s) t) t)
    (hJacobianJ : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ J t)
    (hJacobianK : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ K t)
    (hJ0 : J 0 = 0) (hK0 : K 0 = 0) :
    ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, jacobiWronskian (I := I) g γ J K t = 0 :=
  wronskian_zero_on (I := I) hn g γ J K (fun _ _ => hγ.contMDiffAt)
    hJdiff hKdiff hDJdiff hDKdiff hJacobianJ hJacobianK hJ0 hK0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.wronskian_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.wronskian_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.wronskian_eq_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.wronskian_eq_zero

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ode_bound_of_isJacobiAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) {K t : ℝ}
    (hJ : IsJacobiAt (I := I) g γ J t)
    (hcurv :
      g.inner (γ t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t))
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t))
      ≤ K ^ 2 * g.inner (γ t) (J t) (J t)) :
    g.inner (γ t)
      (covDerivAlong (I := I) g γ
        (fun s : ℝ => covDerivAlong (I := I) g γ J s) t)
      (covDerivAlong (I := I) g γ
        (fun s : ℝ => covDerivAlong (I := I) g γ J s) t)
      ≤ K ^ 2 * g.inner (γ t) (J t) (J t) := by
  have hD :
      covDerivAlong (I := I) g γ
          (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
        = - (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
            (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := by
    have h := hJ
    change covDerivAlong (I := I) g γ
          (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
        + (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
            (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
        = 0 at h
    linear_combination (norm := module) h
  rw [hD]
  simpa using hcurv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.ode_bound_of_isJacobiAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.ode_bound_of_isJacobiAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.ode_bound_of_isJacobiAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.ode_bound_of_isJacobiAt

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
