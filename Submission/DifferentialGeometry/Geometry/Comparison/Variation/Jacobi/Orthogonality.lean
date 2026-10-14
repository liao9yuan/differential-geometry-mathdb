import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Order.Directed

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Manifold _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Geometry.Curvature (riemannOp riemannOp_metric_skew)
open _root_.Submission.DifferentialGeometry.Geometry.Connection (LeviCivita)
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem inner_curveVelocity_eq_add_mul_of_isJacobiAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t, TangentSpace I (γ t)) {s : Set ℝ} (hs : Convex ℝ s)
    (hγ : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hgeo : IsGeodesicOn (I := I) g γ (interior s))
    (hJ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (J r) : TangentBundle I M)) t)
    (hDJ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (covDerivAlong (I := I) g γ J r) :
        TangentBundle I M)) t)
    (hJac : ∀ t ∈ interior s, IsJacobiAt (I := I) g γ J t)
    {a t : ℝ} (ha : a ∈ s) (ht : t ∈ s) :
    g.inner (γ t) (J t) (curveVelocity (I := I) γ t) =
      g.inner (γ a) (J a) (curveVelocity (I := I) γ a) +
        (t - a) * g.inner (γ a) (covDerivAlong (I := I) g γ J a)
          (curveVelocity (I := I) γ a) := by
  let f : ℝ → ℝ := fun r => g.inner (γ r) (J r) (curveVelocity (I := I) γ r)
  let q : ℝ → ℝ := fun r => g.inner (γ r) (covDerivAlong (I := I) g γ J r)
    (curveVelocity (I := I) γ r)
  have hveldiff r (hr : r ∈ s) : DifferentiableAt ℝ
      (chartRepAt (I := I) γ (curveVelocity (I := I) γ) r) r :=
    differentiableAt_chartRepAt_curveVelocity (hγ r hr)
  have hJdiff r (hr : r ∈ s) :=
    (mdifferentiableAt_tangentField_iff.mp (hJ r hr)).2
  have hDJdiff r (hr : r ∈ s) :=
    (mdifferentiableAt_tangentField_iff.mp (hDJ r hr)).2
  have hvelpar r (hr : r ∈ interior s) :
      covDerivAlong (I := I) g γ (curveVelocity (I := I) γ) r = 0 :=
    covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g γ r
      (hγ r (interior_subset hr)) (hgeo.hasGeodesicEquationAt hr)
  have hcurvzero r :
      g.inner (γ r)
        (riemannOp (LeviCivita (I := I) g) (γ r) (J r)
          (curveVelocity (I := I) γ r) (curveVelocity (I := I) γ r))
        (curveVelocity (I := I) γ r) = 0 := by
    have h := riemannOp_metric_skew (I := I) g (γ r) (J r)
      (curveVelocity (I := I) γ r) (curveVelocity (I := I) γ r)
      (curveVelocity (I := I) γ r)
    rw [g.symm (γ r) (curveVelocity (I := I) γ r)] at h
    linarith
  have hfcont : ContinuousOn f s := by
    intro r hr
    exact (inner_deriv_at (I := I) (n := 2) (by norm_num) g γ J
      (curveVelocity (I := I) γ) r (hγ r hr) (hJdiff r hr)
      (hveldiff r hr)).continuousAt.continuousWithinAt
  have hqcont : ContinuousOn q s := by
    intro r hr
    exact (inner_deriv_at (I := I) (n := 2) (by norm_num) g γ
      (fun r => covDerivAlong (I := I) g γ J r) (curveVelocity (I := I) γ)
      r (hγ r hr) (hDJdiff r hr) (hveldiff r hr)).continuousAt.continuousWithinAt
  have hfderiv r (hr : r ∈ interior s) : HasDerivAt f (q r) r := by
    have h := inner_deriv_at (I := I) (n := 2) (by norm_num) g γ J
      (curveVelocity (I := I) γ) r (hγ r (interior_subset hr))
      (hJdiff r (interior_subset hr)) (hveldiff r (interior_subset hr))
    rw [hvelpar r hr] at h
    simpa only [f, q, map_zero, add_zero] using h
  have hqderiv r (hr : r ∈ interior s) : HasDerivAt q 0 r := by
    have h := inner_deriv_at (I := I) (n := 2) (by norm_num) g γ
      (fun r => covDerivAlong (I := I) g γ J r) (curveVelocity (I := I) γ)
      r (hγ r (interior_subset hr)) (hDJdiff r (interior_subset hr))
      (hveldiff r (interior_subset hr))
    rw [hvelpar r hr, jacobi_d2_eq g γ J (hJac r hr)] at h
    simpa only [q, map_zero, add_zero, map_neg, neg_apply,
      hcurvzero r, neg_zero] using h
  have hconst {u : ℝ → ℝ} (hcont : ContinuousOn u s)
      (hderiv : ∀ r ∈ interior s, HasDerivAt u 0 r) :
      ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → u a = u b :=
    constant_of_monotoneOn_antitoneOn
      (monotoneOn_of_deriv_nonneg hs hcont
        (fun r hr => (hderiv r hr).differentiableAt.differentiableWithinAt)
        (fun r hr => (hderiv r hr).deriv.ge))
      (antitoneOn_of_deriv_nonpos hs hcont
        (fun r hr => (hderiv r hr).differentiableAt.differentiableWithinAt)
        (fun r hr => (hderiv r hr).deriv.le))
      (DirectedOn.of_linearOrder s)
  have hqconst : ∀ r ∈ s, q r = q a := fun _ hr => hconst hqcont hqderiv hr ha
  let u : ℝ → ℝ := fun r => f r - r * q a
  have hucont : ContinuousOn u s :=
    hfcont.sub (continuousOn_id.mul continuousOn_const)
  have huderiv r (hr : r ∈ interior s) : HasDerivAt u 0 r := by
    have h := hfderiv r hr
    rw [hqconst r (interior_subset hr)] at h
    exact (h.sub (hasDerivAt_mul_const (q a))).congr_deriv (sub_self (q a))
  have h := hconst hucont huderiv ht ha
  change f t = f a + (t - a) * q a
  dsimp only [u] at h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.inner_curveVelocity_eq_add_mul_of_isJacobiAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.inner_curveVelocity_eq_add_mul_of_isJacobiAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.inner_curveVelocity_eq_add_mul_of_isJacobiAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.inner_curveVelocity_eq_add_mul_of_isJacobiAt

theorem inner_covDerivAlong_curveVelocity_eq_of_isJacobiAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t, TangentSpace I (γ t)) {s : Set ℝ} (hs : Convex ℝ s)
    (hγ : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hgeo : IsGeodesicOn (I := I) g γ (interior s))
    (hJ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (J r) : TangentBundle I M)) t)
    (hDJ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (covDerivAlong (I := I) g γ J r) :
        TangentBundle I M)) t)
    (hJac : ∀ t ∈ interior s, IsJacobiAt (I := I) g γ J t)
    {a t : ℝ} (ha : a ∈ s) (ht : t ∈ s) :
    g.inner (γ t) (covDerivAlong (I := I) g γ J t) (curveVelocity (I := I) γ t) =
      g.inner (γ a) (covDerivAlong (I := I) g γ J a) (curveVelocity (I := I) γ a) := by
  by_cases hta : t = a
  · subst t
    rfl
  have h₁ := inner_curveVelocity_eq_add_mul_of_isJacobiAt g γ J hs hγ hgeo hJ hDJ hJac ha ht
  have h₂ := inner_curveVelocity_eq_add_mul_of_isJacobiAt g γ J hs hγ hgeo hJ hDJ hJac ht ha
  have hmul : (t - a) *
      (g.inner (γ t) (covDerivAlong (I := I) g γ J t) (curveVelocity (I := I) γ t) -
        g.inner (γ a) (covDerivAlong (I := I) g γ J a) (curveVelocity (I := I) γ a)) = 0 := by
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hta))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.inner_covDerivAlong_curveVelocity_eq_of_isJacobiAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.inner_covDerivAlong_curveVelocity_eq_of_isJacobiAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.inner_covDerivAlong_curveVelocity_eq_of_isJacobiAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.inner_covDerivAlong_curveVelocity_eq_of_isJacobiAt

theorem inner_covDerivAlong_curveVelocity_eq_zero_of_isJacobiAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t, TangentSpace I (γ t)) {s : Set ℝ} (hs : Convex ℝ s)
    (hγ : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hgeo : IsGeodesicOn (I := I) g γ (interior s))
    (hJ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (J r) : TangentBundle I M)) t)
    (hDJ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (covDerivAlong (I := I) g γ J r) :
        TangentBundle I M)) t)
    (hJac : ∀ t ∈ interior s, IsJacobiAt (I := I) g γ J t)
    {a b t : ℝ} (ha : a ∈ s) (hb : b ∈ s) (ht : t ∈ s) (hab : a ≠ b)
    (hinner : g.inner (γ a) (J a) (curveVelocity (I := I) γ a) =
      g.inner (γ b) (J b) (curveVelocity (I := I) γ b)) :
    g.inner (γ t) (covDerivAlong (I := I) g γ J t) (curveVelocity (I := I) γ t) = 0 := by
  have h₁ := inner_curveVelocity_eq_add_mul_of_isJacobiAt g γ J hs hγ hgeo hJ hDJ hJac ht ha
  have h₂ := inner_curveVelocity_eq_add_mul_of_isJacobiAt g γ J hs hγ hgeo hJ hDJ hJac ht hb
  have hmul : (a - b) * g.inner (γ t) (covDerivAlong (I := I) g γ J t)
      (curveVelocity (I := I) γ t) = 0 := by
    nlinarith
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hab)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.inner_covDerivAlong_curveVelocity_eq_zero_of_isJacobiAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.inner_covDerivAlong_curveVelocity_eq_zero_of_isJacobiAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.inner_covDerivAlong_curveVelocity_eq_zero_of_isJacobiAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.inner_covDerivAlong_curveVelocity_eq_zero_of_isJacobiAt

theorem inner_curveVelocity_eq_zero_of_isJacobiAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t, TangentSpace I (γ t)) {s : Set ℝ} (hs : Convex ℝ s)
    (hγ : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hgeo : IsGeodesicOn (I := I) g γ (interior s))
    (hJ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (J r) : TangentBundle I M)) t)
    (hDJ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r => (TotalSpace.mk' E (γ r) (covDerivAlong (I := I) g γ J r) :
        TangentBundle I M)) t)
    (hJac : ∀ t ∈ interior s, IsJacobiAt (I := I) g γ J t)
    {a b t : ℝ} (ha : a ∈ s) (hb : b ∈ s) (ht : t ∈ s) (hab : a ≠ b)
    (ha0 : g.inner (γ a) (J a) (curveVelocity (I := I) γ a) = 0)
    (hb0 : g.inner (γ b) (J b) (curveVelocity (I := I) γ b) = 0) :
    g.inner (γ t) (J t) (curveVelocity (I := I) γ t) = 0 := by
  have hq := inner_covDerivAlong_curveVelocity_eq_zero_of_isJacobiAt g γ J hs
    hγ hgeo hJ hDJ hJac ha hb ha hab (ha0.trans hb0.symm)
  have hf := inner_curveVelocity_eq_add_mul_of_isJacobiAt g γ J hs hγ hgeo hJ hDJ hJac ha ht
  rw [ha0, hq, _root_.MulZeroClass.mul_zero, add_zero] at hf
  exact hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.inner_curveVelocity_eq_zero_of_isJacobiAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.inner_curveVelocity_eq_zero_of_isJacobiAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.inner_curveVelocity_eq_zero_of_isJacobiAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.inner_curveVelocity_eq_zero_of_isJacobiAt

theorem jacobi_perp_of_ends
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) {c : ℝ}
    (hc : c ≠ 0)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : IsGeodesic (I := I) g γ)
    (hJdiff : ∀ t, DifferentiableAt ℝ
      (chartRepAt (I := I) γ J t) t)
    (hDJdiff : ∀ t, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hJacobian : IsJacobiAlong (I := I) g γ J)
    (hJ0 : J 0 = 0) (hJc : J c = 0) :
    ∀ t, g.inner (γ t) (J t) (curveVelocity (I := I) γ t) = 0 := by
  intro t
  exact inner_curveVelocity_eq_zero_of_isJacobiAt g γ J convex_univ
    (fun r _ => (hγ.contMDiffAt (x := r)).of_le (WithTop.coe_le_coe.2 le_top))
    (hgeo.isGeodesicOn _)
    (fun r _ => mdifferentiableAt_tangentField_iff.mpr
      ⟨(hγ.mdifferentiable (by simp)) r, hJdiff r⟩)
    (fun r _ => mdifferentiableAt_tangentField_iff.mpr
      ⟨(hγ.mdifferentiable (by simp)) r, hDJdiff r⟩)
    (fun r _ => hJacobian r) (_root_.Set.mem_univ 0) (_root_.Set.mem_univ c) (_root_.Set.mem_univ t) hc.symm
    (by simp only [hJ0, map_zero, zero_apply])
    (by simp only [hJc, map_zero, zero_apply])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_perp_of_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_perp_of_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_perp_of_ends ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_perp_of_ends

end DifferentialGeometry.Geometry.Riemannian.Variation
