import Submission.DifferentialGeometry.Geometry.Comparison.Hessian.AlongGeodesic
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.Transform

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Local

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] in
theorem cov_gradient_eq_zero_of_hessian_eq_zero
    (g : SmoothRiemannianMetric I M) {b : M → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b) (hH : ∀ p, hessFun (I := I) g b p = 0)
    (p : M) (v : TangentSpace I p) :
    (LeviCivita (I := I) g) (fun x => gradientFun (I := I) g b x) p v = 0 := by
  let w := (LeviCivita (I := I) g) (fun x => gradientFun (I := I) g b x) p v
  have hzero : g.inner p w w = 0 := by
    change g.inner p ((LeviCivita (I := I) g) (fun x => gradFun (I := I) g b x) p v) w = 0
    rw [← hessFun_eq_cov_grad (I := I) g hb p v w, hH p]
    rfl
  by_contra hw
  exact (ne_of_gt (g.pos p w hw)) hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.cov_gradient_eq_zero_of_hessian_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.cov_gradient_eq_zero_of_hessian_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.cov_gradient_eq_zero_of_hessian_eq_zero ``Submission.DifferentialGeometry.Geometry.Topology.cov_gradient_eq_zero_of_hessian_eq_zero

end Local

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

def affineGradientFlow
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (b : M → ℝ) (p : M) (t : ℝ) : M :=
  intrinsicGeodesic (I := I) g hEnorm p (gradientFun (I := I) g b p) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineGradientFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineGradientFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineGradientFlow ``Submission.DifferentialGeometry.Geometry.Topology.affineGradientFlow


@[simp] theorem affineGradientFlow_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (b : M → ℝ) (p : M) : affineGradientFlow (I := I) g hEnorm b p 0 = p :=
  intrinsicGeodesic_zero (I := I) g hEnorm p (gradientFun (I := I) g b p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineGradientFlow_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineGradientFlow_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineGradientFlow_zero ``Submission.DifferentialGeometry.Geometry.Topology.affineGradientFlow_zero

theorem hasDerivAt_affineFunction_flow
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (p : M) (t : ℝ) :
    HasDerivAt (fun s => b (affineGradientFlow (I := I) g hEnorm b p s)) 1 t := by
  let c := affineGradientFlow (I := I) g hEnorm b p
  have hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm p (gradientFun (I := I) g b p)
  have hgeo : IsGeodesic (I := I) g c :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p (gradientFun (I := I) g b p)
  have hbc : ContDiff ℝ ∞ (b ∘ c) := contMDiff_iff_contDiff.mp (hb.comp hc)
  have hsecond (s : ℝ) : deriv (deriv (b ∘ c)) s = 0 := by
    have h := deriv2_comp_geo_on (I := I) g isOpen_univ hb.contMDiffOn hc hgeo
      (t := s) (_root_.Set.mem_univ (c s))
    change deriv (deriv (b ∘ c)) s = hessFun (I := I) g b (c s)
      (mfderiv 𝓘(ℝ, ℝ) I c s 1) (mfderiv 𝓘(ℝ, ℝ) I c s 1) at h
    simpa only [hH, LinearMap.zero_apply] using h
  have hfirst0 : deriv (b ∘ c) 0 = 1 := by
    have hd := deriv_comp_mfderiv_along I b c 0
      (hb.mdifferentiable (by simp) (c 0)) (hc.mdifferentiable (by simp) 0)
    change deriv (b ∘ c) 0 = mvfderiv (I := I) b (c 0)
      (mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ) : E) at hd
    have hv : (mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ) : E) =
        (gradientFun (I := I) g b p : E) :=
      intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p (gradientFun (I := I) g b p)
    have hzero : c 0 = p := affineGradientFlow_zero (I := I) g hEnorm b p
    rw [hv] at hd
    erw [hzero] at hd
    rw [← inner_gradientFun (I := I) g b p, hunit p] at hd
    exact hd
  have hdifferentiable : Differentiable ℝ (deriv (b ∘ c)) :=
    (ContDiff.iterate_deriv 1 hbc).differentiable (by simp)
  have hfirst : deriv (b ∘ c) t = 1 :=
    (is_const_of_deriv_eq_zero hdifferentiable hsecond t 0).trans hfirst0
  have hd := (hbc.differentiable (by simp) t).hasDerivAt
  rw [hfirst] at hd
  exact hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.hasDerivAt_affineFunction_flow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.hasDerivAt_affineFunction_flow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.hasDerivAt_affineFunction_flow ``Submission.DifferentialGeometry.Geometry.Topology.hasDerivAt_affineFunction_flow

theorem affineFunction_flow_eq_add
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (p : M) (t : ℝ) :
    b (affineGradientFlow (I := I) g hEnorm b p t) = b p + t := by
  have hd (s : ℝ) :=
    (hasDerivAt_affineFunction_flow (I := I) g hEnorm hb hunit hH p s).sub (hasDerivAt_id s)
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => by simpa only [sub_self] using (hd s).deriv) t 0
  change b (affineGradientFlow (I := I) g hEnorm b p t) - t =
    b (affineGradientFlow (I := I) g hEnorm b p 0) - 0 at hconst
  rw [affineGradientFlow_zero, sub_zero] at hconst
  exact sub_eq_iff_eq_add.mp hconst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineFunction_flow_eq_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineFunction_flow_eq_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineFunction_flow_eq_add ``Submission.DifferentialGeometry.Geometry.Topology.affineFunction_flow_eq_add

theorem affineGradientFlow_velocity
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (p : M) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) I (affineGradientFlow (I := I) g hEnorm b p) t 1 =
      gradientFun (I := I) g b (affineGradientFlow (I := I) g hEnorm b p t) := by
  let c := affineGradientFlow (I := I) g hEnorm b p
  let v : TangentSpace I (c t) := mfderiv 𝓘(ℝ, ℝ) I c t 1
  let w : TangentSpace I (c t) := gradientFun (I := I) g b (c t)
  have hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm p (gradientFun (I := I) g b p)
  have hv : g.inner (c t) v v = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p (gradientFun (I := I) g b p) t).trans
      (hunit p)
  have hw : g.inner (c t) w w = 1 := hunit (c t)
  have hcross : g.inner (c t) w v = 1 := by
    have hd := deriv_comp_mfderiv_along I b c t
      (hb.mdifferentiable (by simp) (c t)) (hc.mdifferentiable (by simp) t)
    change deriv (fun s => b (c s)) t = mvfderiv (I := I) b (c t) v at hd
    rw [← inner_gradientFun (I := I) g b (c t) v] at hd
    exact hd.symm.trans (hasDerivAt_affineFunction_flow (I := I) g hEnorm hb hunit hH p t).deriv
  have hz : g.inner (c t) (v - w) (v - w) = 0 := by
    simp only [map_sub, sub_apply]
    rw [g.symm (c t) v w, hv, hw, hcross]
    ring
  have heq : v - w = 0 := by
    by_contra hne
    exact (ne_of_gt (g.pos (c t) (v - w) hne)) hz
  exact sub_eq_zero.mp heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineGradientFlow_velocity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineGradientFlow_velocity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineGradientFlow_velocity ``Submission.DifferentialGeometry.Geometry.Topology.affineGradientFlow_velocity

theorem affineGradientFlow_isMIntegralCurve
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (p : M) :
    IsMIntegralCurve (I := I) (affineGradientFlow (I := I) g hEnorm b p)
      (fun x => gradientFun (I := I) g b x) := by
  intro t
  have hc := (intrinsicGeodesic_contMDiff (I := I) g hEnorm p
    (gradientFun (I := I) g b p)).mdifferentiable (by simp) t
  have hL : mfderiv 𝓘(ℝ, ℝ) I (affineGradientFlow (I := I) g hEnorm b p) t =
      (1 : ℝ →L[ℝ] ℝ).smulRight
        (gradientFun (I := I) g b (affineGradientFlow (I := I) g hEnorm b p t)) := by
    apply ContinuousLinearMap.ext_ring
    change mfderiv 𝓘(ℝ, ℝ) I (affineGradientFlow (I := I) g hEnorm b p) t 1 =
      (1 : ℝ) • gradientFun (I := I) g b (affineGradientFlow (I := I) g hEnorm b p t)
    rw [one_smul]
    exact affineGradientFlow_velocity (I := I) g hEnorm hb hunit hH p t
  rw [← hL]
  exact hc.hasMFDerivAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineGradientFlow_isMIntegralCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineGradientFlow_isMIntegralCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineGradientFlow_isMIntegralCurve ``Submission.DifferentialGeometry.Geometry.Topology.affineGradientFlow_isMIntegralCurve

theorem affineGradientFlow_add
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (p : M) (s t : ℝ) :
    affineGradientFlow (I := I) g hEnorm b p (t + s) =
      affineGradientFlow (I := I) g hEnorm b (affineGradientFlow (I := I) g hEnorm b p s) t := by
  have h1 := affineGradientFlow_isMIntegralCurve (I := I) g hEnorm hb hunit hH
    (affineGradientFlow (I := I) g hEnorm b p s)
  have h2 := (affineGradientFlow_isMIntegralCurve (I := I) g hEnorm hb hunit hH p).comp_add s
  have h0 : affineGradientFlow (I := I) g hEnorm b
      (affineGradientFlow (I := I) g hEnorm b p s) 0 =
      (affineGradientFlow (I := I) g hEnorm b p ∘ (· + s)) 0 := by
    simp only [affineGradientFlow_zero, Function.comp_apply, zero_add]
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
    ((gradientFun_smooth (I := I) g hb).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)) h1 h2 h0
  exact (congrFun heq t).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineGradientFlow_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineGradientFlow_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineGradientFlow_add ``Submission.DifferentialGeometry.Geometry.Topology.affineGradientFlow_add

def affineFunctionZeroLevelEquiv
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) :
    ({p : M // b p = 0} × ℝ) ≃ M where
  toFun z := affineGradientFlow (I := I) g hEnorm b z.1.1 z.2
  invFun x := (⟨affineGradientFlow (I := I) g hEnorm b x (-b x), by
    rw [affineFunction_flow_eq_add (I := I) g hEnorm hb hunit hH, add_neg_cancel]⟩, b x)
  left_inv z := by
    rcases z with ⟨⟨y, hy⟩, t⟩
    apply Prod.ext
    · apply Subtype.ext
      change affineGradientFlow (I := I) g hEnorm b
        (affineGradientFlow (I := I) g hEnorm b y t)
        (-b (affineGradientFlow (I := I) g hEnorm b y t)) = y
      rw [affineFunction_flow_eq_add (I := I) g hEnorm hb hunit hH, hy, zero_add,
        ← affineGradientFlow_add (I := I) g hEnorm hb hunit hH, neg_add_cancel,
        affineGradientFlow_zero]
    · change b (affineGradientFlow (I := I) g hEnorm b y t) = t
      rw [affineFunction_flow_eq_add (I := I) g hEnorm hb hunit hH, hy, zero_add]
  right_inv x := by
    change affineGradientFlow (I := I) g hEnorm b
      (affineGradientFlow (I := I) g hEnorm b x (-b x)) (b x) = x
    rw [← affineGradientFlow_add (I := I) g hEnorm hb hunit hH, add_neg_cancel,
      affineGradientFlow_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelEquiv ``Submission.DifferentialGeometry.Geometry.Topology.affineFunctionZeroLevelEquiv

end DifferentialGeometry.Geometry.Topology

end
