import Submission.DifferentialGeometry.Geometry.Comparison.Busemann.Support.SmoothDistanceLaplacian
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Riemannian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace


theorem laplacian_exp_mul_sub_one
    (g : SmoothRiemannianMetric I M) {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) (a : ℝ) (x : M) :
    laplacian (I := I) (LeviCivita (I := I) g) g
        (fun y => Real.exp (a * ρ y) - 1) x =
      a * Real.exp (a * ρ x) *
        (laplacian (I := I) (LeviCivita (I := I) g) g ρ x +
          a * g.inner x (gradientFun (I := I) g ρ x) (gradientFun (I := I) g ρ x)) := by
  let φ : ℝ → ℝ := fun t => Real.exp (a * t) - 1
  have hd (t : ℝ) : HasDerivAt φ (Real.exp (a * t) * a) t := by
    simpa only [mul_one] using! (((hasDerivAt_id t).const_mul a).exp.sub_const 1)
  have hprime : deriv φ = fun t => Real.exp (a * t) * a := funext fun t => (hd t).deriv
  have hsecond : HasDerivAt (deriv φ) (Real.exp (a * ρ x) * a * a) (ρ x) := by
    rw [hprime]
    simpa only [mul_one] using! (((hasDerivAt_id (ρ x)).const_mul a).exp.mul_const a)
  have h := laplacian_comp (I := I) (LeviCivita (I := I) g) g
    (fun t => (hd t).differentiableAt) hsecond.differentiableAt
    (fun y => hρ.contMDiffAt.mdifferentiableAt (by simp))
    (gradientFun_mdiffAt (I := I) g hρ x)
  change laplacian (I := I) (LeviCivita (I := I) g) g
    (fun y => Real.exp (a * ρ y) - 1) x = _ at h
  rw [hsecond.deriv, hprime] at h
  rw [h]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.laplacian_exp_mul_sub_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.laplacian_exp_mul_sub_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.laplacian_exp_mul_sub_one ``Submission.DifferentialGeometry.Geometry.Topology.laplacian_exp_mul_sub_one

theorem exists_positive_laplacian_exponential [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) {K : Set M} (hK : IsCompact K)
    (hgrad : ∀ x ∈ K, gradientFun (I := I) g ρ x ≠ 0) :
    ∃ a : ℝ, 0 < a ∧
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => Real.exp (a * ρ y) - 1) ∧
      ∀ x ∈ K, 0 < laplacian (I := I) (LeviCivita (I := I) g) g
        (fun y => Real.exp (a * ρ y) - 1) x := by
  have hsmooth (a : ℝ) :
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => Real.exp (a * ρ y) - 1) :=
    ((Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hρ)).sub contMDiff_const)
  by_cases hne : K.Nonempty
  · let G : M → ℝ := fun x =>
      g.inner x (gradientFun (I := I) g ρ x) (gradientFun (I := I) g ρ x)
    let Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨fun x => gradientFun (I := I) g ρ x, gradientFun_smooth (I := I) g hρ⟩
    have hGcont : Continuous G := TangentBundle.continuous_g_inner_of_smooth_sections g Z Z
    obtain ⟨z, hz, hzmin⟩ := hK.exists_isMinOn hne hGcont.continuousOn
    have hm : 0 < G z := g.pos z _ (hgrad z hz)
    have hLap : Continuous (laplacian (I := I) (LeviCivita (I := I) g) g ρ) := by
      have heq : laplacian (I := I) (LeviCivita (I := I) g) g ρ =
          ΔG (I := I) g ⟨ρ, hρ⟩ :=
        funext fun x => laplacian_levi_eq (I := I) g hρ x
      rw [heq]
      exact (Δ_g_contMDiff (I := I) g ⟨ρ, hρ⟩).continuous
    obtain ⟨A, hA⟩ := hK.bddBelow_image hLap.continuousOn
    let a : ℝ := (_root_.Max.max (-A) 0 + 1) / G z
    have ha : 0 < a := div_pos
      (add_pos_of_nonneg_of_pos (le_max_right (-A) 0) zero_lt_one) hm
    have ham : a * G z = _root_.Max.max (-A) 0 + 1 := div_mul_cancel₀ _ hm.ne'
    refine ⟨a, ha, hsmooth a, fun x hx => ?_⟩
    rw [laplacian_exp_mul_sub_one (I := I) g hρ a x]
    have hGx : G z ≤ G x := hzmin hx
    have hAx : A ≤ laplacian (I := I) (LeviCivita (I := I) g) g ρ x :=
      hA (_root_.Set.mem_image_of_mem _ hx)
    have hsum : 0 < laplacian (I := I) (LeviCivita (I := I) g) g ρ x + a * G x := by
      have hmul := mul_le_mul_of_nonneg_left hGx ha.le
      linarith [le_max_left (-A) 0]
    exact mul_pos (mul_pos ha (Real.exp_pos _)) hsum
  · exact ⟨1, zero_lt_one, hsmooth 1, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_positive_laplacian_exponential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_positive_laplacian_exponential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_positive_laplacian_exponential ``Submission.DifferentialGeometry.Geometry.Topology.exists_positive_laplacian_exponential

end DifferentialGeometry.Geometry.Topology

end
