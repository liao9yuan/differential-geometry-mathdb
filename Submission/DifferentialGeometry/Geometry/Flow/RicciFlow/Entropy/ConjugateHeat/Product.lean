import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.GradientIdentities
import Submission.DifferentialGeometry.Geometry.Operator.Family.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem potential_grad_at
    (g : SmoothRiemannianMetric I M) (n : ℕ) {tau : ℝ}
    {u : M → ℝ} {x : M}
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x)
    (hpos : 0 < u x) (htau : 0 < tau) :
    gradientFun g (perelmanPotential n tau u) x =
      (-(u x)⁻¹) • gradientFun g u x := by
  let p := perelmanDensityPrefactor n tau
  have hp : 0 < p := prefactor_pos n htau
  have hphi : HasDerivAt (fun z : ℝ => -Real.log (z / p))
      (-(u x)⁻¹) (u x) := by
    have h := (((hasDerivAt_id (u x)).div_const p).log
      (div_ne_zero hpos.ne' hp.ne')).neg
    apply h.congr_deriv
    simp only [id_eq]
    field_simp [hpos.ne', hp.ne']
  exact gradientFun_comp g hphi.differentiableAt hu |>.trans (by rw [hphi.deriv])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.potential_grad_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.potential_grad_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.potential_grad_at ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.potential_grad_at

theorem conjugate_heat_mul_eq_potential_drift
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (R A u : ℝ → M → ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) (x : M)
    (hA : DifferentiableAt ℝ (fun s => A s x) t)
    (hu : HasDerivAt (fun s => u s x)
      (laplacianAt G t (u t) x - R t x * u t x) t)
    (hAs : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (A t) x)
    (hus : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (u t) x)
    (hpos : 0 < u t x) :
    deriv (fun s => A s x * u s x) t -
        laplacianAt G t (fun y => A t y * u t y) x +
        R t x * (A t x * u t x) =
      u t x * (deriv (fun s => A s x) t - laplacianAt G t (A t) x +
        2 * (G.metric t).inner x
          (gradientAt G t (perelmanPotential n t (u t)) x)
          (gradientAt G t (A t) x)) := by
  have hAd : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (A t) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
      (hAs.of_le (by simp))).mono fun y hy => hy.mdifferentiableAt (by simp)
  have hud : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
      (hus.of_le (by simp))).mono fun y hy => hy.mdifferentiableAt (by simp)
  have hAg := (gradientFun_contMDiffAt_one (G.metric t) hAs).mdifferentiableAt (by simp)
  have hug := (gradientFun_contMDiffAt_one (G.metric t) hus).mdifferentiableAt (by simp)
  have hlap := laplacian_mul_at (G.connection t) (G.metric t) hAd hud hAg hug
  rw [deriv_fun_mul hA hu.differentiableAt, hu.deriv]
  change _ - laplacian (G.connection t) (G.metric t) _ x + _ = _
  rw [hlap]
  simp only [gradientAt, potential_grad_at (G.metric t) n (hus.mdifferentiableAt (by simp)) hpos ht,
    map_smul, smul_apply, smul_eq_mul]
  rw [(G.metric t).symm x (gradientFun (G.metric t) (u t) x)
    (gradientFun (G.metric t) (A t) x)]
  unfold laplacianAt
  field_simp [hpos.ne']
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conjugate_heat_mul_eq_potential_drift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conjugate_heat_mul_eq_potential_drift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conjugate_heat_mul_eq_potential_drift ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conjugate_heat_mul_eq_potential_drift

end DifferentialGeometry.PDE.RicciFlow.Entropy
