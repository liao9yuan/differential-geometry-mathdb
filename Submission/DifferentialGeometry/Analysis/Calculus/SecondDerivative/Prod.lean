import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.NormNum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

variable {𝕜 P E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem fderiv_const_prod {f : P × E → F} {p : P} {x : E}
    (hf : DifferentiableAt 𝕜 f (p, x)) :
    fderiv 𝕜 (fun y => f (p, y)) x =
      (fderiv 𝕜 f (p, x)).comp (ContinuousLinearMap.inr 𝕜 P E) := by
  exact (hf.hasFDerivAt.comp x
    ((hasFDerivAt_const p x).prodMk (hasFDerivAt_id x))).fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv_const_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv_const_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv_const_prod ``Submission.DifferentialGeometry.Analysis.fderiv_const_prod

theorem fderiv_prod_const {f : P × E → F} {p : P} {x : E}
    (hf : DifferentiableAt 𝕜 f (p, x)) :
    fderiv 𝕜 (fun y => f (y, x)) p =
      (fderiv 𝕜 f (p, x)).comp (ContinuousLinearMap.inl 𝕜 P E) := by
  exact (hf.hasFDerivAt.comp p
    ((hasFDerivAt_id p).prodMk (hasFDerivAt_const x p))).fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv_prod_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv_prod_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv_prod_const ``Submission.DifferentialGeometry.Analysis.fderiv_prod_const

theorem fderiv_fderiv_const_prod_apply {phi : P × E → F} {t : P} {x : E}
    (hphi : ContDiffAt 𝕜 2 phi (t, x)) (v w : E) :
    fderiv 𝕜 (fderiv 𝕜 (fun y => phi (t, y))) x v w =
      fderiv 𝕜 (fderiv 𝕜 phi) (t, x) (0, v) (0, w) := by
  let L : E →L[𝕜] P × E := ContinuousLinearMap.inr 𝕜 P E
  have heq : fderiv 𝕜 (fun y => phi (t, y)) =ᶠ[𝓝 x]
      fun y => (fderiv 𝕜 phi (t, y)).comp L := by
    have hc : ContinuousAt (fun y : E => (t, y)) x := continuousAt_const.prodMk continuousAt_id
    filter_upwards [hc.tendsto.eventually (hphi.eventually (by norm_num))] with y hy
    exact fderiv_const_prod (hy.differentiableAt (by norm_num))
  have hd := ((hphi.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).hasFDerivAt.comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  have hdd := hd.clm_comp (hasFDerivAt_const L x)
  simp only [Function.comp_def] at hdd
  rw [heq.fderiv_eq, hdd.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.inr_apply, map_zero, zero_add, L]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv_fderiv_const_prod_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv_fderiv_const_prod_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv_fderiv_const_prod_apply ``Submission.DifferentialGeometry.Analysis.fderiv_fderiv_const_prod_apply

theorem fderiv_fderiv_prod_const_apply {phi : E × P → F} {t : P} {x : E}
    (hphi : ContDiffAt 𝕜 2 phi (x, t)) (v w : E) :
    fderiv 𝕜 (fderiv 𝕜 (fun y => phi (y, t))) x v w =
      fderiv 𝕜 (fderiv 𝕜 phi) (x, t) (v, 0) (w, 0) := by
  let L : E →L[𝕜] E × P := ContinuousLinearMap.inl 𝕜 E P
  have heq : fderiv 𝕜 (fun y => phi (y, t)) =ᶠ[𝓝 x]
      fun y => (fderiv 𝕜 phi (y, t)).comp L := by
    have hc : ContinuousAt (fun y : E => (y, t)) x := continuousAt_id.prodMk continuousAt_const
    filter_upwards [hc.tendsto.eventually (hphi.eventually (by norm_num))] with y hy
    exact fderiv_prod_const (hy.differentiableAt (by norm_num))
  have hd := ((hphi.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).hasFDerivAt.comp x
      ((hasFDerivAt_id (𝕜 := 𝕜) x).prodMk (hasFDerivAt_const t x))
  have hdd := hd.clm_comp (hasFDerivAt_const L x)
  simp only [Function.comp_def, id_eq] at hdd
  rw [heq.fderiv_eq, hdd.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.inl_apply, map_zero, zero_add, L]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv_fderiv_prod_const_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv_fderiv_prod_const_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv_fderiv_prod_const_apply ``Submission.DifferentialGeometry.Analysis.fderiv_fderiv_prod_const_apply

end DifferentialGeometry.Analysis
