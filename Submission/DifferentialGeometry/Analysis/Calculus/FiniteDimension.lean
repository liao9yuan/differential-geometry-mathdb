import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Function _root_.Module _root_.Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {D : Type*} [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : D → E →L[𝕜] F} {s : Set D} {x : D}

theorem differentiableWithinAt_clm_apply :
    DifferentiableWithinAt 𝕜 f s x ↔
      ∀ y, DifferentiableWithinAt 𝕜 (fun z => f z y) s x := by
  refine ⟨fun h y => h.clm_apply (differentiableWithinAt_const y), fun h => ?_⟩
  let d := _root_.Module.finrank 𝕜 E
  have hd : d = _root_.Module.finrank 𝕜 (Fin d → 𝕜) := (_root_.Module.finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← _root_.Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.differentiableAt.comp_differentiableWithinAt x
    (differentiableWithinAt_pi.mpr fun i => h _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `differentiableWithinAt_clm_apply then
    throwError "Refusing to shadow existing declaration differentiableWithinAt_clm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `differentiableWithinAt_clm_apply ``Submission.differentiableWithinAt_clm_apply

theorem differentiableAt_clm_apply :
    DifferentiableAt 𝕜 f x ↔ ∀ y, DifferentiableAt 𝕜 (fun z => f z y) x := by
  simp only [← differentiableWithinAt_univ, differentiableWithinAt_clm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `differentiableAt_clm_apply then
    throwError "Refusing to shadow existing declaration differentiableAt_clm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `differentiableAt_clm_apply ``Submission.differentiableAt_clm_apply

theorem differentiableOn_clm_apply :
    DifferentiableOn 𝕜 f s ↔ ∀ y, DifferentiableOn 𝕜 (fun z => f z y) s := by
  simp only [DifferentiableOn, differentiableWithinAt_clm_apply]
  exact ⟨fun h y x hx => h x hx y, fun h x hx y => h y x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `differentiableOn_clm_apply then
    throwError "Refusing to shadow existing declaration differentiableOn_clm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `differentiableOn_clm_apply ``Submission.differentiableOn_clm_apply

theorem differentiable_clm_apply :
    Differentiable 𝕜 f ↔ ∀ y, Differentiable 𝕜 (fun z => f z y) := by
  simp only [Differentiable, differentiableAt_clm_apply]
  exact forall_comm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `differentiable_clm_apply then
    throwError "Refusing to shadow existing declaration differentiable_clm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `differentiable_clm_apply ``Submission.differentiable_clm_apply

theorem hasDerivWithinAt_clm_apply
    {f : 𝕜 → E →L[𝕜] F} {f' : E →L[𝕜] F} {s : Set 𝕜} {x : 𝕜} :
    HasDerivWithinAt f f' s x ↔
      ∀ y, HasDerivWithinAt (fun t => f t y) (f' y) s x := by
  refine ⟨?_, ?_⟩
  · intro h y
    simpa only [map_zero, add_zero] using h.clm_apply (hasDerivWithinAt_const x s y)
  · intro h
    let e : (E →L[𝕜] F) ≃L[𝕜] Fin (_root_.Module.finrank 𝕜 E) → F :=
      ((ContinuousLinearEquiv.ofFinrankEq (_root_.Module.finrank_fin_fun 𝕜).symm).arrowCongr
        (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing _)
    have he : HasDerivWithinAt (fun t => e (f t)) (e f') s x :=
      hasDerivWithinAt_pi.mpr fun _ => h _
    have hback := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt x he
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hback

run_cmd do
  let env ← Lean.getEnv
  if env.contains `hasDerivWithinAt_clm_apply then
    throwError "Refusing to shadow existing declaration hasDerivWithinAt_clm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `hasDerivWithinAt_clm_apply ``Submission.hasDerivWithinAt_clm_apply

theorem hasDerivAt_clm_apply
    {f : 𝕜 → E →L[𝕜] F} {f' : E →L[𝕜] F} {x : 𝕜} :
    HasDerivAt f f' x ↔ ∀ y, HasDerivAt (fun t => f t y) (f' y) x := by
  simp only [← hasDerivWithinAt_univ, hasDerivWithinAt_clm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `hasDerivAt_clm_apply then
    throwError "Refusing to shadow existing declaration hasDerivAt_clm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `hasDerivAt_clm_apply ``Submission.hasDerivAt_clm_apply
