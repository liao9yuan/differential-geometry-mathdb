import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Function
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

set_option backward.isDefEq.respectTransparency false in



theorem mfderiv_comp_planeLinearEquiv (U : ℂ → M) (L : ℂ ≃L[ℝ] ℂ) (z : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U ∘ L) z =
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (L z)).comp L.toContinuousLinearMap := by
  have hL : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) L z :=
    L.differentiableAt.mdifferentiableAt
  by_cases hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (L z)
  · rw [mfderiv_comp z hU hL, mfderiv_eq_fderiv, L.hasFDerivAt.fderiv]
  · have hc : ¬ MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U ∘ L) z := by
      intro h
      have hi : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) L.symm (L z) :=
        L.symm.differentiableAt.mdifferentiableAt
      have h' : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U ∘ L) (L.symm (L z)) :=
        (L.symm_apply_apply z).symm ▸ h
      have heq : ((U ∘ L) ∘ L.symm) = U := by
        funext w
        simp only [Function.comp_apply, L.apply_symm_apply]
      exact hU (heq ▸ h'.comp (L z) hi)
    rw [mfderiv_zero_of_not_mdifferentiableAt hc, mfderiv_zero_of_not_mdifferentiableAt hU]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mfderiv_comp_planeLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mfderiv_comp_planeLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mfderiv_comp_planeLinearEquiv ``Submission.DifferentialGeometry.Geometry.mfderiv_comp_planeLinearEquiv



theorem diskMapPartial_comp_conj (U : ℂ → M) (z v : ℂ) :
    diskMapPartial (E := E) (U ∘ conj) z v = diskMapPartial (E := E) U (conj z) (conj v) :=
  congrArg (fun L : ℂ →L[ℝ] E => L v)
    (mfderiv_comp_planeLinearEquiv (E := E) U Complex.conjCLE z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapPartial_comp_conj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapPartial_comp_conj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapPartial_comp_conj ``Submission.DifferentialGeometry.Geometry.diskMapPartial_comp_conj


theorem diskMapPartial_comp_conj_one (U : ℂ → M) (z : ℂ) :
    diskMapPartial (E := E) (U ∘ conj) z 1 = diskMapPartial (E := E) U (conj z) 1 := by
  rw [diskMapPartial_comp_conj, map_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapPartial_comp_conj_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapPartial_comp_conj_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapPartial_comp_conj_one ``Submission.DifferentialGeometry.Geometry.diskMapPartial_comp_conj_one


theorem diskMapPartial_comp_conj_I (U : ℂ → M) (z : ℂ) :
    diskMapPartial (E := E) (U ∘ conj) z Complex.I = -diskMapPartial (E := E) U (conj z) Complex.I := by
  rw [diskMapPartial_comp_conj, Complex.conj_I]
  exact map_neg (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (conj z)) Complex.I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapPartial_comp_conj_I then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapPartial_comp_conj_I"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapPartial_comp_conj_I ``Submission.DifferentialGeometry.Geometry.diskMapPartial_comp_conj_I

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem DiskMapConformalAt.comp_conj (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {z : ℂ}
    (h : DiskMapConformalAt g U (conj z)) : DiskMapConformalAt g (U ∘ conj) z := by
  unfold DiskMapConformalAt at h ⊢
  simp only [Function.comp_apply]
  constructor
  · simpa only [diskMapPartial_comp_conj_one, diskMapPartial_comp_conj_I, map_neg,
      _root_.neg_apply, neg_eq_zero] using h.1
  · simpa only [diskMapPartial_comp_conj_one, diskMapPartial_comp_conj_I, map_neg,
      _root_.neg_apply, neg_neg] using h.2

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.DiskMapConformalAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskMapConformalAt.comp_conj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskMapConformalAt.comp_conj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskMapConformalAt.comp_conj ``Submission.DifferentialGeometry.Geometry.DiskMapConformalAt.comp_conj

end DifferentialGeometry.Geometry
