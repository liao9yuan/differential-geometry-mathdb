import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle
open _root_.Submission.DifferentialGeometry.Geometry
open scoped _root_.Manifold _root_.ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev CylinderI := (𝓡 2).prod (𝓘(ℝ, ℝ))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderI
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderI target :: scope.openDecls } }
local notation "sphereMetric" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance cylinderDeckDifferentialSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeckDifferentialSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeckDifferentialSphereDimension target :: scope.openDecls } }

private theorem cylinderDeck_two_coefficients {T t₀ t₁ S B L Q : ℝ}
    (hdifferent : t₀ ≠ t₁)
    (h₀ : 2 * (T - t₀) * S + L = 2 * (T - t₀) * B + Q)
    (h₁ : 2 * (T - t₁) * S + L = 2 * (T - t₁) * B + Q) :
    S = B ∧ L = Q := by
  have hfactor : (t₁ - t₀) * (S - B) = 0 := by nlinarith [h₀, h₁]
  have htime : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr hdifferent.symm
  have hsphere := sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left htime)
  refine ⟨hsphere, ?_⟩
  rw [hsphere] at h₀
  exact add_left_cancel h₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_two_coefficients
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_two_coefficients target :: scope.openDecls } }

variable (Phi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, CylinderI⟯ (SphereTwo × ℝ))
  {T t₀ t₁ : ℝ} (hdifferent : t₀ ≠ t₁)
  (hmetric : ∀ t : ℝ, t = t₀ ∨ t = t₁ →
    ∀ (p : SphereTwo × ℝ) (v w : TangentSpace (𝓡 2) p.1) (a c : ℝ),
      (2 * (T - t)) * (sphereMetric).inner (Phi p).1
          (mfderiv CylinderI CylinderI Phi p (v, a)).1
          (mfderiv CylinderI CylinderI Phi p (w, c)).1 +
        (mfderiv CylinderI CylinderI Phi p (v, a)).2 *
          (mfderiv CylinderI CylinderI Phi p (w, c)).2 =
      (2 * (T - t)) * (sphereMetric).inner p.1 v w + a * c)

include hdifferent hmetric

theorem cylinderDeck_mfderiv_block_inner (p : SphereTwo × ℝ)
    (v w : TangentSpace (𝓡 2) p.1) (a c : ℝ) :
    (sphereMetric).inner (Phi p).1
        (mfderiv CylinderI CylinderI Phi p (v, a)).1
        (mfderiv CylinderI CylinderI Phi p (w, c)).1 =
      (sphereMetric).inner p.1 v w ∧
    (mfderiv CylinderI CylinderI Phi p (v, a)).2 *
        (mfderiv CylinderI CylinderI Phi p (w, c)).2 = a * c := by
  exact cylinderDeck_two_coefficients hdifferent
    (hmetric t₀ (Or.inl rfl) p v w a c) (hmetric t₁ (Or.inr rfl) p v w a c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_block_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_block_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_block_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_block_inner

theorem cylinderDeck_mfderiv_preserves_factors (p : SphereTwo × ℝ)
    (v : TangentSpace (𝓡 2) p.1) (a : ℝ) :
    (mfderiv CylinderI CylinderI Phi p (v, 0)).2 = 0 ∧
      (mfderiv CylinderI CylinderI Phi p (0, a)).1 = 0 := by
  have hhorizontal := cylinderDeck_mfderiv_block_inner
    Phi hdifferent hmetric p v v 0 0
  have hvertical := cylinderDeck_mfderiv_block_inner
    Phi hdifferent hmetric p (0 : TangentSpace (𝓡 2) p.1)
      (0 : TangentSpace (𝓡 2) p.1) a a
  constructor
  · have hsquare : (mfderiv CylinderI CylinderI Phi p (v, 0)).2 *
        (mfderiv CylinderI CylinderI Phi p (v, 0)).2 = 0 := by
      simpa only [_root_.MulZeroClass.zero_mul] using hhorizontal.2
    exact mul_self_eq_zero.mp hsquare
  · have hinner : (sphereMetric).inner (Phi p).1
        (mfderiv CylinderI CylinderI Phi p (0, a)).1
        (mfderiv CylinderI CylinderI Phi p (0, a)).1 = 0 := by
      simpa only [map_zero, zero_apply] using hvertical.1
    by_contra hne
    have hpos := (sphereMetric).pos (Phi p).1
      (mfderiv CylinderI CylinderI Phi p (0, a)).1 hne
    rw [hinner] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_preserves_factors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_preserves_factors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_preserves_factors ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_preserves_factors

theorem cylinderDeck_mfderiv_block_diagonal (p : SphereTwo × ℝ)
    (v : TangentSpace (𝓡 2) p.1) (a : ℝ) :
    mfderiv CylinderI CylinderI Phi p (v, a) =
      ((mfderiv CylinderI CylinderI Phi p (v, 0)).1,
        (mfderiv CylinderI CylinderI Phi p (0, a)).2) := by
  obtain ⟨hhorizontal, hvertical⟩ := cylinderDeck_mfderiv_preserves_factors
    Phi hdifferent hmetric p v a
  have hp : (v, a) = (v, 0) + (0, a) := by
    ext <;> simp
  calc
    mfderiv CylinderI CylinderI Phi p (v, a) =
        mfderiv CylinderI CylinderI Phi p (v, 0) +
          mfderiv CylinderI CylinderI Phi p (0, a) := by
      rw [hp]
      exact (mfderiv CylinderI CylinderI Phi p).map_add (v, 0) (0, a)
    _ = _ := by
      apply Prod.ext
      · change (mfderiv CylinderI CylinderI Phi p (v, 0)).1 +
          (mfderiv CylinderI CylinderI Phi p (0, a)).1 =
            (mfderiv CylinderI CylinderI Phi p (v, 0)).1
        rw [hvertical, add_zero]
      · change (mfderiv CylinderI CylinderI Phi p (v, 0)).2 +
          (mfderiv CylinderI CylinderI Phi p (0, a)).2 =
            (mfderiv CylinderI CylinderI Phi p (0, a)).2
        rw [hhorizontal, zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_block_diagonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_block_diagonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_block_diagonal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_block_diagonal

theorem cylinderDeck_mfderiv_block_norms (p : SphereTwo × ℝ)
    (v : TangentSpace (𝓡 2) p.1) (a : ℝ) :
    Real.sqrt ((sphereMetric).inner (Phi p).1
        (mfderiv CylinderI CylinderI Phi p (v, 0)).1
        (mfderiv CylinderI CylinderI Phi p (v, 0)).1) =
      Real.sqrt ((sphereMetric).inner p.1 v v) ∧
    |(mfderiv CylinderI CylinderI Phi p (0, a)).2| = |a| := by
  have hhorizontal := cylinderDeck_mfderiv_block_inner
    Phi hdifferent hmetric p v v 0 0
  have hvertical := cylinderDeck_mfderiv_block_inner
    Phi hdifferent hmetric p (0 : TangentSpace (𝓡 2) p.1)
      (0 : TangentSpace (𝓡 2) p.1) a a
  refine ⟨congrArg Real.sqrt hhorizontal.1, ?_⟩
  apply (sq_eq_sq_iff_abs_eq_abs _ _).mp
  convert hvertical.2 using 1 <;> simp only [pow_two]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_block_norms then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_block_norms"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_block_norms ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_mfderiv_block_norms

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
