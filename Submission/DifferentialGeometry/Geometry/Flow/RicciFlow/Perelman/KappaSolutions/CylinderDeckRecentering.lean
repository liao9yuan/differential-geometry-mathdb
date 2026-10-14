import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderDeckClassification
import Mathlib.Analysis.Calculus.FDeriv.Add

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
private abbrev CylinderI := (𝓡 2).prod (𝓘(ℝ, ℝ))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderI
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderI target :: scope.openDecls } }
local notation "OrthogonalThree" => SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient
local notation "sphereMetric" => roundMetric (E := SphereAmbient) (n := 2)
local notation "antipodal" => sphereDiffeo (n := 2)
  (LinearIsometryEquiv.neg ℝ : OrthogonalThree)

private local instance cylinderRecenteringSphereDimension :
    Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderRecenteringSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderRecenteringSphereDimension target :: scope.openDecls } }

private def cylinderRecentering_lineTranslation (c : ℝ) : ℝ ≃ₘ[ℝ] ℝ where
  toFun s := s + c
  invFun s := s - c
  left_inv s := add_sub_cancel_right s c
  right_inv s := sub_add_cancel s c
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderRecentering_lineTranslation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderRecentering_lineTranslation target :: scope.openDecls } }


def cylinderLineTranslation (c : ℝ) :
    (SphereTwo × ℝ) ≃ₘ⟮CylinderI, CylinderI⟯ (SphereTwo × ℝ) :=
  (Diffeomorph.refl (𝓡 2) SphereTwo ∞).prodCongr (cylinderRecentering_lineTranslation c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation


theorem cylinderLineTranslation_apply (c : ℝ) (p : SphereTwo × ℝ) :
    cylinderLineTranslation c p = (p.1, p.2 + c) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation_apply


theorem mfderiv_cylinderLineTranslation (c : ℝ) (x : SphereTwo) (s : ℝ)
    (v : TangentSpace (𝓡 2) x) (a : ℝ) :
    mfderiv CylinderI CylinderI (cylinderLineTranslation c) (x, s) (v, a) =
      (v, a) := by
  have hline : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (cylinderRecentering_lineTranslation c) s =
      ContinuousLinearMap.id ℝ ℝ := by
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => r + c) s = _
    rw [mfderiv_eq_fderiv, fderiv_add_const]
    exact fderiv_id
  change mfderiv CylinderI CylinderI
    (Prod.map (id : SphereTwo → SphereTwo) (cylinderRecentering_lineTranslation c))
      (x, s) (v, a) = _
  rw [mfderiv_prodMap mdifferentiableAt_id
    ((cylinderRecentering_lineTranslation c).mdifferentiable (by decide) s),
    mfderiv_id, hline]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mfderiv_cylinderLineTranslation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mfderiv_cylinderLineTranslation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mfderiv_cylinderLineTranslation ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mfderiv_cylinderLineTranslation

section FixedCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

theorem cylinderLineTranslation_trans_pullback
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (g t)).inner (Psi (x, s))
          (mfderiv CylinderI I Psi (x, s) (v, a))
          (mfderiv CylinderI I Psi (x, s) (w, b)) =
        (2 * (T - t)) * (sphereMetric).inner x v w + a * b)
    (c : ℝ) :
    ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (g t)).inner
          (((cylinderLineTranslation c).trans Psi) (x, s))
          (mfderiv CylinderI I ((cylinderLineTranslation c).trans Psi) (x, s) (v, a))
          (mfderiv CylinderI I ((cylinderLineTranslation c).trans Psi) (x, s) (w, b)) =
        (2 * (T - t)) * (sphereMetric).inner x v w + a * b := by
  have hderiv (x : SphereTwo) (s : ℝ) (v : TangentSpace (𝓡 2) x) (a : ℝ) :
      mfderiv CylinderI I ((cylinderLineTranslation c).trans Psi) (x, s) (v, a) =
        mfderiv CylinderI I Psi (x, s + c) (v, a) := by
    change mfderiv CylinderI I
      ((Psi : SphereTwo × ℝ → UniversalCover M) ∘ (cylinderLineTranslation c))
        (x, s) (v, a) = _
    rw [mfderiv_comp_apply (x, s)
      (Psi.mdifferentiable (by decide) (cylinderLineTranslation c (x, s)))
      ((cylinderLineTranslation c).mdifferentiable (by decide) (x, s)) (v, a),
      mfderiv_cylinderLineTranslation, cylinderLineTranslation_apply]
    rfl
  intro t ht x s v w a b
  change (UniversalCover.liftedMetric (I := I) (g t)).inner (Psi (x, s + c))
    (mfderiv CylinderI I ((cylinderLineTranslation c).trans Psi) (x, s) (v, a))
    (mfderiv CylinderI I ((cylinderLineTranslation c).trans Psi) (x, s) (w, b)) = _
  rw [hderiv, hderiv]
  exact hproduct t ht x (s + c) v w a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation_trans_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation_trans_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation_trans_pullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation_trans_pullback

omit [IsManifold I ∞ M] in
theorem cylinderDeck_recenter_fibres
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M) (c : ℝ)
    (hfibres : ∀ p q : SphereTwo × ℝ,
      UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
        q = p ∨ q = (antipodal p.1, 2 * c - p.2)) :
    ∀ p q : SphereTwo × ℝ,
      UniversalCover.proj (((cylinderLineTranslation c).trans Psi) p) =
        UniversalCover.proj (((cylinderLineTranslation c).trans Psi) q) ↔
          q = p ∨ q = (antipodal p.1, -p.2) := by
  intro p q
  change UniversalCover.proj (Psi (p.1, p.2 + c)) =
    UniversalCover.proj (Psi (q.1, q.2 + c)) ↔ _
  rw [hfibres]
  constructor
  · rintro (h | h)
    · left
      apply Prod.ext
      · simpa only using congrArg (fun z : SphereTwo × ℝ => z.1) h
      · have hs := congrArg (fun z : SphereTwo × ℝ => z.2) h
        change q.2 + c = p.2 + c at hs
        linarith
    · right
      apply Prod.ext
      · simpa only using congrArg (fun z : SphereTwo × ℝ => z.1) h
      · have hs := congrArg (fun z : SphereTwo × ℝ => z.2) h
        change q.2 + c = 2 * c - (p.2 + c) at hs
        change q.2 = -p.2
        linarith
  · rintro (h | h)
    · subst q
      exact Or.inl rfl
    · right
      rw [h]
      apply Prod.ext
      · rfl
      · change -p.2 + c = 2 * c - (p.2 + c)
        ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_recenter_fibres then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_recenter_fibres"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_recenter_fibres ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_recenter_fibres

omit [IsManifold I ∞ M] in
theorem cylinderDeck_recenter_surjective
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (hsurjective : Function.Surjective
      (fun p : SphereTwo × ℝ => UniversalCover.proj (Psi p))) (c : ℝ) :
    Function.Surjective (fun p : SphereTwo × ℝ =>
      UniversalCover.proj (((cylinderLineTranslation c).trans Psi) p)) :=
  hsurjective.comp (cylinderLineTranslation c).surjective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_recenter_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_recenter_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_recenter_surjective ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDeck_recenter_surjective

end FixedCover

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
