import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem mfderivWithin_comp_prod_id {F : ℝ × ℝ → M} {J : Set ℝ}
    {φ : ℝ → ℝ} {t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (hF : MDifferentiableWithinAt 𝓘(ℝ, ℝ × ℝ) I F (_root_.Set.univ ×ˢ J) (φ t, t))
    (hφ : DifferentiableWithinAt ℝ φ J t) :
    mfderivWithin 𝓘(ℝ, ℝ) I (fun s => F (φ s, s)) J t (1 : ℝ) =
      (derivWithin φ J t) • mfderiv 𝓘(ℝ, ℝ) I (fun x => F (x, t)) (φ t) (1 : ℝ) +
        mfderivWithin 𝓘(ℝ, ℝ) I (fun s => F (φ t, s)) J t (1 : ℝ) := by
  let A : (ℝ × ℝ) →L[ℝ] TangentSpace I (F (φ t, t)) :=
    mfderivWithin 𝓘(ℝ, ℝ × ℝ) I F (_root_.Set.univ ×ˢ J) (φ t, t)
  have hpair : HasFDerivWithinAt (fun s : ℝ => (φ s, s))
      ((fderivWithin ℝ φ J t).prod (ContinuousLinearMap.id ℝ ℝ)) J t :=
    hφ.hasFDerivWithinAt.prodMk (hasFDerivWithinAt_id t J)
  have hchain := mfderivWithin_comp (f := fun s : ℝ => (φ s, s)) (g := F) t hF
    hpair.hasMFDerivWithinAt.mdifferentiableWithinAt
    (fun s hs => ⟨mem_univ _, hs⟩) hJ.uniqueMDiffWithinAt
  have hpairderiv : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) (fun s : ℝ => (φ s, s)) J t =
      ((fderivWithin ℝ φ J t).prod (ContinuousLinearMap.id ℝ ℝ)) :=
    hpair.hasMFDerivWithinAt.mfderivWithin hJ.uniqueMDiffWithinAt
  have htime : mfderivWithin 𝓘(ℝ, ℝ) I (fun s => F (φ t, s)) J t (1 : ℝ) = A (0, 1) := by
    have hp : HasFDerivWithinAt (fun s : ℝ => (φ t, s))
        ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)) J t :=
      (hasFDerivWithinAt_const (φ t) t J).prodMk (hasFDerivWithinAt_id t J)
    have hh := mfderivWithin_comp (f := fun s : ℝ => (φ t, s)) (g := F) t hF
      hp.hasMFDerivWithinAt.mdifferentiableWithinAt
      (fun s hs => ⟨mem_univ _, hs⟩) hJ.uniqueMDiffWithinAt
    change mfderivWithin 𝓘(ℝ, ℝ) I (F ∘ fun s : ℝ => (φ t, s)) J t (1 : ℝ) = _
    rw [hh, hp.hasMFDerivWithinAt.mfderivWithin hJ.uniqueMDiffWithinAt]
    rfl
  have hspace : mfderiv 𝓘(ℝ, ℝ) I (fun x => F (x, t)) (φ t) (1 : ℝ) = A (1, 0) := by
    have hp : HasFDerivWithinAt (fun s : ℝ => (s, t))
        ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)) _root_.Set.univ (φ t) :=
      (hasFDerivWithinAt_id (φ t) _root_.Set.univ).prodMk (hasFDerivWithinAt_const t (φ t) _root_.Set.univ)
    have hh := mfderivWithin_comp (f := fun s : ℝ => (s, t)) (g := F) (φ t) hF
      hp.hasMFDerivWithinAt.mdifferentiableWithinAt
      (fun s _ => ⟨mem_univ _, ht⟩) (uniqueDiffWithinAt_univ.uniqueMDiffWithinAt)
    change mfderiv 𝓘(ℝ, ℝ) I (F ∘ fun s : ℝ => (s, t)) (φ t) (1 : ℝ) = _
    rw [← mfderivWithin_univ, hh,
      hp.hasMFDerivWithinAt.mfderivWithin uniqueDiffWithinAt_univ.uniqueMDiffWithinAt]
    rfl
  change mfderivWithin 𝓘(ℝ, ℝ) I (F ∘ fun s : ℝ => (φ s, s)) J t (1 : ℝ) = _
  rw [hchain, hpairderiv, htime, hspace]
  change A (derivWithin φ J t, 1) = derivWithin φ J t • A (1, 0) + A (0, 1)
  have hsplit : (derivWithin φ J t, (1 : ℝ)) =
      derivWithin φ J t • ((1, 0) : ℝ × ℝ) + (0, 1) := by simp
  rw [hsplit, map_add, map_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.mfderivWithin_comp_prod_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.mfderivWithin_comp_prod_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.mfderivWithin_comp_prod_id ``Submission.DifferentialGeometry.mfderivWithin_comp_prod_id

end DifferentialGeometry
