import Submission.DifferentialGeometry.Analysis.Calculus.Periodic.Immersion
import Submission.DifferentialGeometry.Analysis.Calculus.ProdWithin
import Submission.DifferentialGeometry.Analysis.Calculus.TimeJet.SpatialDerivatives
import Submission.DifferentialGeometry.Topology.LoopSpace.Regular
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

private theorem periodic_deriv_circle {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : AddCircle (1 : ℝ) → F) :
    Function.Periodic (deriv (fun r : ℝ => c (r : AddCircle (1 : ℝ)))) 1 := by
  simpa only [iteratedDeriv_one] using
    DifferentialGeometry.Topology.periodic_iteratedDeriv (n := 1)
      (f := fun r : ℝ => c (r : AddCircle (1 : ℝ))) (T := 1) (by
        intro r
        simp only [AddCircle.coe_add_period])

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.periodic_deriv_circle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.periodic_deriv_circle target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem contMDiff_loop_family_slice
    (γ : ℝ × AddCircle (1 : ℝ) → M) {J : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ (p.2, (p.1 : AddCircle (1 : ℝ)))) (_root_.Set.univ ×ˢ J))
    {t : ℝ} (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun r : ℝ => γ (t, (r : AddCircle (1 : ℝ)))) := by
  apply contMDiffOn_univ.mp
  exact hγ.comp (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffOn
    (fun r _ => ⟨mem_univ r, ht⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.contMDiff_loop_family_slice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.contMDiff_loop_family_slice target :: scope.openDecls } }

theorem deriv_loop_family_comp (e : M → F) (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    (γ : ℝ × AddCircle (1 : ℝ) → M) {J : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ (p.2, (p.1 : AddCircle (1 : ℝ)))) (_root_.Set.univ ×ˢ J)) {t : ℝ} (ht : t ∈ J) (r : ℝ) :
    deriv (fun s : ℝ => e (γ (t, (s : AddCircle (1 : ℝ))))) r =
      mfderiv I 𝓘(ℝ, F) e (γ (t, (r : AddCircle (1 : ℝ))))
        (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γ (t, (s : AddCircle (1 : ℝ)))) r (1 : ℝ)) := by
  have hh := mfderiv_comp_apply r (he.mdifferentiableAt (by simp))
    ((contMDiff_loop_family_slice γ hγ ht).mdifferentiableAt (by simp)) (1 : ℝ)
  rw [mfderiv_eq_fderiv] at hh
  exact hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.deriv_loop_family_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.deriv_loop_family_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.deriv_loop_family_comp ``Submission.DifferentialGeometry.Topology.deriv_loop_family_comp

theorem norm_deriv_loop_family_sub_le_iteratedFDerivWithin_one
    (e : M → F) (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    (γ Γ : ℝ × AddCircle (1 : ℝ) → M) {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ (p.2, (p.1 : AddCircle (1 : ℝ)))) (_root_.Set.univ ×ˢ _root_.Set.Icc a b))
    (hΓ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => Γ (p.2, (p.1 : AddCircle (1 : ℝ)))) (_root_.Set.univ ×ˢ _root_.Set.Icc a b))
    {t : ℝ} (ht : t ∈ _root_.Set.Icc a b) (r : ℝ) :
    ‖deriv (fun s : ℝ => e (Γ (t, (s : AddCircle (1 : ℝ))))) r -
      deriv (fun s : ℝ => e (γ (t, (s : AddCircle (1 : ℝ))))) r‖ ≤
      ‖iteratedFDerivWithin ℝ 1
          (fun q : ℝ × ℝ => e (Γ (q.2, (q.1 : AddCircle (1 : ℝ)))))
          (_root_.Set.univ ×ˢ _root_.Set.Icc a b) (r, t) -
        iteratedFDerivWithin ℝ 1
          (fun q : ℝ × ℝ => e (γ (q.2, (q.1 : AddCircle (1 : ℝ)))))
          (_root_.Set.univ ×ˢ _root_.Set.Icc a b) (r, t)‖ := by
  let f : ℝ × ℝ → F := fun q => e (γ (q.2, (q.1 : AddCircle (1 : ℝ))))
  let g : ℝ × ℝ → F := fun q => e (Γ (q.2, (q.1 : AddCircle (1 : ℝ))))
  have hf : ContDiffOn ℝ ∞ f (_root_.Set.univ ×ˢ _root_.Set.Icc a b) := contMDiffOn_iff_contDiffOn.mp
    ((he.contMDiffOn (s := _root_.Set.univ)).comp hγ (fun _ _ => _root_.Set.mem_univ _))
  have hg : ContDiffOn ℝ ∞ g (_root_.Set.univ ×ˢ _root_.Set.Icc a b) := contMDiffOn_iff_contDiffOn.mp
    ((he.contMDiffOn (s := _root_.Set.univ)).comp hΓ (fun _ _ => _root_.Set.mem_univ _))
  have huniq : UniqueDiffWithinAt ℝ (_root_.Set.univ ×ˢ _root_.Set.Icc a b) (r, t) :=
    (uniqueDiffOn_univ.prod (uniqueDiffOn_Icc hab)) (r, t) ⟨mem_univ _, ht⟩
  change ‖deriv (fun s => g (s, t)) r - deriv (fun s => f (s, t)) r‖ ≤ _
  have hgd := DifferentialGeometry.Analysis.Calculus.derivWithin_prod_fst_of_hasFDerivWithinAt g _
    (show t ∈ _root_.Set.Icc a b from ht) uniqueDiffWithinAt_univ
    ((hg (r, t) ⟨mem_univ _, ht⟩).differentiableWithinAt (by simp)).hasFDerivWithinAt
  have hfd := DifferentialGeometry.Analysis.Calculus.derivWithin_prod_fst_of_hasFDerivWithinAt f _
    (show t ∈ _root_.Set.Icc a b from ht) uniqueDiffWithinAt_univ
    ((hf (r, t) ⟨mem_univ _, ht⟩).differentiableWithinAt (by simp)).hasFDerivWithinAt
  rw [derivWithin_univ] at hgd hfd
  rw [hgd, hfd]
  have hdist := dist_iteratedFDerivWithin_one (𝕜 := ℝ) g f huniq huniq
  rw [dist_eq_norm, dist_eq_norm] at hdist
  rw [hdist]
  have hb := ContinuousLinearMap.le_opNorm
    (fderivWithin ℝ g (_root_.Set.univ ×ˢ _root_.Set.Icc a b) (r, t) -
      fderivWithin ℝ f (_root_.Set.univ ×ˢ _root_.Set.Icc a b) (r, t)) ((1 : ℝ), (0 : ℝ))
  simpa only [sub_apply, Prod.norm_def, _root_.NormOneClass.norm_one, norm_zero,
    max_eq_left zero_le_one, mul_one] using hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.norm_deriv_loop_family_sub_le_iteratedFDerivWithin_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.norm_deriv_loop_family_sub_le_iteratedFDerivWithin_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.norm_deriv_loop_family_sub_le_iteratedFDerivWithin_one ``Submission.DifferentialGeometry.Topology.norm_deriv_loop_family_sub_le_iteratedFDerivWithin_one

theorem exists_loop_family_immersion_separation_radius
    (e : M → F) (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    (heinj : ∀ p, Function.Injective (mfderiv I 𝓘(ℝ, F) e p))
    (γ : ℝ × AddCircle (1 : ℝ) → M) {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ (p.2, (p.1 : AddCircle (1 : ℝ)))) (_root_.Set.univ ×ˢ _root_.Set.Icc a b))
    (hi : ∀ r t, t ∈ _root_.Set.Icc a b →
      mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γ (t, (s : AddCircle (1 : ℝ)))) r (1 : ℝ) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ Γ : ℝ × AddCircle (1 : ℝ) → M,
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
          (fun p : ℝ × ℝ => Γ (p.2, (p.1 : AddCircle (1 : ℝ)))) (_root_.Set.univ ×ˢ _root_.Set.Icc a b) →
        (∀ q ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b,
          ‖iteratedFDerivWithin ℝ 1
              (fun p : ℝ × ℝ => e (Γ (p.2, (p.1 : AddCircle (1 : ℝ))))) (_root_.Set.univ ×ˢ _root_.Set.Icc a b) q -
            iteratedFDerivWithin ℝ 1
              (fun p : ℝ × ℝ => e (γ (p.2, (p.1 : AddCircle (1 : ℝ)))))
              (_root_.Set.univ ×ˢ _root_.Set.Icc a b) q‖ < ε) →
        (∀ r t, t ∈ _root_.Set.Icc a b →
          mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => Γ (t, (s : AddCircle (1 : ℝ)))) r (1 : ℝ) ≠ 0) ∧
        ∀ t ∈ _root_.Set.Icc a b, ∀ z w : AddCircle (1 : ℝ),
          z ≠ w → Γ (t, z) = Γ (t, w) → δ ≤ _root_.Dist.dist z w := by
  let c : _root_.Set.Icc a b → AddCircle (1 : ℝ) → F := fun t z => e (γ (t, z))
  let hp (t : _root_.Set.Icc a b) := periodic_deriv_circle (c t)
  let v : _root_.Set.Icc a b → AddCircle (1 : ℝ) → F := fun t => (hp t).lift
  have hF : ContDiffOn ℝ ∞
      (fun q : ℝ × ℝ => e (γ (q.2, (q.1 : AddCircle (1 : ℝ))))) (_root_.Set.univ ×ˢ _root_.Set.Icc a b) :=
    contMDiffOn_iff_contDiffOn.mp
      ((he.contMDiffOn (s := _root_.Set.univ)).comp hγ (fun _ _ => _root_.Set.mem_univ _))
  have hvreal : Continuous (fun p : _root_.Set.Icc a b × ℝ =>
      deriv (fun s : ℝ => c p.1 (s : AddCircle (1 : ℝ))) p.2) :=
    (DifferentialGeometry.Analysis.contDiffOn_deriv_fst isOpen_univ
      (uniqueDiffOn_Icc hab) hF).continuousOn.comp_continuous
        (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
        (fun p => ⟨mem_univ _, p.1.2⟩)
  have hv : Continuous (fun p : _root_.Set.Icc a b × AddCircle (1 : ℝ) => v p.1 p.2) :=
    DifferentialGeometry.Topology.continuous_periodic_family hvreal hp
  have hcderiv (t : _root_.Set.Icc a b) (r : ℝ) : HasDerivAt (fun s : ℝ => c t (s : AddCircle (1 : ℝ)))
      (v t (r : AddCircle (1 : ℝ))) r := by
    exact ((he.comp (contMDiff_loop_family_slice γ hγ t.2)).contDiff.differentiable
      (by simp) r).hasDerivAt
  have hvne (t : _root_.Set.Icc a b) (z : AddCircle (1 : ℝ)) : v t z ≠ 0 := by
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective z
    change deriv (fun s : ℝ => e (γ (t, (s : AddCircle (1 : ℝ))))) r ≠ 0
    rw [deriv_loop_family_comp e he γ hγ t.2 r]
    exact (map_ne_zero_iff _ (heinj _)).mpr (hi r t t.2)
  obtain ⟨ε, hε, δ, hδ, hstable⟩ :=
    DifferentialGeometry.Calculus.exists_uniform_injective_radius_of_deriv_close hv hcderiv hvne
  refine ⟨ε, hε, δ, hδ, fun Γ hΓ hclose => ?_⟩
  have hs (t : _root_.Set.Icc a b) :
      (∀ r : ℝ, deriv (fun s : ℝ => e (Γ (t, (s : AddCircle (1 : ℝ))))) r ≠ 0) ∧
      ∀ z w : AddCircle (1 : ℝ), _root_.Dist.dist z w < δ → e (Γ (t, z)) = e (Γ (t, w)) → z = w := by
    apply hstable t (fun z => e (Γ (t, z)))
      ((he.comp (contMDiff_loop_family_slice Γ hΓ t.2)).contDiff.differentiable
        (by simp))
    intro r
    obtain ⟨s, hs, hsr⟩ := AddCircle.eq_coe_Ico (r : AddCircle (1 : ℝ))
    have heq (c₀ : AddCircle (1 : ℝ) → F) :
        deriv (fun y : ℝ => c₀ (y : AddCircle (1 : ℝ))) r =
          deriv (fun y : ℝ => c₀ (y : AddCircle (1 : ℝ))) s := by
      let hper := periodic_deriv_circle c₀
      change hper.lift (r : AddCircle (1 : ℝ)) = hper.lift (s : AddCircle (1 : ℝ))
      rw [hsr]
    rw [heq (fun z => e (Γ (t, z))), heq (fun z => e (γ (t, z)))]
    exact lt_of_le_of_lt
      (norm_deriv_loop_family_sub_le_iteratedFDerivWithin_one e he γ Γ hab hγ hΓ t.2 s)
      (hclose (s, t) ⟨⟨hs.1, hs.2.le⟩, t.2⟩)
  refine ⟨?_, ?_⟩
  · intro r t ht hz
    have hnot := (hs ⟨t, ht⟩).1 r
    apply hnot
    rw [deriv_loop_family_comp e he Γ hΓ ht r]
    change mfderiv I 𝓘(ℝ, F) e (Γ (t, (r : AddCircle (1 : ℝ))))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => Γ (t, (s : AddCircle (1 : ℝ)))) r (1 : ℝ)) = 0
    change mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => Γ (t, (s : AddCircle (1 : ℝ)))) r (1 : ℝ) = 0 at hz
    rw [hz, map_zero]
  · intro t ht z w hzw heq
    exact le_of_not_gt (fun hlt => hzw ((hs ⟨t, ht⟩).2 z w hlt (congrArg e heq)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_loop_family_immersion_separation_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_loop_family_immersion_separation_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_loop_family_immersion_separation_radius ``Submission.DifferentialGeometry.Topology.exists_loop_family_immersion_separation_radius

end DifferentialGeometry.Topology

end
