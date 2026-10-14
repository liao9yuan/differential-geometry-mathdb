import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCover
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.FreeOrthogonalAction
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Isometry.Representation
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Metric _root_.Module _root_.Submission.Module _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private instance euclideanThreeFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.euclideanThreeFinrankFact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.euclideanThreeFinrankFact target :: scope.openDecls } }

theorem solitonModelCovering_roundTwoSphere_deck_eq_one_or_antipodal
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 → M}
    (hπ : solitonModelCovering roundTwoSphereShrinkerMetric
      roundTwoSphereShrinkerPotential g f cover)
    (gamma : coveringDeckGroup cover) :
    gamma.1 = 1 ∨ gamma.1 =
      (realProjectiveSpaceAntipodalHomeomorph
        (EuclideanSpace Real (Fin 3))).toEquiv := by
  let phi (delta : coveringDeckGroup cover) :=
    coveringDeckGroupDiffeomorph
      (solitonModelCovering_isLocalDiffeomorph hπ) delta
  have hphiMetric (delta : coveringDeckGroup cover) :
      Diffeomorph.pullbackMetricCross roundTwoSphereShrinkerMetric (phi delta) =
        roundTwoSphereShrinkerMetric :=
    (solitonModelCovering_deckGroup_preserves hπ delta).1
  have hphiOne (x : _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
      phi 1 x = x := by
    rfl
  have hphiMul (delta eta : coveringDeckGroup cover)
      (x : _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
      phi (delta * eta) x = phi delta (phi eta x) := by
    rfl
  have hphiIso (delta : coveringDeckGroup cover)
      (x : _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
      (v w : TangentSpace (𝓡 2) x) :
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x v w =
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner
          (phi delta x)
          (mfderiv (𝓡 2) (𝓡 2) (phi delta) x v)
          (mfderiv (𝓡 2) (𝓡 2) (phi delta) x w) := by
    have h := Diffeomorph.pullbackMetricCross_inner
      roundTwoSphereShrinkerMetric (phi delta) x v w
    rw [hphiMetric delta] at h
    have hscaled := h
    simp only [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric,
      scaleMetric_inner] at hscaled
    exact mul_left_cancel₀
      (ne_of_gt (sq_pos_of_pos
        (roundSphereShrinkerRadius_pos (n := 2) (by decide)))) hscaled
  have hphiFree : ∀ (delta : coveringDeckGroup cover)
      (x : _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1),
      phi delta x = x → delta = 1 := by
    let _ : PreconnectedSpace
        (_root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
      Subtype.preconnectedSpace
        (isPreconnected_sphere
          (Module.one_lt_rank_of_one_lt_finrank (by norm_num))
          (0 : EuclideanSpace Real (Fin 3)) 1)
    intro delta x hx
    exact coveringDeckGroup_eq_one_of_apply_eq
      (solitonModelCovering_isCoveringMap hπ) delta x hx
  obtain ⟨rho, hrho⟩ := orth_rep_of_iso
    (E := EuclideanSpace Real (Fin 3)) (n := 2)
    phi (by norm_num) hphiOne hphiMul hphiIso
  have hfree : ∀ (delta : coveringDeckGroup cover)
      (x : _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1),
      sphereDiffeo (n := 2) (rho delta) x = x → delta = 1 := by
    intro delta x hx
    apply hphiFree delta x
    rw [← hrho delta]
    exact hx
  rcases orth_rep_apply_eq_one_or_neg_of_free_sphere_action rho hfree gamma with
    hrhoGamma | hrhoGamma
  · left
    apply Equiv.ext
    intro x
    have h := congrArg
      (fun d : _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1
          ≃ₘ⟮𝓡 2, 𝓡 2⟯ _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 => d x)
      (hrho gamma)
    rw [hrhoGamma] at h
    change x = gamma.1 x at h
    exact h.symm
  · right
    apply Equiv.ext
    intro x
    have h := congrArg
      (fun d : _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1
          ≃ₘ⟮𝓡 2, 𝓡 2⟯ _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 => d x)
      (hrho gamma)
    rw [hrhoGamma] at h
    change -x = gamma.1 x at h
    exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.solitonModelCovering_roundTwoSphere_deck_eq_one_or_antipodal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.solitonModelCovering_roundTwoSphere_deck_eq_one_or_antipodal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.solitonModelCovering_roundTwoSphere_deck_eq_one_or_antipodal ``Submission.DifferentialGeometry.Geometry.solitonModelCovering_roundTwoSphere_deck_eq_one_or_antipodal

theorem solitonModelCovering_roundTwoSphere_deckGroup_eq_bot_or_antipodal
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 → M}
    (hπ : solitonModelCovering roundTwoSphereShrinkerMetric
      roundTwoSphereShrinkerPotential g f cover) :
    coveringDeckGroup cover = ⊥ ∨
      coveringDeckGroup cover = realProjectivePlaneAntipodalGroup := by
  classical
  by_cases hanti : ∃ gamma : coveringDeckGroup cover,
      gamma.1 = (realProjectiveSpaceAntipodalHomeomorph
        (EuclideanSpace Real (Fin 3))).toEquiv
  · right
    apply le_antisymm
    · intro psi hpsi
      let gamma : coveringDeckGroup cover := ⟨psi, hpsi⟩
      rcases solitonModelCovering_roundTwoSphere_deck_eq_one_or_antipodal
          hπ gamma with hone | hgenerator
      · rw [show psi = 1 from hone]
        exact Subgroup.one_mem _
      · rw [show psi =
          (realProjectiveSpaceAntipodalHomeomorph
            (EuclideanSpace Real (Fin 3))).toEquiv from hgenerator]
        exact Subgroup.mem_zpowers _
    · change Subgroup.zpowers
        (realProjectiveSpaceAntipodalHomeomorph
          (EuclideanSpace Real (Fin 3))).toEquiv ≤ coveringDeckGroup cover
      apply Subgroup.zpowers_le.mpr
      obtain ⟨gamma, hgamma⟩ := hanti
      rw [← hgamma]
      exact gamma.property
  · left
    apply le_antisymm
    · intro psi hpsi
      simp only [Subgroup.mem_bot]
      let gamma : coveringDeckGroup cover := ⟨psi, hpsi⟩
      rcases solitonModelCovering_roundTwoSphere_deck_eq_one_or_antipodal
          hπ gamma with hone | hgenerator
      · exact hone
      · exact (hanti ⟨gamma, hgenerator⟩).elim
    · exact bot_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.solitonModelCovering_roundTwoSphere_deckGroup_eq_bot_or_antipodal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.solitonModelCovering_roundTwoSphere_deckGroup_eq_bot_or_antipodal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.solitonModelCovering_roundTwoSphere_deckGroup_eq_bot_or_antipodal ``Submission.DifferentialGeometry.Geometry.solitonModelCovering_roundTwoSphere_deckGroup_eq_bot_or_antipodal

theorem solitonModelCovering_target_homeomorphic_two_sphere_or_real_projective_plane_of_isQuotientCoveringMap
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 → M}
    (hπ : solitonModelCovering roundTwoSphereShrinkerMetric
      roundTwoSphereShrinkerPotential g f cover)
    (hquotient : IsQuotientCoveringMap cover (coveringDeckGroup cover)) :
    (∃ e : _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 ≃ₜ M,
      ∀ x, e x = cover x) ∨
    (∃ e : RealProjectivePlane ≃ₜ M,
      ∀ x, e (realProjectivePlaneQuotientMap x) = cover x) := by
  rcases solitonModelCovering_roundTwoSphere_deckGroup_eq_bot_or_antipodal hπ with
    htrivial | hantipodal
  · left
    have hinjective : Function.Injective cover := by
      intro x y hxy
      obtain ⟨gamma, hgamma⟩ := hquotient.apply_eq_iff_mem_orbit.mp hxy
      have hmem : gamma.1 ∈ (⊥ : Subgroup
          (Equiv.Perm (_root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1))) := by
        rw [← htrivial]
        exact gamma.property
      have hone : gamma.1 = 1 := by
        simpa only [Subgroup.mem_bot] using hmem
      change gamma.1 y = x at hgamma
      rw [hone] at hgamma
      exact hgamma.symm
    let e : _root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 ≃ₜ M :=
      Continuous.homeoOfEquivCompactToT2
        (f := Equiv.ofBijective cover
          ⟨hinjective, solitonModelCovering_surjective hπ⟩)
        (solitonModelCovering_contMDiff hπ).continuous
    exact ⟨e, fun _ => rfl⟩
  · right
    have hquotient' : IsQuotientCoveringMap cover
        realProjectivePlaneAntipodalGroup :=
      (IsQuotientCoveringMap.subgroup_congr
        cover (Equiv.Perm
          (_root_.Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1))
        (coveringDeckGroup cover) realProjectivePlaneAntipodalGroup
        hantipodal).mp hquotient
    let e : RealProjectivePlane ≃ₜ M :=
      hquotient'.orbitRelQuotientHomeomorph
    refine ⟨e, fun x => ?_⟩
    exact hquotient'.orbitRelQuotientHomeomorph_apply x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.solitonModelCovering_target_homeomorphic_two_sphere_or_real_projective_plane_of_isQuotientCoveringMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.solitonModelCovering_target_homeomorphic_two_sphere_or_real_projective_plane_of_isQuotientCoveringMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.solitonModelCovering_target_homeomorphic_two_sphere_or_real_projective_plane_of_isQuotientCoveringMap ``Submission.DifferentialGeometry.Geometry.solitonModelCovering_target_homeomorphic_two_sphere_or_real_projective_plane_of_isQuotientCoveringMap

end DifferentialGeometry.Geometry
