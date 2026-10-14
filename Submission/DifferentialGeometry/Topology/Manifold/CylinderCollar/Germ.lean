import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.RadialGerm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Metric
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

private def puncturedDiffeomorph (F : E3 ≃ₘ[ℝ] E3) (hF : F 0 = 0) :
    puncturedSpace E3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ puncturedSpace E3 where
  toEquiv := (F.toHomeomorph.subtype (fun x => by
    change x ≠ 0 ↔ F x ≠ 0
    constructor
    · intro hx he
      exact hx (F.injective (he.trans hF.symm))
    · intro hx he
      exact hx (he ▸ hF))).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (puncturedSpace E3) _).mp
    exact F.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (puncturedSpace E3) _).mp
    exact F.symm.contMDiff.comp contMDiff_subtype_val

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.puncturedDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.puncturedDiffeomorph target :: scope.openDecls } }

private def cylindricalConjugate (v : S2) (F : E3 ≃ₘ[ℝ] E3) (hF : F 0 = 0) :
    SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder :=
  (sphereProdRealDiffeomorphPunctured (n := 2) v).trans
    ((puncturedDiffeomorph F hF).trans (sphereProdRealDiffeomorphPunctured (n := 2) v).symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.cylindricalConjugate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.cylindricalConjugate target :: scope.openDecls } }

private theorem cylindricalConjugate_apply (v : S2) (F : E3 ≃ₘ[ℝ] E3) (hF : F 0 = 0)
    (q : SphereCylinder) :
    cylinderExponentialChart v (cylindricalConjugate v F hF q) = F (cylinderExponentialChart v q) := by
  change (sphereProdRealDiffeomorphPunctured (n := 2) v
    ((sphereProdRealDiffeomorphPunctured (n := 2) v).symm
      (puncturedDiffeomorph F hF (sphereProdRealDiffeomorphPunctured (n := 2) v q)))).val = _
  rw [Diffeomorph.apply_symm_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.cylindricalConjugate_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.cylindricalConjugate_apply target :: scope.openDecls } }

theorem exists_supported_diffeomorph_eq_zero_section_germ
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source)
    (hfixed : ∀ p : S2, A (p, 0) = (p, 0))
    (hside : ∀ q ∈ A.source, q.2 ≤ 0 → (A q).2 ≤ 0)
    (l u : ℝ) (hl : l < 0) (hu : 0 < u) :
    ∃ G : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
      ∃ V : Set SphereCylinder, IsOpen V ∧ _root_.Set.range (fun p : S2 => (p, (0 : ℝ))) ⊆ V ∧
        V ⊆ A.source ∧ _root_.Set.EqOn G A V ∧
        ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo l u ∧
          EqOn G id Kᶜ ∧ _root_.Set.EqOn G.symm id Kᶜ := by
  let v : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨F, V, hV, hSV, hVA, hFA, hF0, K, hK, hKO, hfix, hfixi⟩ :=
    exists_supported_radial_diffeomorph_eq_cylinder_germ v A hsource hfixed hside l u hl hu
  let E := cylinderExponentialChart v
  let e := sphereProdRealDiffeomorphPunctured (n := 2) v
  let G := cylindricalConjugate v F hF0
  let V' := E ⁻¹' V
  have hcont : Continuous E := by
    rw [← continuousOn_univ, ← cylinderExponentialChart_source v]
    exact E.contMDiffOn.continuousOn
  have hV' : IsOpen V' := hV.preimage hcont
  have hS' : _root_.Set.range (fun p : S2 => (p, (0 : ℝ))) ⊆ V' := by
    rintro q ⟨p, rfl⟩
    change E (p, 0) ∈ V
    rw [cylinderExponentialChart_zero]
    exact hSV p.property
  have hsub : V' ⊆ A.source := by
    intro q hq
    have hh := (cylinderRadialGerm_source v A (E q)).mp (hVA hq)
    have he : E.symm (E q) = q := E.left_inv (by rw [cylinderExponentialChart_source]; trivial)
    exact he ▸ hh.2
  have hmatch : _root_.Set.EqOn G A V' := by
    intro q hq
    apply e.injective
    apply Subtype.ext
    change E (G q) = E (A q)
    rw [cylindricalConjugate_apply, hFA hq]
    change E (A (E.symm (E q))) = _
    have he : E.symm (E q) = q := E.left_inv (by rw [cylinderExponentialChart_source]; trivial)
    exact congrArg (fun z => E (A z)) he
  let K' := E.symm '' K
  have hKsrc : K ⊆ E.target := by
    intro x hx
    rw [cylinderExponentialChart_target]
    change x ≠ 0
    intro hx0
    have hh := (hKO hx).1
    rw [hx0, norm_zero] at hh
    exact (not_lt_of_ge (Real.exp_pos l).le) hh
  have hK' : IsCompact K' := hK.image_of_continuousOn (E.symm.contMDiffOn.continuousOn.mono hKsrc)
  have hKband : K' ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo l u := by
    rintro q ⟨x, hx, rfl⟩
    have hxn : x ≠ 0 := by
      have hh := hKsrc hx
      change x ∈ (cylinderExponentialChart v).target at hh
      rw [cylinderExponentialChart_target] at hh
      exact hh
    rw [cylinderExponentialChart_symm_apply v x hxn]
    refine ⟨mem_univ _, ?_, ?_⟩
    · exact Real.lt_log_iff_exp_lt (norm_pos_iff.mpr hxn) |>.mpr (hKO hx).1
    · exact Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hxn) |>.mpr (hKO hx).2
  have hGfix : _root_.Set.EqOn G id K'ᶜ := by
    intro q hq
    have hqK : E q ∉ K := by
      intro hqK
      exact hq ⟨E q, hqK, E.left_inv (by rw [cylinderExponentialChart_source]; trivial)⟩
    apply e.injective
    apply Subtype.ext
    change E (G q) = E q
    rw [cylindricalConjugate_apply, hfix hqK]
    rfl
  refine ⟨G, V', hV', hS', hsub, hmatch, K', hK', hKband, hGfix, ?_⟩
  intro q hq
  have hh := G.symm_apply_apply q
  rw [hGfix hq] at hh
  exact hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_zero_section_germ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_zero_section_germ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_zero_section_germ ``Submission.DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_zero_section_germ


theorem exists_supported_diffeomorph_eq_on_cylinder_collar
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source)
    (hfixed : ∀ p : S2, A (p, 0) = (p, 0))
    (hside : ∀ q ∈ A.source, q.2 ≤ 0 → (A q).2 ≤ 0)
    (l u : ℝ) (hl : l < 0) (hu : 0 < u) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ G : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
      (∀ (p : S2) (t : ℝ), |t| < ε → (p, t) ∈ A.source ∧ G (p, t) = A (p, t)) ∧
      (∀ p : S2, G (p, 0) = (p, 0)) ∧
      (∀ q : SphereCylinder, q.2 ≤ l ∨ u ≤ q.2 → G q = q ∧ G.symm q = q) ∧
      ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo l u ∧
        EqOn G id Kᶜ ∧ _root_.Set.EqOn G.symm id Kᶜ := by
  obtain ⟨G, V, hV, hSV, hVA, hG, K, hK, hKU, hfix, hfixi⟩ :=
    exists_supported_diffeomorph_eq_zero_section_germ A hsource hfixed hside l u hl hu
  have hslice : (_root_.Set.univ : Set S2) ×ˢ ({0} : Set ℝ) ⊆ V := by
    rintro ⟨p, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hSV ⟨p, rfl⟩
  obtain ⟨S, T, _, hT, hSS, hTT, hST⟩ := generalized_tube_lemma isCompact_univ isCompact_singleton hV hslice
  obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.mp hT 0 (hTT (_root_.Set.mem_singleton 0))
  refine ⟨ε, hε, G, ?_, ?_, ?_, K, hK, hKU, hfix, hfixi⟩
  · intro p t ht
    have hmem : (p, t) ∈ V := hST ⟨hSS (_root_.Set.mem_univ p), hεT (by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht)⟩
    exact ⟨hVA hmem, hG hmem⟩
  · intro p
    exact (hG (hSV ⟨p, rfl⟩)).trans (hfixed p)
  · intro q hq
    have hn : q ∉ K := by
      intro hqK
      have hinterval := (hKU hqK).2
      rcases hq with hq | hq
      · exact (not_lt_of_ge hq) hinterval.1
      · exact (not_lt_of_ge hq) hinterval.2
    exact ⟨hfix hn, hfixi hn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_on_cylinder_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_on_cylinder_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_on_cylinder_collar ``Submission.DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_on_cylinder_collar

end DifferentialGeometry.Topology.Manifold
