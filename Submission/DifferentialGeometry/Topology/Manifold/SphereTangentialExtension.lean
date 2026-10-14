import Submission.DifferentialGeometry.Topology.Manifold.SphereGraphExtension
import Submission.DifferentialGeometry.Topology.Manifold.SphereDiffeomorphDegree

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

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
private abbrev Cylinder := S2 × ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Cylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Cylinder target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

private def sphereAxialSuspension
    (J : ℝ → S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (hJ : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × S2 => J q.1 q.2))
    (hJi : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × S2 => (J q.1).symm q.2))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) : Cylinder ≃ₘ⟮IC, IC⟯ Cylinder where
  toFun p := (J (χ p.2) p.1, p.2)
  invFun p := ((J (χ p.2)).symm p.1, p.2)
  left_inv p := Prod.ext ((J (χ p.2)).symm_apply_apply p.1) rfl
  right_inv p := Prod.ext ((J (χ p.2)).apply_symm_apply p.1) rfl
  contMDiff_toFun :=
    (hJ.comp ((hχ.contMDiff.comp contMDiff_snd).prodMk contMDiff_fst)).prodMk contMDiff_snd
  contMDiff_invFun :=
    (hJi.comp ((hχ.contMDiff.comp contMDiff_snd).prodMk contMDiff_fst)).prodMk contMDiff_snd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.sphereAxialSuspension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.sphereAxialSuspension target :: scope.openDecls } }

theorem exists_supported_diffeomorph_eq_sphere_map_on_strip
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (hη : sphereDiffeomorphDegree η = 1)
    (a b l u : ℝ) (hla : l < a) (hbu : b < u) :
    ∃ F : Cylinder ≃ₘ⟮IC, IC⟯ Cylinder,
      (∀ (p : S2) (s : ℝ), s ∈ _root_.Set.Icc a b → F (p, s) = (η p, s)) ∧
      (∀ p : Cylinder, (F p).2 = p.2) ∧
      ∃ S : Set Cylinder, IsCompact S ∧ S ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo l u ∧
        EqOn F id Sᶜ ∧ _root_.Set.EqOn F.symm id Sᶜ := by
  obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ := (sphereDiffeomorphDegree_eq_one_iff_isotopy η).mp hη
  obtain ⟨χ, hχ, hcχ, hχone, hχsupp, _⟩ := DifferentialGeometry.Analysis.exists_bump_compact
    _root_.CompactIccSpace.isCompact_Icc isOpen_Ioo (show _root_.Set.Icc a b ⊆ _root_.Set.Ioo l u from fun s hs => ⟨hla.trans_le hs.1, hs.2.trans_lt hbu⟩)
  let A : ℝ → S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2 := fun t => J (1 - t)
  have ht : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓘(ℝ).prod (𝓡 2)) ∞
      (fun q : ℝ × S2 => (1 - q.1, q.2)) := (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
  let F := sphereAxialSuspension A (hJ.comp ht) (hJi.comp ht) χ hχ
  have hzero : A 0 = Diffeomorph.refl (𝓡 2) S2 ∞ := by simpa only [A, sub_zero] using hJ1
  refine ⟨F, ?_, fun _ => rfl, _root_.Set.univ ×ˢ tsupport χ, isCompact_univ.prod hcχ,
    _root_.Set.prod_mono subset_rfl hχsupp, ?_, ?_⟩
  · intro p s hs
    have hone : χ s = 1 := Filter.EventuallyEq.eq_of_nhds (hχone.filter_mono (nhds_le_nhdsSet hs))
    change (A (χ s) p, s) = _
    rw [hone]
    change (J (1 - 1) p, s) = _
    rw [sub_self, hJ0]
  · intro p hp
    have hnot : p.2 ∉ tsupport χ := fun hx => hp ⟨mem_univ _, hx⟩
    change (A (χ p.2) p.1, p.2) = _
    rw [image_eq_zero_of_notMem_tsupport hnot, hzero]
    rfl
  · intro p hp
    have hnot : p.2 ∉ tsupport χ := fun hx => hp ⟨mem_univ _, hx⟩
    change ((A (χ p.2)).symm p.1, p.2) = _
    rw [image_eq_zero_of_notMem_tsupport hnot, hzero]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_sphere_map_on_strip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_sphere_map_on_strip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_sphere_map_on_strip ``Submission.DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_sphere_map_on_strip

end DifferentialGeometry.Topology.Manifold
