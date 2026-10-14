import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.Extension
import Submission.DifferentialGeometry.Topology.Manifold.SphereTangentialExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }

private def sphereCylinderMap (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder :=
  η.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.sphereCylinderMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.sphereCylinderMap target :: scope.openDecls } }

theorem exists_supported_diffeomorph_eq_on_parametrized_cylinder_collar
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (hη : sphereDiffeomorphDegree η = 1)
    {r R l u : ℝ} (hr : 0 < r) (hrR : r < R) (hlR : l < -R) (hRu : R < u)
    (hsource : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ A.source)
    (hzero : ∀ p : S2, A (p, 0) = (η p, 0))
    (hside : ∀ q ∈ A.source, q.2 ≤ 0 → (A q).2 ≤ 0)
    (himage : A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R) ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo l u) :
    ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
      (∀ q : SphereCylinder, |q.2| ≤ r → F q = A q) ∧
      (∀ p : S2, F (p, 0) = (η p, 0)) ∧
      ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo l u ∧
        EqOn F id Kᶜ ∧ _root_.Set.EqOn F.symm id Kᶜ := by
  let B := (sphereCylinderMap η).symm.toPartialDiffeomorph.trans A
  have hBs : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ B.source := by
    rintro q ⟨_, hq⟩
    exact ⟨mem_univ _, hsource ⟨mem_univ _, hq⟩⟩
  have hBzero (p : S2) : B (p, 0) = (p, 0) := by
    change A (η.symm p, 0) = _
    rw [hzero, η.apply_symm_apply]
  have hBside : ∀ q ∈ B.source, q.2 ≤ 0 → (B q).2 ≤ 0 := by
    intro q hq hq0
    exact hside (sphereCylinderMap η |>.symm <| q) hq.2 hq0
  have hBimage : B '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R) ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo l u := by
    rintro x ⟨q, hq, rfl⟩
    exact himage ⟨(sphereCylinderMap η).symm q, ⟨mem_univ _, hq.2⟩, rfl⟩
  obtain ⟨G, hG, hGzero, K, hK, hKU, hfix, hfixi⟩ :=
    exists_supported_diffeomorph_eq_on_compact_cylinder_collar B hr hrR hlR hRu hBs hBzero hBside hBimage
  obtain ⟨T, hT, _, S, hS, hSU, hTfix, hTfixi⟩ :=
    exists_supported_diffeomorph_eq_sphere_map_on_strip η hη (-R) R l u hlR hRu
  let F := T.trans G
  have hmatch (q : SphereCylinder) (hq : |q.2| ≤ r) : F q = A q := by
    have hqR : q.2 ∈ _root_.Set.Icc (-R) R :=
      ⟨(neg_le_neg hrR.le).trans (abs_le.mp hq).1, (abs_le.mp hq).2.trans hrR.le⟩
    change G (T q) = _
    have hTq : T q = (η q.1, q.2) := hT q.1 q.2 hqR
    rw [hTq, hG (η q.1, q.2) hq]
    change A (η.symm (η q.1), q.2) = _
    rw [η.symm_apply_apply]
  refine ⟨F, hmatch, fun p => (hmatch (p, 0) (by simpa using hr.le)).trans (hzero p),
    S ∪ K, hS.union hK, _root_.Set.union_subset hSU hKU, ?_, ?_⟩
  · intro q hq
    have hqS : q ∉ S := fun h => hq (Or.inl h)
    have hqK : q ∉ K := fun h => hq (Or.inr h)
    change G (T q) = q
    rw [hTfix hqS, id_eq, hfix hqK]
    rfl
  · intro q hq
    have hqS : q ∉ S := fun h => hq (Or.inl h)
    have hqK : q ∉ K := fun h => hq (Or.inr h)
    change T.symm (G.symm q) = q
    rw [hfixi hqK, id_eq, hTfixi hqS]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_on_parametrized_cylinder_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_on_parametrized_cylinder_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_on_parametrized_cylinder_collar ``Submission.DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_on_parametrized_cylinder_collar

end DifferentialGeometry.Topology.Manifold
