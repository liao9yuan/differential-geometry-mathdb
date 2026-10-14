import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.ParametrizedExtension

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

theorem exists_supported_diffeomorph_matching_original_collar
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (φ ψ : PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (hη : sphereDiffeomorphDegree η = 1)
    {r R l u : ℝ} (hr : 0 < r) (hrR : r < R) (hlR : l < -R) (hRu : R < u)
    (hsource : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ φ.source)
    (hoverlap : φ '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R) ⊆ ψ.target)
    (hψzero : ∀ p : S2, (η p, 0) ∈ ψ.source)
    (hzero : ∀ p : S2, φ (p, 0) = ψ (η p, 0))
    (hside : ∀ q ∈ φ.source, φ q ∈ ψ.target → q.2 ≤ 0 → (ψ.symm (φ q)).2 ≤ 0)
    (himage : ∀ q ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R, ψ.symm (φ q) ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo l u) :
    ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
      (∀ q : SphereCylinder, |q.2| ≤ r → F q ∈ ψ.source ∧ ψ (F q) = φ q) ∧
      (∀ p : S2, F (p, 0) = (η p, 0)) ∧
      ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo l u ∧
        EqOn F id Kᶜ ∧ _root_.Set.EqOn F.symm id Kᶜ := by
  let A := φ.trans ψ.symm
  have hAsource : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ A.source :=
    fun q hq => ⟨hsource hq, hoverlap ⟨q, hq, rfl⟩⟩
  have hAzero (p : S2) : A (p, 0) = (η p, 0) := by
    change ψ.symm (φ (p, 0)) = _
    rw [hzero p]
    exact ψ.left_inv (hψzero p)
  have hAside : ∀ q ∈ A.source, q.2 ≤ 0 → (A q).2 ≤ 0 :=
    fun q hq hq0 => hside q hq.1 hq.2 hq0
  have hAimage : A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R) ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo l u := by
    rintro x ⟨q, hq, rfl⟩
    exact himage q hq
  obtain ⟨F, hF, hFzero, K, hK, hKU, hfix, hfixi⟩ :=
    exists_supported_diffeomorph_eq_on_parametrized_cylinder_collar A η hη hr hrR hlR hRu
      hAsource hAzero hAside hAimage
  refine ⟨F, ?_, hFzero, K, hK, hKU, hfix, hfixi⟩
  intro q hq
  have hqR : q ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R :=
    ⟨mem_univ _, (neg_le_neg hrR.le).trans (abs_le.mp hq).1, (abs_le.mp hq).2.trans hrR.le⟩
  rw [hF q hq]
  exact ⟨ψ.map_target (hoverlap ⟨q, hqR, rfl⟩), ψ.right_inv (hoverlap ⟨q, hqR, rfl⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_matching_original_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_matching_original_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_matching_original_collar ``Submission.DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_matching_original_collar

end DifferentialGeometry.Topology.Manifold
