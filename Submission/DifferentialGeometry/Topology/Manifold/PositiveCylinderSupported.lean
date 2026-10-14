import Submission.DifferentialGeometry.Topology.Manifold.TruncatedCylinderAnnulus
import Submission.DifferentialGeometry.Topology.Manifold.CylinderAnnulusSupported

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev Pos : TopologicalSpace.Opens SphereCylinder :=
  ⟨univ ×ˢ _root_.Set.Ioi (0 : ℝ),isOpen_univ.prod isOpen_Ioi⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Pos target :: scope.openDecls } }

theorem exists_supported_diffeomorph_matching_positive_cylinder_sphere
    (σ : S2 → Pos) (hσ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ σ)
    (p : SphereSeparation.ComplementPair (_root_.Set.range σ))
    (hleft : _root_.Set.range σ ⊆ closure p.left) (hright : _root_.Set.range σ ⊆ closure p.right)
    (hK : IsCompact (closure ((Subtype.val : Pos → SphereCylinder) '' p.left)))
    {ρ a b : ℝ} (ha : 0 < a) (hρa : ρ < a) (hab : a < b)
    (hlow : ∀ q : Pos, q.val.2 < b → q ∈ p.left)
    (hdepth : ∀ q : S2, b < (σ q).val.2) :
    ∃ (F : SphereCylinder ≃ₘ⟮SphereCylinderModel,SphereCylinderModel⟯ SphereCylinder)
      (η : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞),
      (∀ q : S2, F (η q,a) = (σ q).val) ∧
      ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioi ρ ∧
        EqOn F id Kᶜ ∧ _root_.Set.EqOn F.symm id Kᶜ := by
  obtain ⟨e,η,hes,het,he,hei,h₀,h₁⟩ :=
    exists_smooth_truncated_positive_cylinder_lower_annulus σ hσ p hleft hright hK ha hab hlow hdepth
  have heρ : ∀ q ∈ e.target, ρ < q.2 := by
    intro q hq
    rw [het] at hq
    exact hρa.trans_le hq.2.2
  obtain ⟨F,hF,K,hKc,hKρ,hfix,hfixi⟩ :=
    exists_supported_diffeomorph_matching_cylinder_annulus_ends e hes he hei ρ heρ
  refine ⟨F,η,?_,K,hKc,hKρ,hfix,hfixi⟩
  intro q
  rw [← h₀ (η q),hF,h₁]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_matching_positive_cylinder_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_matching_positive_cylinder_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_matching_positive_cylinder_sphere ``Submission.DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_matching_positive_cylinder_sphere

end DifferentialGeometry.Topology.Manifold
