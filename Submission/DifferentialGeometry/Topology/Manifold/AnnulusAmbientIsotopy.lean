import Submission.DifferentialGeometry.Topology.Manifold.SphereAnnulusBoundaryMatching
import Submission.DifferentialGeometry.Topology.Embedding.AmbientIsotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.Manifold

open private injective_mfderiv_of_smooth_partial_equiv from Submission.DifferentialGeometry.Topology.Manifold.SphereAnnulusBoundaryMatching

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
private abbrev CI := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.CI
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.CI target :: scope.openDecls } }

private theorem isSmoothEmbedding_annulus_slice
    (e : PartialEquiv (S2 × unitInterval) E3) (hes : e.source = _root_.Set.univ)
    (he : ContMDiff CI (𝓡 3) ∞ e) (hei : ContMDiffOn (𝓡 3) CI ∞ e.symm e.target)
    (t : unitInterval) : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun p : S2 => e (p,t)) := by
  have hs : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun p : S2 => e (p,t)) :=
    he.comp (contMDiff_id.prodMk contMDiff_const)
  refine ⟨isImmersion_of_injective_mfderiv (by decide) hs ?_,
    hs.continuous.isClosedEmbedding (fun p q h => congrArg Prod.fst (e.injective_of_source_eq_univ hes h))
      |>.isEmbedding⟩
  intro p
  have hinc : ContMDiff (𝓡 2) CI ∞ (fun q : S2 => (q,t)) := contMDiff_id.prodMk contMDiff_const
  change _root_.Function.Injective (mfderiv (𝓡 2) (𝓡 3) (e ∘ fun q : S2 => (q,t)) p)
  rw [mfderiv_comp p (he.mdifferentiableAt (by decide)) (hinc.mdifferentiableAt (by decide)),mfderiv_prod_left]
  exact (injective_mfderiv_of_smooth_partial_equiv e hes he hei (p,t)).comp
    (fun _ _ h => congrArg Prod.fst h)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_annulus_slice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_annulus_slice target :: scope.openDecls } }

theorem exists_supported_diffeomorph_matching_annulus_ends
    (e : PartialEquiv (S2 × unitInterval) E3) (hes : e.source = _root_.Set.univ)
    (he : ContMDiff CI (𝓡 3) ∞ e) (hei : ContMDiffOn (𝓡 3) CI ∞ e.symm e.target)
    {U : Set E3} (hU : IsOpen U) (hetU : e.target ⊆ U) :
    ∃ F : E3 ≃ₘ[ℝ] E3,
      (∀ p : S2, F (e (p,0)) = e (p,1)) ∧
      ∃ K : Set E3, IsCompact K ∧ K ⊆ U ∧ _root_.Set.EqOn F id Kᶜ ∧ _root_.Set.EqOn F.symm id Kᶜ := by
  let f : ℝ × S2 → E3 := fun q => e (q.2,_root_.Set.projIcc 0 1 zero_le_one q.1)
  have hf : ContMDiffOn (𝓘(ℝ).prod (𝓡 2)) (𝓡 3) ∞ f (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.univ) := by
    apply he.comp_contMDiffOn
    exact contMDiff_snd.contMDiffOn.prodMk
      (contMDiffOn_projIcc.comp contMDiff_fst.contMDiffOn (fun q hq => hq.1))
  have hemb (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
      IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun p : S2 => f (t,p)) :=
    isSmoothEmbedding_annulus_slice e hes he hei (_root_.Set.projIcc 0 1 zero_le_one t)
  have hfU : f '' (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.univ) ⊆ U := by
    rintro x ⟨q,_,rfl⟩
    exact hetU (e.map_source (hes ▸ _root_.Set.mem_univ _))
  obtain ⟨Φ,hΦ,hΦi,hΦ0,htrack,K,hK,hKU,hfix⟩ :=
    _root_.Submission.Manifold.exists_contDiff_compact_ambient_isotopy_Icc hf hemb hU hfU
  refine ⟨Φ 1,?_,K,hK,hKU,(hfix 1).1,(hfix 1).2⟩
  intro p
  have h := (htrack 1 ⟨zero_le_one,le_rfl⟩ p).1
  have h₀ : _root_.Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) := Subtype.ext (by simp)
  have h₁ : _root_.Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : unitInterval) := Subtype.ext (by simp)
  simpa only [f,h₀,h₁] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_matching_annulus_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_matching_annulus_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_matching_annulus_ends ``Submission.DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_matching_annulus_ends

end DifferentialGeometry.Topology.Manifold
