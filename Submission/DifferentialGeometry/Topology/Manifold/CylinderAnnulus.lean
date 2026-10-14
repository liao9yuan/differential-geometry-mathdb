import Submission.DifferentialGeometry.Topology.Manifold.SphereAnnulusBoundaryMatching
import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.Coordinates
import Submission.DifferentialGeometry.Topology.Manifold.NestedBallShell
import Submission.DifferentialGeometry.Topology.SphereSeparation.TwoSphereDomain
import Submission.DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenflies
import Submission.DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFilling
import Submission.DifferentialGeometry.Topology.Embedding.CompactFrontier
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding

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

theorem exists_smooth_cylinder_annulus_parametrization
    {K : Set SphereCylinder} (hK : IsCompact K)
    (hregular : closure (interior K) = K) (hconn : IsPreconnected (interior K))
    (e₀ e₁ : S2 → SphereCylinder)
    (he₀ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ e₀)
    (he₁ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ e₁)
    (hfront : frontier K = _root_.Set.range e₀ ∪ _root_.Set.range e₁)
    (hdisj : Disjoint (_root_.Set.range e₀) (_root_.Set.range e₁)) :
    ∃ (e : PartialEquiv (S2 × unitInterval) SphereCylinder)
      (η : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞),
      e.source = _root_.Set.univ ∧ e.target = K ∧
      ContMDiff ((𝓡 2).prod (𝓡∂ 1)) SphereCylinderModel ∞ e ∧
      ContMDiffOn SphereCylinderModel ((𝓡 2).prod (𝓡∂ 1)) ∞ e.symm K ∧
      (∀ p : S2, e (p,0) = e₀ p) ∧ ∀ p : S2, e (η p,1) = e₁ p := by
  let v : S2 := Classical.arbitrary S2
  let C := cylinderExponentialChart v
  have hCs : C.source = univ := cylinderExponentialChart_source v
  have hCinj : _root_.Function.Injective C := C.toPartialEquiv.injective_of_source_eq_univ hCs
  have hClocal : IsLocalDiffeomorph SphereCylinderModel (𝓡 3) ∞ C :=
    fun q => C.isLocalDiffeomorphAt _ _ _ (hCs ▸ _root_.Set.mem_univ q)
  have hC : _root_.Manifold.IsSmoothEmbedding SphereCylinderModel (𝓡 3) ∞ C :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective
      hClocal hCinj
  have hCo : _root_.Topology.IsOpenEmbedding C :=
    hClocal.isLocalHomeomorph.isOpenEmbedding_of_injective hCinj
  let L := C '' K
  have hLc : IsCompact L := hK.image hCo.continuous
  have hi : interior L = C '' interior K :=
    (DifferentialGeometry.Topology.Embedding.image_interior_of_isOpenEmbedding hCo K).symm
  have hLregular : closure (interior L) = L := by
    apply Subset.antisymm
    · exact hLc.isClosed.closure_interior_subset
    · rw [hi]
      calc
        L = C '' closure (interior K) := by rw [hregular]
        _ ⊆ closure (C '' interior K) := image_closure_subset_closure_image hCo.continuous
  have hLconn : IsPreconnected (interior L) := by
    rw [hi]
    exact hconn.image C hCo.continuous.continuousOn
  have hLe₀ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (C ∘ e₀) :=
    IsSmoothEmbedding.comp hC he₀ (by simp)
  have hLe₁ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (C ∘ e₁) :=
    IsSmoothEmbedding.comp hC he₁ (by simp)
  have hLf : frontier L = _root_.Set.range (C ∘ e₀) ∪ _root_.Set.range (C ∘ e₁) := by
    rw [show L = C '' K from rfl,
      ← DifferentialGeometry.Topology.Embedding.image_frontier_of_isOpenEmbedding_of_isCompact hCo hK,
      hfront,_root_.Set.image_union,← _root_.Set.range_comp,← _root_.Set.range_comp]
  have hLd : Disjoint (_root_.Set.range (C ∘ e₀)) (_root_.Set.range (C ∘ e₁)) := by
    rw [_root_.Set.range_comp,_root_.Set.range_comp]
    exact (_root_.Set.disjoint_image_iff hCinj).mpr hdisj
  have hSch : SphereSeparation.smoothSchoenfliesThree :=
    SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph.mpr
      ThreeManifold.smooth_schoenflies_three
  obtain ⟨outer,inner,hnest,hrange⟩ :=
    SphereSeparation.exists_nested_ball_shell_of_two_spherical_boundaries
      hSch hLc hLregular hLconn (C ∘ e₀) (C ∘ e₁) hLe₀ hLe₁ hLf hLd
  obtain ⟨e,hes,het,he,hei⟩ := exists_smooth_nestedBallShell_parametrization (n := 2)
    outer.toPartialDiffeomorph inner.toPartialDiffeomorph zero_lt_one
    (_root_.Set.subset_univ _) (_root_.Set.subset_univ _) hnest v
  have het' : e.target = L := het.trans hrange.symm
  have heC : e.target ⊆ C.target := by
    rw [het']
    rintro x ⟨q,_,rfl⟩
    exact C.map_source (hCs ▸ _root_.Set.mem_univ q)
  obtain ⟨Ψ,η,hΨ₀,hΨ₁⟩ := exists_parametrized_sphere_annulus_of_smooth_partial_equiv
    e hes he hei (C ∘ e₀) (C ∘ e₁) hLe₀ hLe₁ (by rw [het']; exact hLf)
  let em := Ψ.toEquiv.transPartialEquiv e
  have hems : em.source = univ := by
    change Ψ ⁻¹' e.source = _root_.Set.univ
    rw [hes,_root_.Set.preimage_univ]
  have hemt : em.target = e.target := rfl
  have hem : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ em := he.comp Ψ.contMDiff
  have hemi : ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡∂ 1)) ∞ em.symm em.target :=
    Ψ.symm.contMDiff.comp_contMDiffOn hei
  let d := em.trans C.symm.toPartialEquiv
  have hds : d.source = univ := by
    ext p
    constructor
    · exact fun _ => _root_.Set.mem_univ _
    · intro _
      have hp : p ∈ em.source := hems ▸ _root_.Set.mem_univ p
      exact ⟨hp,heC (em.map_source hp)⟩
  have hdt : d.target = K := by
    ext q
    constructor
    · rintro ⟨hq,hqe⟩
      change C q ∈ e.target at hqe
      rw [het'] at hqe
      obtain ⟨x,hx,hxq⟩ := hqe
      exact hCinj hxq ▸ hx
    · intro hq
      refine ⟨show q ∈ C.source from hCs ▸ _root_.Set.mem_univ q,?_⟩
      change C q ∈ e.target
      rw [het']
      exact _root_.Set.mem_image_of_mem C hq
  refine ⟨d,η,hds,hdt,?_,?_,?_,?_⟩
  · apply contMDiffOn_univ.mp
    exact C.contMDiffOn_invFun.comp hem.contMDiffOn
      (fun p _ => heC (em.map_source (hems ▸ _root_.Set.mem_univ p)))
  · exact hemi.comp (hC.contMDiff.contMDiffOn)
      (fun q hq => het'.symm ▸ _root_.Set.mem_image_of_mem C hq)
  · intro p
    change C.symm (e (Ψ (p,0))) = e₀ p
    rw [hΨ₀]
    exact C.left_inv (hCs ▸ _root_.Set.mem_univ _)
  · intro p
    change C.symm (e (Ψ (η p,1))) = e₁ p
    rw [hΨ₁]
    exact C.left_inv (hCs ▸ _root_.Set.mem_univ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_smooth_cylinder_annulus_parametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_smooth_cylinder_annulus_parametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_smooth_cylinder_annulus_parametrization ``Submission.DifferentialGeometry.Topology.Manifold.exists_smooth_cylinder_annulus_parametrization

end DifferentialGeometry.Topology.Manifold
