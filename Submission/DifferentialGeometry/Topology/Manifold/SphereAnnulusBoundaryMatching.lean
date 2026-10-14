import Submission.DifferentialGeometry.Topology.Ehresmann.ProductEnds
import Submission.DifferentialGeometry.Topology.Manifold.ProductHalfSpaceBoundary
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import Submission.DifferentialGeometry.Topology.Embedding.Diffeomorph
import Submission.DifferentialGeometry.Geometry.Boundary.EmbeddingFrontier
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Analysis.Normed.Module.Connected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
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
private abbrev CI := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.CI
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.CI target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instHasSmoothBoundaryProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceCI : DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))
    (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)) CI :=
  productHalfSpaceBoundaryModel

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instHasSmoothBoundaryProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceCI
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instHasSmoothBoundaryProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceCI target :: scope.openDecls } }

private theorem injective_mfderiv_of_smooth_partial_equiv
    (e : PartialEquiv (S2 × unitInterval) E3) (hes : e.source = _root_.Set.univ)
    (he : ContMDiff CI (𝓡 3) ∞ e) (hei : ContMDiffOn (𝓡 3) CI ∞ e.symm e.target)
    (q : S2 × unitInterval) : _root_.Function.Injective (mfderiv CI (𝓡 3) e q) := by
  have hcomp : e.symm ∘ e = id := funext (fun p => e.left_inv (hes ▸ _root_.Set.mem_univ p))
  have hd := mfderivWithin_comp q
    (hei.mdifferentiableOn (by decide) (e q) (e.map_source (hes ▸ _root_.Set.mem_univ q)))
    ((he.mdifferentiable (by decide) q).mdifferentiableWithinAt (s := _root_.Set.univ))
    (fun p _ => e.map_source (hes ▸ _root_.Set.mem_univ p)) (uniqueMDiffWithinAt_univ CI)
  rw [hcomp,mfderivWithin_univ,mfderiv_id,mfderivWithin_univ] at hd
  intro v w hvw
  have h := congrArg (mfderivWithin (𝓡 3) CI e.symm e.target (e q)) hvw
  rw [← ContinuousLinearMap.comp_apply,← hd,← ContinuousLinearMap.comp_apply,← hd] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_smooth_partial_equiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_smooth_partial_equiv target :: scope.openDecls } }

theorem exists_parametrized_sphere_annulus_of_smooth_partial_equiv
    (e : PartialEquiv (S2 × unitInterval) E3) (hes : e.source = _root_.Set.univ)
    (he : ContMDiff CI (𝓡 3) ∞ e) (hei : ContMDiffOn (𝓡 3) CI ∞ e.symm e.target)
    (e₀ e₁ : S2 → E3)
    (he₀ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hfront : frontier e.target = _root_.Set.range e₀ ∪ _root_.Set.range e₁) :
    ∃ Ψ : Diffeomorph CI CI (S2 × unitInterval) (S2 × unitInterval) ∞,
      ∃ η : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞,
        (∀ p : S2, e (Ψ (p,0)) = e₀ p) ∧
        ∀ p : S2, e (Ψ (η p,1)) = e₁ p := by
  let : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : E3) (by norm_num : (0 : ℝ) ≤ 1))
  have hinj := e.injective_of_source_eq_univ hes
  have hclosed := he.continuous.isClosedEmbedding hinj
  have hder := injective_mfderiv_of_smooth_partial_equiv e hes he hei
  have hrange : _root_.Set.range e = e.target := by
    rw [← _root_.Set.image_univ,← hes,e.image_source_eq_target]
  have hbdy : e '' CI.boundary (S2 × unitInterval) = _root_.Set.range e₀ ∪ _root_.Set.range e₁ := by
    rw [DifferentialGeometry.Geometry.Boundary.image_boundary_eq_frontier_of_fullRank_closedEmbedding
      e he hclosed hder (by simp),hrange,hfront]
  obtain ⟨D,h₀,h₁⟩ := Ehresmann.exists_intervalProduct_with_labeled_ends
    (Diffeomorph.refl CI (S2 × unitInterval) ∞) e he.continuous hinj
    (_root_.Set.range e₀) (_root_.Set.range e₁) (isPreconnected_range he₀.contMDiff.continuous)
    (isPreconnected_range he₁.contMDiff.continuous) hbdy
  have hsmooth (t : unitInterval) :
      ContMDiff (𝓡 2) (𝓡 3) ∞ (fun p : S2 => e (D (p,t))) :=
    he.comp (D.contMDiff.comp (contMDiff_id.prodMk contMDiff_const))
  have hslice (t : unitInterval) :
      IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun p : S2 => e (D (p,t))) := by
    refine ⟨isImmersion_of_injective_mfderiv (by decide) (hsmooth t) ?_,
      (hsmooth t).continuous.isClosedEmbedding (fun p q h => congrArg Prod.fst (D.injective (hinj h)))
        |>.isEmbedding⟩
    intro p
    have hD : _root_.Function.Injective (mfderiv CI CI D (p,t)) :=
      (D.isLocalDiffeomorph (p,t)).mfderivToContinuousLinearEquiv (by decide) |>.injective
    have hι : _root_.Function.Injective (mfderiv (𝓡 2) CI (fun q : S2 => (q,t)) p) := by
      rw [mfderiv_prod_left]
      exact fun _ _ h => congrArg Prod.fst h
    have hinc : ContMDiff (𝓡 2) CI ∞ (fun q : S2 => (q,t)) :=
      contMDiff_id.prodMk contMDiff_const
    have hdiff : MDifferentiableAt (𝓡 2) CI (D ∘ fun q : S2 => (q,t)) p :=
      (D.contMDiff.comp hinc).mdifferentiableAt (by decide)
    have hde := mfderiv_comp p (he.mdifferentiableAt (by decide)) hdiff
    have hdD := mfderiv_comp p (D.contMDiff.mdifferentiableAt (by decide))
      (hinc.mdifferentiableAt (by decide))
    change _root_.Function.Injective (mfderiv (𝓡 2) (𝓡 3) (e ∘ D ∘ fun q : S2 => (q,t)) p)
    rw [hde,hdD]
    exact (hder _).comp (hD.comp hι)
  let η₀ := he₀.diffeomorphOfRangeEq (hslice 0) h₀.symm
  let η₁ := he₁.diffeomorphOfRangeEq (hslice 1) h₁.symm
  let Ψ := (η₀.prodCongr (Diffeomorph.refl (𝓡∂ 1) unitInterval ∞)).trans D
  let η := η₁.trans η₀.symm
  refine ⟨Ψ,η,?_,?_⟩
  · intro p
    exact he₀.comp_diffeomorphOfRangeEq (hslice 0) h₀.symm p
  · intro p
    change e (D (η₀ (η₀.symm (η₁ p)),1)) = e₁ p
    rw [η₀.apply_symm_apply]
    exact he₁.comp_diffeomorphOfRangeEq (hslice 1) h₁.symm p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_parametrized_sphere_annulus_of_smooth_partial_equiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_parametrized_sphere_annulus_of_smooth_partial_equiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_parametrized_sphere_annulus_of_smooth_partial_equiv ``Submission.DifferentialGeometry.Topology.Manifold.exists_parametrized_sphere_annulus_of_smooth_partial_equiv

end DifferentialGeometry.Topology.Manifold
