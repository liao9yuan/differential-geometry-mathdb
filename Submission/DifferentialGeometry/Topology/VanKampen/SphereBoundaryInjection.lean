import Submission.DifferentialGeometry.Topology.VanKampen.TwoBoundaryCollars
import Submission.DifferentialGeometry.Topology.VanKampen.BoundaryCollarInjection
import Submission.DifferentialGeometry.Topology.VanKampen.SmoothTwoSidedCollarBridge
import Submission.DifferentialGeometry.Topology.Manifold.SmoothBicollar
import Mathlib.Topology.Piecewise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

private def sumSelfHomeomorphBoolProd (S : Type*) [TopologicalSpace S] :
    (S ⊕ S) ≃ₜ Bool × S where
  toEquiv := (Equiv.boolProdEquivSum S).symm
  continuous_toFun :=
    (continuous_const.prodMk continuous_id).sumElim (continuous_const.prodMk continuous_id)
  continuous_invFun := by
    change Continuous (fun p : Bool × S ↦ if p.1 = _root_.Bool.true then Sum.inr p.2 else Sum.inl p.2)
    have hcl : IsClopen {p : Bool × S | p.1 = _root_.Bool.true} :=
      (isClopen_discrete ({_root_.Bool.true} : Set Bool)).preimage continuous_fst
    exact Continuous.if (by simp only [hcl.frontier_eq, _root_.Set.mem_empty_iff_false, false_implies, implies_true])
      (continuous_inr.comp continuous_snd) (continuous_inl.comp continuous_snd)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.sumSelfHomeomorphBoolProd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.sumSelfHomeomorphBoolProd target :: scope.openDecls } }

theorem subsingleton_pathHomotopicQuotient_sum_sphereTwo (x y : SphereTwo ⊕ SphereTwo) :
    Subsingleton (Path.Homotopic.Quotient x y) :=
  subsingleton_pathHomotopicQuotient_of_homotopyEquiv
    (sumSelfHomeomorphBoolProd SphereTwo).toHomotopyEquiv
    (subsingleton_pathHomotopicQuotient_prod
      subsingleton_pathHomotopicQuotient_of_totallyDisconnected (fun _ _ ↦ inferInstance)) x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_sum_sphereTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_sum_sphereTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_sum_sphereTwo ``Submission.DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_sum_sphereTwo

theorem exists_outward_collar_of_two_spherical_boundaries
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {K : Set M} (hregular : closure (interior K) = K)
    (e₀ e₁ : SphereTwo → M)
    (he₀ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hfront : frontier K = _root_.Set.range e₀ ∪ _root_.Set.range e₁)
    (hd : Disjoint (_root_.Set.range e₀) (_root_.Set.range e₁)) :
    ∃ c : ThreeManifold.TwoSidedCollar (Sum.elim e₀ e₁),
      ∀ p : (SphereTwo ⊕ SphereTwo) × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0 := by
  obtain ⟨c₀⟩ := exists_smoothTwoSidedCollar_of_smoothSphereEmbedding e₀ he₀
  obtain ⟨c₁⟩ := exists_smoothTwoSidedCollar_of_smoothSphereEmbedding e₁ he₁
  exact c₀.toTwoSidedCollar.exists_outward_collar_of_two_components c₁.toTwoSidedCollar
    hregular hfront hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_outward_collar_of_two_spherical_boundaries then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_outward_collar_of_two_spherical_boundaries"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_outward_collar_of_two_spherical_boundaries ``Submission.DifferentialGeometry.Topology.exists_outward_collar_of_two_spherical_boundaries

theorem injective_fundamentalGroup_map_of_two_spherical_boundaries
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {K : Set M} [PathConnectedSpace K] (hregular : closure (interior K) = K)
    (e₀ e₁ : SphereTwo → M)
    (he₀ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hfront : frontier K = _root_.Set.range e₀ ∪ _root_.Set.range e₁)
    (hd : Disjoint (_root_.Set.range e₀) (_root_.Set.range e₁)) (x₀ : K) :
    Function.Injective (FundamentalGroup.map (VanKampen.subsetToAmbient K) x₀) := by
  obtain ⟨c, hside⟩ := exists_outward_collar_of_two_spherical_boundaries
    hregular e₀ e₁ he₀ he₁ hfront hd
  apply c.injective_fundamentalGroup_map_domain (hregular ▸ isClosed_closure) ?_
    hside subsingleton_pathHomotopicQuotient_sum_sphereTwo x₀
  rw [hfront]
  rintro x (⟨s, rfl⟩ | ⟨s, rfl⟩)
  · exact ⟨Sum.inl s, rfl⟩
  · exact ⟨Sum.inr s, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.injective_fundamentalGroup_map_of_two_spherical_boundaries then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.injective_fundamentalGroup_map_of_two_spherical_boundaries"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.injective_fundamentalGroup_map_of_two_spherical_boundaries ``Submission.DifferentialGeometry.Topology.injective_fundamentalGroup_map_of_two_spherical_boundaries

end DifferentialGeometry.Topology
