import Submission.DifferentialGeometry.Topology.Homology.SimplexDegreeChainLevel
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalCharts

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set _root_.AlgebraicTopology
open scoped _root_.Simplicial

namespace DifferentialGeometry.Topology.SimplexDegree

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

set_option backward.isDefEq.respectTransparency false in
private theorem relative_simplex_chain_map (g : C(X, Y)) {A : Set X} {B : Set Y}
    (hg : _root_.Set.MapsTo g A B) (σ : C(stdSimplex ℝ (Fin 4), X)) :
    (integralSimplexChain 3 σ ≫ (cokernel.π (integralSingularChainMap
        (singularSubspaceInclusion A))).f 3) ≫ (integralRelativeChainMap g hg).f 3 =
      integralSimplexChain 3 (g.comp σ) ≫
        (cokernel.π (integralSingularChainMap (singularSubspaceInclusion B))).f 3 := by
  have hnat := congrArg (fun k => k.f 3) (integralRelativeChainMap_π g hg)
  simp only [HomologicalComplex.comp_f] at hnat
  rw [Category.assoc, hnat, ← Category.assoc]
  congr 1
  have h := SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X))
    (TopCat.toSSet.obj (TopCat.of Y)) (TopCat.toSSet.map (TopCat.ofHom g))
    integralSingularCoefficients ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋3⦌)).symm σ)
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.relative_simplex_chain_map
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.relative_simplex_chain_map target :: scope.openDecls } }

theorem integralRelativeHomologyMap_simplexLocalClass
    (g : C(X, Y)) (p : X) (q : Y)
    (hg : _root_.Set.MapsTo g ({p}ᶜ : Set X) ({q}ᶜ : Set Y))
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (t : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i t) ≠ p) :
    integralRelativeHomologyMap 3 g hg (simplexLocalClass p σ hσ) =
      simplexLocalClass q (g.comp σ) (fun i t => hg (hσ i t)) := by
  have hchain := relative_simplex_chain_map g hg σ
  unfold simplexLocalClass
  generalize_proofs _ _ _ _ hpcycle _ _ _ hqcycle
  change (HomologicalComplex.homologyMap (integralRelativeChainMap g hg) 3).hom _ = _
  rw [chainComplex_homologyMap_liftCycles_apply (integralRelativeChainMap g hg) 2 _ hpcycle
    (hchain.symm ▸ hqcycle)]
  exact congrArg (fun k : integralSingularCoefficients ⟶ (integralRelativeChains ({q}ᶜ : Set Y)).homology 3 =>
    k (ULift.up 1)) (chainComplex_liftCycles_homologyπ_congr 2 _ _ _ _ hchain)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralRelativeHomologyMap_simplexLocalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralRelativeHomologyMap_simplexLocalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralRelativeHomologyMap_simplexLocalClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralRelativeHomologyMap_simplexLocalClass

theorem integralLocalHomologyHomeomorphIso_simplexLocalClass
    (g : X ≃ₜ Y) (p : X) (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p) :
    (integralLocalHomologyHomeomorphIso 3 g p).hom.hom (simplexLocalClass p σ hσ) =
      simplexLocalClass (g p) ((⟨g, g.continuous⟩ : C(X, Y)).comp σ)
        (fun i q h => hσ i q (g.injective h)) := by
  exact integralRelativeHomologyMap_simplexLocalClass ⟨g, g.continuous⟩ p (g p) (fun _ hy => g.injective.ne hy) σ hσ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralLocalHomologyHomeomorphIso_simplexLocalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralLocalHomologyHomeomorphIso_simplexLocalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralLocalHomologyHomeomorphIso_simplexLocalClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralLocalHomologyHomeomorphIso_simplexLocalClass

theorem integralLocalHomologyNeighborhoodIso_simplexLocalClass [T1Space X]
    (U : Set X) (hU : IsOpen U) (p : X) (hp : p ∈ U)
    (σ : C(stdSimplex ℝ (Fin 4), U))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)),
      σ (orientedSimplexFace i q) ≠ (⟨p, hp⟩ : U)) :
    (integralLocalHomologyNeighborhoodIso 3 p U hU hp).hom.hom
      (simplexLocalClass (⟨p, hp⟩ : U) σ hσ) =
      simplexLocalClass p ((singularSubspaceInclusion U).comp σ)
        (fun i q h => hσ i q (Subtype.ext h)) := by
  exact integralRelativeHomologyMap_simplexLocalClass (singularSubspaceInclusion U) ⟨p, hp⟩ p _ σ hσ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralLocalHomologyNeighborhoodIso_simplexLocalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralLocalHomologyNeighborhoodIso_simplexLocalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralLocalHomologyNeighborhoodIso_simplexLocalClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralLocalHomologyNeighborhoodIso_simplexLocalClass

theorem integralLocalHomologyOpenPartialHomeomorphIso_simplexLocalClass
    [T1Space X] [T1Space Y]
    (e : OpenPartialHomeomorph X Y) (p : X) (hp : p ∈ e.source)
    (σ : C(stdSimplex ℝ (Fin 4), X)) (hσsource : ∀ q, σ q ∈ e.source)
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p) :
    (integralLocalHomologyOpenPartialHomeomorphIso 3 e p hp).hom.hom
      (simplexLocalClass p σ hσ) =
      simplexLocalClass (e p)
        ⟨fun q => e (σ q), e.continuousOn.comp_continuous σ.continuous hσsource⟩
        (fun i q h => hσ i q (e.injOn (hσsource _) hp h)) := by
  let σU : C(stdSimplex ℝ (Fin 4), e.source) :=
    ⟨fun q => ⟨σ q, hσsource q⟩, σ.continuous.subtype_mk hσsource⟩
  have hσU : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)),
      σU (orientedSimplexFace i q) ≠ (⟨p, hp⟩ : e.source) :=
    fun i q h => hσ i q (congrArg Subtype.val h)
  have hU : (integralLocalHomologyNeighborhoodIso 3 p e.source e.open_source hp).hom.hom
      (simplexLocalClass (⟨p, hp⟩ : e.source) σU hσU) = simplexLocalClass p σ hσ :=
    integralLocalHomologyNeighborhoodIso_simplexLocalClass e.source e.open_source p hp σU hσU
  rw [← hU]
  change (integralLocalHomologyNeighborhoodIso 3 (e p) e.target e.open_target
    (e.map_source hp)).hom.hom
      ((integralLocalHomologyHomeomorphIso 3 e.toHomeomorphSourceTarget
        (⟨p, hp⟩ : e.source)).hom.hom
          ((integralLocalHomologyNeighborhoodIso 3 p e.source e.open_source hp).inv.hom
            ((integralLocalHomologyNeighborhoodIso 3 p e.source e.open_source hp).hom.hom
              (simplexLocalClass (⟨p, hp⟩ : e.source) σU hσU)))) = _
  rw [Iso.hom_inv_id_apply, integralLocalHomologyHomeomorphIso_simplexLocalClass]
  exact integralLocalHomologyNeighborhoodIso_simplexLocalClass e.target e.open_target (e p)
    (e.map_source hp) _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralLocalHomologyOpenPartialHomeomorphIso_simplexLocalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralLocalHomologyOpenPartialHomeomorphIso_simplexLocalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralLocalHomologyOpenPartialHomeomorphIso_simplexLocalClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralLocalHomologyOpenPartialHomeomorphIso_simplexLocalClass

end DifferentialGeometry.Topology.SimplexDegree
