import Submission.DifferentialGeometry.Topology.Homology.Subdivision.Homotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E E' : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : E →L[ℝ] E')

local notation "Φ" => TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f)))


theorem affineSimplex_map_linear {n : ℕ} (v : Fin (n + 1) → E) :
    (⟨f, f.continuous⟩ : C(E, E')).comp (affineSimplex v) = affineSimplex (f ∘ v) := by
  ext x
  change f (∑ i, x i • v i) = ∑ i, x i • f (v i)
  simp only [map_sum, map_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSimplex_map_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSimplex_map_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSimplex_map_linear ``Submission.DifferentialGeometry.Homology.affineSimplex_map_linear


theorem map_affineSingularSimplex_linear {n : ℕ} (v : Fin (n + 1) → E) :
    (Φ).app (_root_.Opposite.op ⦋n⦌) (affineSingularSimplex v) = affineSingularSimplex (f ∘ v) := by
  apply ((TopCat.of E').toSSetObjEquiv (_root_.Opposite.op ⦋n⦌)).injective
  exact affineSimplex_map_linear f v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.map_affineSingularSimplex_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.map_affineSingularSimplex_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.map_affineSingularSimplex_linear ``Submission.DifferentialGeometry.Homology.map_affineSingularSimplex_linear


theorem singularSimplexVertices_map_linear {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    singularSimplexVertices ((Φ).app (_root_.Opposite.op ⦋n⦌) σ) = f ∘ singularSimplexVertices σ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSimplexVertices_map_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSimplexVertices_map_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSimplexVertices_map_linear ``Submission.DifferentialGeometry.Homology.singularSimplexVertices_map_linear


theorem singularSimplexBarycenter_map_linear {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    singularSimplexBarycenter ((Φ).app (_root_.Opposite.op ⦋n⦌) σ) = f (singularSimplexBarycenter σ) := by
  simp only [singularSimplexBarycenter, singularSimplexVertices_map_linear,
    Finset.centerMass, Function.comp_apply, map_smul, map_sum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSimplexBarycenter_map_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSimplexBarycenter_map_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSimplexBarycenter_map_linear ``Submission.DifferentialGeometry.Homology.singularSimplexBarycenter_map_linear


theorem affineStraightening_naturality_linear :
    (Φ) ≫ affineStraightening (E := E') = affineStraightening (E := E) ≫ (Φ) := by
  ext n σ
  exact (congrArg affineSingularSimplex (singularSimplexVertices_map_linear f σ)).trans
    (map_affineSingularSimplex_linear f (singularSimplexVertices σ)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineStraightening_naturality_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineStraightening_naturality_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineStraightening_naturality_linear ``Submission.DifferentialGeometry.Homology.affineStraightening_naturality_linear

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

local notation "T" => _root_.SSet.chainComplexMap (Φ) R
local notation "K" => _root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R
local notation "L" => _root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E')) R
local notation "S" => _root_.SSet.chainComplexMap (affineStraightening (E := E)) R
local notation "S'" => _root_.SSet.chainComplexMap (affineStraightening (E := E')) R


theorem affineStraightening_chain_naturality_linear : (T) ≫ (S') = (S) ≫ (T) := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, affineStraightening_naturality_linear]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineStraightening_chain_naturality_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineStraightening_chain_naturality_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineStraightening_chain_naturality_linear ``Submission.DifferentialGeometry.Homology.affineStraightening_chain_naturality_linear


@[reassoc]
theorem affineCone_naturality_linear (p : E) (n : ℕ) :
    affineCone R p n ≫ (T).f (n + 1) = (T).f n ≫ affineCone R (f p) n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_affineCone, SSet.ι_chainComplexMap_f,
    map_affineSingularSimplex_linear]
  rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((T).f n),
    SSet.ι_chainComplexMap_f, ι_affineCone, singularSimplexVertices_map_linear, Fin.comp_cons]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineCone_naturality_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineCone_naturality_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineCone_naturality_linear ``Submission.DifferentialGeometry.Homology.affineCone_naturality_linear


theorem affineSubdivisionMap_naturality_linear (n : ℕ) :
    affineSubdivisionMap (E := E) R n ≫ (T).f n =
      (T).f n ≫ affineSubdivisionMap (E := E') R n := by
  induction n with
  | zero => rw [affineSubdivisionMap_zero, affineSubdivisionMap_zero,
      Category.id_comp, Category.comp_id]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionMap_succ]
    simp only [Category.assoc]
    rw [affineCone_naturality_linear]
    rw [← Category.assoc (affineSubdivisionMap (E := E) R n), hn]
    simp only [Category.assoc]
    rw [← Category.assoc ((K).d (n + 1) n), ← (T).comm]
    simp only [Category.assoc]
    rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((T).f (n + 1)),
      SSet.ι_chainComplexMap_f]
    rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((T).f (n + 1)),
      SSet.ι_chainComplexMap_f, ι_affineSubdivisionMap_succ, singularSimplexBarycenter_map_linear]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivisionMap_naturality_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivisionMap_naturality_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivisionMap_naturality_linear ``Submission.DifferentialGeometry.Homology.affineSubdivisionMap_naturality_linear


theorem affineSubdivision_naturality_linear :
    affineSubdivision (E := E) R ≫ (T) = (T) ≫ affineSubdivision (E := E') R := by
  apply HomologicalComplex.hom_f_injective
  funext n
  exact affineSubdivisionMap_naturality_linear f R n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivision_naturality_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivision_naturality_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivision_naturality_linear ``Submission.DifferentialGeometry.Homology.affineSubdivision_naturality_linear

private theorem difference_naturality_linear (n : ℕ) :
    (affineSubdivision (E := E) R - S).f n ≫ (T).f n =
      (T).f n ≫ (affineSubdivision (E := E') R - S').f n := by
  rw [HomologicalComplex.sub_f_apply, Preadditive.sub_comp, affineSubdivision_f,
    affineSubdivisionMap_naturality_linear]
  have h := HomologicalComplex.congr_hom (affineStraightening_chain_naturality_linear f R) n
  simp only [HomologicalComplex.comp_f] at h
  rw [← h, HomologicalComplex.sub_f_apply, Preadditive.comp_sub, affineSubdivision_f]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.difference_naturality_linear
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.difference_naturality_linear target :: scope.openDecls } }


theorem affineSubdivisionHomotopyMap_naturality_linear (n : ℕ) :
    affineSubdivisionHomotopyMap (E := E) R n ≫ (T).f (n + 1) =
      (T).f n ≫ affineSubdivisionHomotopyMap (E := E') R n := by
  induction n with
  | zero => rw [affineSubdivisionHomotopyMap_zero, affineSubdivisionHomotopyMap_zero,
      _root_.CategoryTheory.Limits.zero_comp, _root_.CategoryTheory.Limits.comp_zero]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    have hz :
        ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫
            (affineSubdivision (E := E) R - S).f (n + 1) -
          (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (K).d (n + 1) n ≫
            affineSubdivisionHomotopyMap R n) ≫ (T).f (n + 1) =
        (TopCat.toSSet.obj (TopCat.of E')).ιChainComplex ((Φ).app (_root_.Opposite.op ⦋n + 1⦌) σ) ≫
            (affineSubdivision (E := E') R - S').f (n + 1) -
          (TopCat.toSSet.obj (TopCat.of E')).ιChainComplex ((Φ).app (_root_.Opposite.op ⦋n + 1⦌) σ) ≫
            (L).d (n + 1) n ≫ affineSubdivisionHomotopyMap R n := by
      rw [Preadditive.sub_comp]
      simp only [Category.assoc]
      rw [difference_naturality_linear, hn]
      rw [← Category.assoc ((K).d (n + 1) n), ← (T).comm]
      simp only [Category.assoc]
      rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((T).f (n + 1)),
        SSet.ι_chainComplexMap_f]
      rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((T).f (n + 1)),
        SSet.ι_chainComplexMap_f]
    rw [← Category.assoc, ι_affineSubdivisionHomotopyMap_succ, Category.assoc,
      affineCone_naturality_linear, ← Category.assoc, hz]
    rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((T).f (n + 1)),
      SSet.ι_chainComplexMap_f, ι_affineSubdivisionHomotopyMap_succ,
      singularSimplexBarycenter_map_linear]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_naturality_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_naturality_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_naturality_linear ``Submission.DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_naturality_linear

end DifferentialGeometry.Homology
