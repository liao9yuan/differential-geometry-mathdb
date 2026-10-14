import Submission.DifferentialGeometry.Topology.Homology.Subdivision.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial
universe u
noncomputable section
namespace DifferentialGeometry.Homology
private abbrev simplexAmbient (n : ℕ) := ULift.{u} (Fin (n + 1) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexAmbient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexAmbient target :: scope.openDecls } }
private def simplexRegion (n : ℕ) : Set (simplexAmbient.{u} n) :=
  ULift.down ⁻¹' stdSimplex ℝ (Fin (n + 1))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexRegion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexRegion target :: scope.openDecls } }
private theorem convex_simplexRegion (n : ℕ) : Convex ℝ (simplexRegion.{u} n) := by
  intro x hx y hy a b ha hb hab
  exact (convex_stdSimplex ℝ (Fin (n + 1))) hx hy ha hb hab

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.convex_simplexRegion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.convex_simplexRegion target :: scope.openDecls } }
private def simplexRegionHomeo (n : ℕ) :
    SimplexCategory.toTop.{u}.obj ⦋n⦌ ≃ₜ simplexRegion.{u} n where
  toFun x := ⟨⟨x.down.val⟩, x.down.property⟩
  invFun x := ⟨⟨x.val.down, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _
  continuous_invFun :=
    continuous_uliftUp.comp ((continuous_uliftDown.comp continuous_subtype_val).subtype_mk _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexRegionHomeo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexRegionHomeo target :: scope.openDecls } }
private def simplexCoordinatesMap {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    simplexAmbient.{u} n →L[ℝ] simplexAmbient.{u} m where
  toFun x := ⟨FunOnFinite.linearMap ℝ ℝ f x.down⟩
  map_add' x y := by
    apply ULift.ext
    exact map_add (FunOnFinite.linearMap ℝ ℝ f) x.down y.down
  map_smul' a x := by
    apply ULift.ext
    exact map_smul (FunOnFinite.linearMap ℝ ℝ f) a x.down
  cont := continuous_uliftUp.comp ((FunOnFinite.continuous_linearMap ℝ ℝ f).comp
    continuous_uliftDown)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexCoordinatesMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexCoordinatesMap target :: scope.openDecls } }
private theorem simplexCoordinatesMap_mem {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    Set.MapsTo (simplexCoordinatesMap.{u} f) (simplexRegion n) (simplexRegion m) := by
  intro x hx
  exact (stdSimplex.map f ⟨x.down, hx⟩).property

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexCoordinatesMap_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexCoordinatesMap_mem target :: scope.openDecls } }
private def simplexEmbedding (n : ℕ) :
    SimplexCategory.toTop.{u}.obj ⦋n⦌ ⟶ TopCat.of (simplexAmbient.{u} n) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.down.val⟩,
    continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexEmbedding
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexEmbedding target :: scope.openDecls } }
private theorem simplexEmbedding_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    SimplexCategory.toTop.map f ≫ simplexEmbedding m =
      simplexEmbedding n ≫ TopCat.ofHom (⟨simplexCoordinatesMap f,
        (simplexCoordinatesMap f).continuous⟩ : C(simplexAmbient n, simplexAmbient m)) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexEmbedding_naturality
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexEmbedding_naturality target :: scope.openDecls } }

private def simplexSupportedIso (n : ℕ) :
    TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌) ≅
      (smallSingularSimplices (TopCat.of (simplexAmbient.{u} n))
        (fun _ : Unit ↦ simplexRegion n) : SSet) :=
  TopCat.toSSet.mapIso (TopCat.isoOfHomeo (simplexRegionHomeo n)) ≪≫
    singularSubspaceIso _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexSupportedIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexSupportedIso target :: scope.openDecls } }

private theorem simplexSupportedIso_inclusion (n : ℕ) :
    (simplexSupportedIso.{u} n).hom ≫
        (smallSingularSimplices (TopCat.of (simplexAmbient.{u} n))
          (fun _ : Unit ↦ simplexRegion n)).ι =
      TopCat.toSSet.map (simplexEmbedding n) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexSupportedIso_inclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexSupportedIso_inclusion target :: scope.openDecls } }

private def simplexSupportedMap {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (smallSingularSimplices (TopCat.of (simplexAmbient.{u} n))
      (fun _ : Unit ↦ simplexRegion n) : SSet) ⟶
    (smallSingularSimplices (TopCat.of (simplexAmbient.{u} m))
      (fun _ : Unit ↦ simplexRegion m) : SSet) :=
  smallSingularSimplicesMap
    (TopCat.ofHom (⟨simplexCoordinatesMap f, (simplexCoordinatesMap f).continuous⟩ :
      C(simplexAmbient n, simplexAmbient m))) (fun _ ↦ ⟨(), simplexCoordinatesMap_mem f⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexSupportedMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexSupportedMap target :: scope.openDecls } }

private theorem simplexSupportedIso_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    TopCat.toSSet.map (SimplexCategory.toTop.map f) ≫ (simplexSupportedIso.{u} m).hom =
      (simplexSupportedIso.{u} n).hom ≫ simplexSupportedMap f := by
  ext d σ
  apply Subtype.ext
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexSupportedIso_naturality
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexSupportedIso_naturality target :: scope.openDecls } }

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

private def simplexSupportedChainIso (n : ℕ) :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).mapIso (simplexSupportedIso.{u} n)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexSupportedChainIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexSupportedChainIso target :: scope.openDecls } }

private theorem simplexSupportedChainIso_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R ≫
        (simplexSupportedChainIso R m).hom =
      (simplexSupportedChainIso R n).hom ≫ SSet.chainComplexMap (simplexSupportedMap f) R := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, simplexSupportedIso_naturality]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexSupportedChainIso_naturality
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexSupportedChainIso_naturality target :: scope.openDecls } }

private theorem simplexSupportedChainIso_inv_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (simplexSupportedChainIso R n).inv ≫
        SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R =
      SSet.chainComplexMap (simplexSupportedMap f) R ≫ (simplexSupportedChainIso R m).inv := by
  apply (Iso.inv_comp_eq _).mpr
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv _).mpr (simplexSupportedChainIso_naturality R f)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexSupportedChainIso_inv_naturality
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexSupportedChainIso_inv_naturality target :: scope.openDecls } }


def simplexSubdivision (n : ℕ) :
    (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R ⟶
      (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R :=
  (simplexSupportedChainIso R n).hom ≫
    smallAffineSubdivision (convex_simplexRegion n) R ≫ (simplexSupportedChainIso R n).inv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.simplexSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.simplexSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.simplexSubdivision ``Submission.DifferentialGeometry.Homology.simplexSubdivision


def simplexStraightening (n : ℕ) :
    (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R ⟶
      (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R :=
  (simplexSupportedChainIso R n).hom ≫
    SSet.chainComplexMap (smallAffineStraightening (convex_simplexRegion n)) R ≫
      (simplexSupportedChainIso R n).inv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.simplexStraightening then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.simplexStraightening"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.simplexStraightening ``Submission.DifferentialGeometry.Homology.simplexStraightening


def simplexSubdivisionHomotopy (n : ℕ) :
    Homotopy (simplexSubdivision R n) (simplexStraightening R n) :=
  ((smallAffineSubdivisionHomotopy (convex_simplexRegion n) R).compLeft
    (simplexSupportedChainIso R n).hom).compRight (simplexSupportedChainIso R n).inv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.simplexSubdivisionHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.simplexSubdivisionHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.simplexSubdivisionHomotopy ``Submission.DifferentialGeometry.Homology.simplexSubdivisionHomotopy

theorem simplexSubdivision_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    simplexSubdivision R n ≫
        SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R =
      SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R ≫
        simplexSubdivision R m := by
  have hB : smallAffineSubdivision (convex_simplexRegion n) R ≫
        SSet.chainComplexMap (simplexSupportedMap f) R =
      SSet.chainComplexMap (simplexSupportedMap f) R ≫
        smallAffineSubdivision (convex_simplexRegion m) R := by
    apply HomologicalComplex.hom_f_injective
    funext d
    exact smallAffineSubdivisionMap_naturality_linear _ R _ (simplexCoordinatesMap f)
      (simplexCoordinatesMap_mem f) d
  simp only [simplexSubdivision, Category.assoc]
  rw [simplexSupportedChainIso_inv_naturality]
  rw [← Category.assoc (smallAffineSubdivision (convex_simplexRegion n) R), hB]
  simp only [Category.assoc]
  rw [← Category.assoc ((simplexSupportedChainIso R n).hom),
    ← simplexSupportedChainIso_naturality]
  simp only [Category.assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.simplexSubdivision_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.simplexSubdivision_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.simplexSubdivision_naturality ``Submission.DifferentialGeometry.Homology.simplexSubdivision_naturality


theorem simplexSubdivisionHomotopy_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (d : ℕ) :
    (simplexSubdivisionHomotopy R n).hom d (d + 1) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R).f (d + 1) =
      (SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R).f d ≫
        (simplexSubdivisionHomotopy R m).hom d (d + 1) := by
  have h := HomologicalComplex.congr_hom (simplexSupportedChainIso_naturality R f) d
  have hi := HomologicalComplex.congr_hom (simplexSupportedChainIso_inv_naturality R f) (d + 1)
  simp only [HomologicalComplex.comp_f] at h hi
  simp only [simplexSubdivisionHomotopy, Homotopy.compRight_hom, Homotopy.compLeft_hom,
    smallAffineSubdivisionHomotopy_hom, Category.assoc]
  rw [hi]
  rw [← Category.assoc (smallAffineSubdivisionHomotopyMap (convex_simplexRegion n) R d)]
  have hH : smallAffineSubdivisionHomotopyMap (convex_simplexRegion n) R d ≫
        (SSet.chainComplexMap (simplexSupportedMap f) R).f (d + 1) =
      (SSet.chainComplexMap (simplexSupportedMap f) R).f d ≫
        smallAffineSubdivisionHomotopyMap (convex_simplexRegion m) R d :=
    smallAffineSubdivisionHomotopyMap_naturality_linear _ R _ (simplexCoordinatesMap f)
      (simplexCoordinatesMap_mem f) d
  rw [hH]
  simp only [Category.assoc]
  rw [← Category.assoc ((simplexSupportedChainIso R n).hom.f d), ← h]
  simp only [Category.assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.simplexSubdivisionHomotopy_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.simplexSubdivisionHomotopy_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.simplexSubdivisionHomotopy_naturality ``Submission.DifferentialGeometry.Homology.simplexSubdivisionHomotopy_naturality


def fundamentalSingularSimplex (n : ℕ) :
    TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌) _⦋n⦌ :=
  ULift.up (𝟙 _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.fundamentalSingularSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.fundamentalSingularSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.fundamentalSingularSimplex ``Submission.DifferentialGeometry.Homology.fundamentalSingularSimplex


def fundamentalSimplexChain (n : ℕ) :
    R ⟶ ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R).X n :=
  (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).ιChainComplex
    (fundamentalSingularSimplex n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.fundamentalSimplexChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.fundamentalSimplexChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.fundamentalSimplexChain ``Submission.DifferentialGeometry.Homology.fundamentalSimplexChain


def barycentricSimplexChain (n : ℕ) :
    R ⟶ ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R).X n :=
  fundamentalSimplexChain R n ≫ (simplexSubdivision R n).f n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.barycentricSimplexChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.barycentricSimplexChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.barycentricSimplexChain ``Submission.DifferentialGeometry.Homology.barycentricSimplexChain


def barycentricSimplexHomotopyChain (n : ℕ) :
    R ⟶ ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R).X (n + 1) :=
  fundamentalSimplexChain R n ≫ (simplexSubdivisionHomotopy R n).hom n (n + 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.barycentricSimplexHomotopyChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.barycentricSimplexHomotopyChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.barycentricSimplexHomotopyChain ``Submission.DifferentialGeometry.Homology.barycentricSimplexHomotopyChain


theorem fundamentalSimplexChain_boundary (n : ℕ) :
    fundamentalSimplexChain R (n + 1) ≫
        ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n + 1⦌)).chainComplex R).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1) ^ i.val •
        (fundamentalSimplexChain R n ≫
          (SSet.chainComplexMap (TopCat.toSSet.map
            (SimplexCategory.toTop.map (SimplexCategory.δ i))) R).f n) := by
  rw [fundamentalSimplexChain, SSet.ιChainComplex_d]
  apply Finset.sum_congr rfl
  intro i _
  rw [fundamentalSimplexChain, SSet.ι_chainComplexMap_f]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.fundamentalSimplexChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.fundamentalSimplexChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.fundamentalSimplexChain_boundary ``Submission.DifferentialGeometry.Homology.fundamentalSimplexChain_boundary


theorem barycentricSimplexChain_boundary (n : ℕ) :
    barycentricSimplexChain R (n + 1) ≫
        ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n + 1⦌)).chainComplex R).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1) ^ i.val •
        (barycentricSimplexChain R n ≫
          (SSet.chainComplexMap (TopCat.toSSet.map
            (SimplexCategory.toTop.map (SimplexCategory.δ i))) R).f n) := by
  rw [barycentricSimplexChain, Category.assoc, (simplexSubdivision R (n + 1)).comm,
    ← Category.assoc, fundamentalSimplexChain_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro i _
  have h := HomologicalComplex.congr_hom (simplexSubdivision_naturality R (SimplexCategory.δ i)) n
  simp only [HomologicalComplex.comp_f] at h
  rw [← h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.barycentricSimplexChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.barycentricSimplexChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.barycentricSimplexChain_boundary ``Submission.DifferentialGeometry.Homology.barycentricSimplexChain_boundary

private theorem simplexEmbedding_fundamental (n : ℕ) :
    (TopCat.toSSet.map (simplexEmbedding.{u} n)).app (_root_.Opposite.op ⦋n⦌) (fundamentalSingularSimplex n) =
      affineSingularSimplex (fun i ↦ ULift.up (stdSimplex.vertex (S := ℝ) i).val) := by
  apply ((TopCat.of (simplexAmbient.{u} n)).toSSetObjEquiv (_root_.Opposite.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  change x.val = (∑ i, x i • ULift.up (stdSimplex.vertex (S := ℝ) i).val).down
  change x.val = (ULift.moduleEquiv : simplexAmbient.{u} n ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
    (∑ i, x i • ULift.up (stdSimplex.vertex (S := ℝ) i).val)
  rw [map_sum]
  simp only [map_smul, ULift.moduleEquiv_apply]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.simplexEmbedding_fundamental
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.simplexEmbedding_fundamental target :: scope.openDecls } }


theorem fundamentalSimplexChain_straightening (n : ℕ) :
    fundamentalSimplexChain R n ≫ (simplexStraightening R n).f n =
      fundamentalSimplexChain R n := by
  have hσ : (smallAffineStraightening (convex_simplexRegion n)).app (_root_.Opposite.op ⦋n⦌)
        ((simplexSupportedIso.{u} n).hom.app (_root_.Opposite.op ⦋n⦌) (fundamentalSingularSimplex n)) =
      (simplexSupportedIso.{u} n).hom.app (_root_.Opposite.op ⦋n⦌) (fundamentalSingularSimplex n) := by
    apply Subtype.ext
    change affineSingularSimplex (singularSimplexVertices
        ((TopCat.toSSet.map (simplexEmbedding n)).app (_root_.Opposite.op ⦋n⦌) (fundamentalSingularSimplex n))) =
      (TopCat.toSSet.map (simplexEmbedding n)).app (_root_.Opposite.op ⦋n⦌) (fundamentalSingularSimplex n)
    rw [simplexEmbedding_fundamental, singularSimplexVertices_affineSingularSimplex]
  have h : fundamentalSimplexChain R n ≫ (simplexSupportedChainIso R n).hom.f n ≫
        (SSet.chainComplexMap (smallAffineStraightening (convex_simplexRegion n)) R).f n =
      fundamentalSimplexChain R n ≫ (simplexSupportedChainIso R n).hom.f n := by
    rw [fundamentalSimplexChain, ← Category.assoc]
    change ((TopCat.toSSet.obj (SimplexCategory.toTop.obj ⦋n⦌)).ιChainComplex
        (fundamentalSingularSimplex n) ≫
        (SSet.chainComplexMap (simplexSupportedIso n).hom R).f n) ≫ _ = _
    rw [SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f, hσ]
    exact (SSet.ι_chainComplexMap_f _ _ _ R (fundamentalSingularSimplex n)).symm
  have hid := HomologicalComplex.congr_hom (simplexSupportedChainIso R n).hom_inv_id n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hid
  change fundamentalSimplexChain R n ≫ (simplexSupportedChainIso R n).hom.f n ≫
      (SSet.chainComplexMap (smallAffineStraightening (convex_simplexRegion n)) R).f n ≫
        (simplexSupportedChainIso R n).inv.f n = _
  simpa only [Category.assoc, hid, Category.comp_id] using
    congrArg (fun q ↦ q ≫ (simplexSupportedChainIso R n).inv.f n) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.fundamentalSimplexChain_straightening then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.fundamentalSimplexChain_straightening"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.fundamentalSimplexChain_straightening ``Submission.DifferentialGeometry.Homology.fundamentalSimplexChain_straightening


@[simp]
theorem barycentricSimplexChain_zero :
    barycentricSimplexChain R 0 = fundamentalSimplexChain R 0 := by
  have hid := HomologicalComplex.congr_hom (simplexSupportedChainIso R 0).hom_inv_id 0
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hid
  simp only [barycentricSimplexChain, simplexSubdivision, HomologicalComplex.comp_f,
    smallAffineSubdivision_f, smallAffineSubdivisionMap_zero, Category.id_comp,
    hid, Category.comp_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.barycentricSimplexChain_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.barycentricSimplexChain_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.barycentricSimplexChain_zero ``Submission.DifferentialGeometry.Homology.barycentricSimplexChain_zero


@[simp]
theorem barycentricSimplexHomotopyChain_zero : barycentricSimplexHomotopyChain R 0 = 0 := by
  simp only [barycentricSimplexHomotopyChain, simplexSubdivisionHomotopy,
    Homotopy.compRight_hom, Homotopy.compLeft_hom, smallAffineSubdivisionHomotopy_hom,
    smallAffineSubdivisionHomotopyMap_zero, _root_.CategoryTheory.Limits.comp_zero, _root_.CategoryTheory.Limits.zero_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.barycentricSimplexHomotopyChain_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.barycentricSimplexHomotopyChain_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.barycentricSimplexHomotopyChain_zero ``Submission.DifferentialGeometry.Homology.barycentricSimplexHomotopyChain_zero


theorem barycentricSimplexHomotopyChain_boundary (n : ℕ) :
    barycentricSimplexChain R (n + 1) - fundamentalSimplexChain R (n + 1) =
      (∑ i : Fin (n + 2), (-1) ^ i.val •
        (barycentricSimplexHomotopyChain R n ≫
          (SSet.chainComplexMap (TopCat.toSSet.map
            (SimplexCategory.toTop.map (SimplexCategory.δ i))) R).f (n + 1))) +
      barycentricSimplexHomotopyChain R (n + 1) ≫
        ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n + 1⦌)).chainComplex R).d (n + 2) (n + 1) := by
  have h := (simplexSubdivisionHomotopy R (n + 1)).comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  have he := congrArg (fun q ↦ fundamentalSimplexChain R (n + 1) ≫ q) h
  simp only [Preadditive.comp_add] at he
  rw [fundamentalSimplexChain_straightening] at he
  apply (sub_eq_iff_eq_add).mpr
  change fundamentalSimplexChain R (n + 1) ≫ (simplexSubdivision R (n + 1)).f (n + 1) = _
  rw [he]
  congr 2
  rw [← Category.assoc, fundamentalSimplexChain_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro i _
  rw [← simplexSubdivisionHomotopy_naturality R (SimplexCategory.δ i) n]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.barycentricSimplexHomotopyChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.barycentricSimplexHomotopyChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.barycentricSimplexHomotopyChain_boundary ``Submission.DifferentialGeometry.Homology.barycentricSimplexHomotopyChain_boundary

end DifferentialGeometry.Homology
