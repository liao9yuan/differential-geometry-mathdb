import Submission.DifferentialGeometry.Topology.Homology.Algebra.Augment

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits
namespace DifferentialGeometry.HomologicalComplex
variable {C : Type*} [Category* C] [Abelian C]
  {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}
  (f : K ⟶ L) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
private theorem homologyIsoSc'_naturality :
    _root_.HomologicalComplex.homologyMap f j ≫ (L.homologyIsoSc' i j k hi hk).hom =
      (K.homologyIsoSc' i j k hi hk).hom ≫
        ShortComplex.homologyMap ((_root_.HomologicalComplex.shortComplexFunctor' C c i j k).map f) := by
  subst i k
  simp only [_root_.HomologicalComplex.homologyIsoSc'_eq_refl, Iso.refl_hom]
  change _root_.HomologicalComplex.homologyMap f j ≫ 𝟙 (L.homology j) =
    𝟙 (K.homology j) ≫ _root_.HomologicalComplex.homologyMap f j
  simp only [Category.comp_id,Category.id_comp]

run_cmd do
  let target := ``Submission.DifferentialGeometry.HomologicalComplex.homologyIsoSc'_naturality
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.HomologicalComplex.homologyIsoSc'_naturality target :: scope.openDecls } }

end DifferentialGeometry.HomologicalComplex

namespace DifferentialGeometry.ChainComplex
variable {C : Type*} [Category* C] [Abelian C]
  {K L : ChainComplex C ℕ} {A B : C}
  {ε : K.X 0 ⟶ A} {η : L.X 0 ⟶ B}
  (hε : K.d 1 0 ≫ ε = 0) (hη : L.d 1 0 ≫ η = 0)
private def augmentPositiveShortComplexIso (n : ℕ) :
    (K.augment ε hε).sc' (n + 3) (n + 2) (n + 1) ≅ K.sc' (n + 2) (n + 1) n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by change 𝟙 _ ≫ K.d _ _ = K.d _ _ ≫ 𝟙 _; simp)
    (by change 𝟙 _ ≫ K.d _ _ = K.d _ _ ≫ 𝟙 _; simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.ChainComplex.augmentPositiveShortComplexIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.ChainComplex.augmentPositiveShortComplexIso target :: scope.openDecls } }


def augmentHomologySuccIso (n : ℕ) :
    (K.augment ε hε).homology (n + 2) ≅ K.homology (n + 1) :=
  (K.augment ε hε).homologyIsoSc' (n + 3) (n + 2) (n + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (augmentPositiveShortComplexIso hε n) ≪≫
      (K.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ChainComplex.augmentHomologySuccIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ChainComplex.augmentHomologySuccIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ChainComplex.augmentHomologySuccIso ``Submission.DifferentialGeometry.ChainComplex.augmentHomologySuccIso

private theorem augmentPositiveShortComplexIso_naturality (f : K ⟶ L) (a : A ⟶ B)
    (w : f.f 0 ≫ η = ε ≫ a) (n : ℕ) :
    ((_root_.HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ)
      (n + 3) (n + 2) (n + 1)).map (augmentMap hε hη f a w)) ≫
      (augmentPositiveShortComplexIso hη n).hom =
    (augmentPositiveShortComplexIso hε n).hom ≫
      ((_root_.HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ)
        (n + 2) (n + 1) n).map f) := by
  ext
  · change f.f (n + 2) ≫ 𝟙 _ = 𝟙 _ ≫ f.f (n + 2); simp
  · change f.f (n + 1) ≫ 𝟙 _ = 𝟙 _ ≫ f.f (n + 1); simp
  · change f.f n ≫ 𝟙 _ = 𝟙 _ ≫ f.f n; simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.ChainComplex.augmentPositiveShortComplexIso_naturality
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.ChainComplex.augmentPositiveShortComplexIso_naturality target :: scope.openDecls } }


@[reassoc]
theorem augmentHomologySuccIso_naturality (f : K ⟶ L) (a : A ⟶ B)
    (w : f.f 0 ≫ η = ε ≫ a) (n : ℕ) :
    _root_.HomologicalComplex.homologyMap (augmentMap hε hη f a w) (n + 2) ≫
      (augmentHomologySuccIso hη n).hom =
    (augmentHomologySuccIso hε n).hom ≫ _root_.HomologicalComplex.homologyMap f (n + 1) := by
  have hshort := congrArg (fun g => (ShortComplex.homologyMap g :
    ((K.augment ε hε).sc' (n + 3) (n + 2) (n + 1)).homology ⟶
      (L.sc' (n + 2) (n + 1) n).homology))
    (augmentPositiveShortComplexIso_naturality hε hη f a w n)
  simp only [ShortComplex.homologyMap_comp] at hshort
  have hinv : (K.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).inv ≫
      _root_.HomologicalComplex.homologyMap f (n + 1) =
    ShortComplex.homologyMap ((_root_.HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ)
      (n + 2) (n + 1) n).map f) ≫
      (L.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).inv := by
    apply (_root_.CategoryTheory.cancel_epi (K.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc,
      ← DifferentialGeometry.HomologicalComplex.homologyIsoSc'_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp only [augmentHomologySuccIso, Iso.trans_hom, Iso.symm_hom]
  simp only [ShortComplex.homologyMapIso_hom]
  rw [← Category.assoc, DifferentialGeometry.HomologicalComplex.homologyIsoSc'_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (ShortComplex.homologyMap _), hshort]
  simp only [Category.assoc]
  rw [← hinv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ChainComplex.augmentHomologySuccIso_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ChainComplex.augmentHomologySuccIso_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ChainComplex.augmentHomologySuccIso_naturality ``Submission.DifferentialGeometry.ChainComplex.augmentHomologySuccIso_naturality
end DifferentialGeometry.ChainComplex
