import Submission.DifferentialGeometry.Topology.Homology.Reduced

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
noncomputable section
universe u
namespace DifferentialGeometry.Homology
variable {k : Type u} [Ring k] (R : ModuleCat.{u} k) (X : TopCat.{u})
private def positiveMap (n : ℕ) :
    (augmentedSingularChainComplex R X).sc' (n + 3) (n + 2) (n + 1) ⟶
      ((TopCat.toSSet.obj X).chainComplex R).sc' (n + 2) (n + 1) n where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by
    change 𝟙 _ ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 2) (n + 1) =
      ((TopCat.toSSet.obj X).chainComplex R).d (n + 2) (n + 1) ≫ 𝟙 _
    simp
  comm₂₃ := by
    change 𝟙 _ ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n =
      ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫ 𝟙 _
    simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.positiveMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.positiveMap target :: scope.openDecls } }

@[reassoc]
theorem reducedSingularHomologySuccIso_cycle (n : ℕ) {A : ModuleCat.{u} k}
    (c : A ⟶ ((TopCat.toSSet.obj X).chainComplex R).X (n + 1))
    (hc : c ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n = 0) :
    (augmentedSingularChainComplex R X).liftCycles (i := n + 2) c (n + 1) (by simp) hc ≫
      (augmentedSingularChainComplex R X).homologyπ (n + 2) ≫
      (reducedSingularHomologySuccIso R X n).hom =
    ((TopCat.toSSet.obj X).chainComplex R).liftCycles c n (by simp) hc ≫
      ((TopCat.toSSet.obj X).chainComplex R).homologyπ (n + 1) := by
  unfold reducedSingularHomologySuccIso
  simp only [Iso.trans_hom, Iso.symm_hom, ShortComplex.homologyMapIso_hom,
    HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.homologyπ_naturality_assoc,
    HomologicalComplex.π_homologyIsoSc'_inv]
  simp only [← Category.assoc]
  congr 1
  apply (_root_.CategoryTheory.cancel_mono (((TopCat.toSSet.obj X).chainComplex R).iCycles (n + 1))).mp
  simp only [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles,
    HomologicalComplex.liftCycles_i]
  change _ ≫ _ ≫ ShortComplex.cyclesMap (positiveMap R X n) ≫ _ = c
  have h := congrArg (fun z ↦
    (augmentedSingularChainComplex R X).liftCycles (i := n + 2) c (n + 1) (by simp) hc ≫
      ((augmentedSingularChainComplex R X).cyclesIsoSc' (n + 3) (n + 2) (n + 1)
        (by simp) (by simp)).hom ≫ z) (ShortComplex.cyclesMap_i (positiveMap R X n))
  refine h.trans ?_
  have hId := congrArg (fun z ↦
    (augmentedSingularChainComplex R X).liftCycles (i := n + 2) c (n + 1) (by simp) hc ≫
      ((augmentedSingularChainComplex R X).cyclesIsoSc' (n + 3) (n + 2) (n + 1)
        (by simp) (by simp)).hom ≫ z)
    (Category.comp_id ((augmentedSingularChainComplex R X).sc' (n + 3) (n + 2) (n + 1)).iCycles)
  have hC := congrArg (fun z ↦
    (augmentedSingularChainComplex R X).liftCycles (i := n + 2) c (n + 1) (by simp) hc ≫ z)
    ((augmentedSingularChainComplex R X).cyclesIsoSc'_hom_iCycles
      (n + 3) (n + 2) (n + 1) (by simp) (by simp))
  exact hId.trans (hC.trans ((augmentedSingularChainComplex R X).liftCycles_i (i := n + 2) c (n + 1) (by simp) hc))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.reducedSingularHomologySuccIso_cycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.reducedSingularHomologySuccIso_cycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.reducedSingularHomologySuccIso_cycle ``Submission.DifferentialGeometry.Homology.reducedSingularHomologySuccIso_cycle

private theorem cycleClass_naturality
    {K L : ChainComplex (ModuleCat.{u} k) ℕ} (φ : K ⟶ L)
    {A : ModuleCat.{u} k} (i j : ℕ) (hj : (ComplexShape.down ℕ).next i = j)
    (c : A ⟶ K.X i) (hc : c ≫ K.d i j = 0) :
    K.liftCycles c j hj hc ≫ K.homologyπ i ≫ HomologicalComplex.homologyMap φ i =
      L.liftCycles (c ≫ φ.f i) j hj
        (by rw [Category.assoc, φ.comm, ← Category.assoc, hc, _root_.CategoryTheory.Limits.zero_comp]) ≫ L.homologyπ i := by
  rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.cycleClass_naturality
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.cycleClass_naturality target :: scope.openDecls } }

variable {X} {Y : TopCat.{u}}

@[reassoc]
theorem reducedSingularHomologySuccIso_naturality (f : X ⟶ Y) (n : ℕ) :
    reducedSingularHomologyMap R f (n + 1) ≫ (reducedSingularHomologySuccIso R Y n).hom =
      (reducedSingularHomologySuccIso R X n).hom ≫
        SSet.homologyMap (TopCat.toSSet.map f) R (n + 1) := by
  let c : (augmentedSingularChainComplex R X).cycles (n + 2) ⟶
      ((TopCat.toSSet.obj X).chainComplex R).X (n + 1) :=
    (augmentedSingularChainComplex R X).iCycles (n + 2)
  have hc : c ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n = 0 :=
    (augmentedSingularChainComplex R X).iCycles_d (n + 2) (n + 1)
  let l := (augmentedSingularChainComplex R X).liftCycles
    (i := n + 2) c (n + 1) (by simp) hc
  have hl : l = 𝟙 _ := by
    apply (_root_.CategoryTheory.cancel_mono ((augmentedSingularChainComplex R X).iCycles (n + 2))).mp
    exact ((augmentedSingularChainComplex R X).liftCycles_i
      (i := n + 2) c (n + 1) (by simp) hc).trans (Category.id_comp _).symm
  have : _root_.CategoryTheory.Epi l := by rw [hl]; infer_instance
  apply (_root_.CategoryTheory.cancel_epi (l ≫ (augmentedSingularChainComplex R X).homologyπ (n + 2))).mp
  let φ := SSet.chainComplexMap (TopCat.toSSet.map f) R
  have hc' : (c ≫ φ.f (n + 1)) ≫ ((TopCat.toSSet.obj Y).chainComplex R).d (n + 1) n = 0 := by
    rw [Category.assoc, φ.comm, ← Category.assoc, hc, _root_.CategoryTheory.Limits.zero_comp]
  have ha := cycleClass_naturality (augmentedSingularChainMap R f)
    (n + 2) (n + 1) (by simp) c
    (show c ≫ (augmentedSingularChainComplex R X).d (n + 2) (n + 1) = 0 from hc)
  have ho := cycleClass_naturality φ (n + 1) n (by simp) c hc
  have hx := reducedSingularHomologySuccIso_cycle R X n c hc
  have hy := reducedSingularHomologySuccIso_cycle R Y n (c ≫ φ.f (n + 1)) hc'
  have hleft := congrArg (fun z ↦ z ≫ (reducedSingularHomologySuccIso R Y n).hom) ha
  have hright := congrArg (fun z ↦ z ≫ HomologicalComplex.homologyMap φ (n + 1)) hx
  have hleft' := hleft.trans (by simpa only [Category.assoc] using! hy)
  have hright' := (by simpa only [Category.assoc] using! ho.symm.trans hright.symm)
  simpa only [Category.assoc] using! hleft'.trans hright'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.reducedSingularHomologySuccIso_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.reducedSingularHomologySuccIso_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.reducedSingularHomologySuccIso_naturality ``Submission.DifferentialGeometry.Homology.reducedSingularHomologySuccIso_naturality

end DifferentialGeometry.Homology
