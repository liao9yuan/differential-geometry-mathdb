import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Homotopy.Contractible
import Submission.DifferentialGeometry.Topology.SphereSeparation.SphereCohomology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.ZeroObject

namespace DifferentialGeometry.Topology.SphereSeparation



private noncomputable def dualHomotopyComponent
    {C D : ChainComplex (ModuleCat ℤ) ℕ} {f g : C ⟶ D}
    (h : _root_.Homotopy f g) (i j : ℕ) :
    (dualCochainComplex D).X i ⟶ (dualCochainComplex C).X j :=
  ModuleCat.ofHom (dualDifferential (h.hom j i))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualHomotopyComponent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.dualHomotopyComponent target :: scope.openDecls } }

@[simp]
private theorem dualHomotopyComponent_apply
    {C D : ChainComplex (ModuleCat ℤ) ℕ} {f g : C ⟶ D}
    (h : _root_.Homotopy f g) (i j : ℕ)
    (φ : integerDual (D.X i)) (x : C.X j) :
    (show integerDual (C.X j) from dualHomotopyComponent h i j φ) x =
      φ (h.hom j i x) :=
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualHomotopyComponent_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.dualHomotopyComponent_apply target :: scope.openDecls } }

@[simp]
private theorem dualCochainMap_apply
    {C D : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) (i : ℕ)
    (φ : integerDual (D.X i)) (x : C.X i) :
    (show integerDual (C.X i) from (dualCochainMap f).f i φ) x =
      φ (f.f i x) :=
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualCochainMap_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.dualCochainMap_apply target :: scope.openDecls } }

private theorem dualHomotopyPointwise
    {C D : ChainComplex (ModuleCat ℤ) ℕ} {f g : C ⟶ D}
    (h : _root_.Homotopy f g) (i : ℕ)
    (φ : integerDual (D.X i)) (x : C.X i) :
    φ (f.f i x) =
      φ ((h.hom i (i + 1) ≫ D.d (i + 1) i) x) +
        φ ((C.d i (i - 1) ≫ h.hom (i - 1) i) x) +
          φ (g.f i x) := by
  have hi := h.comm i
  rw [dNext_nat C D i h.hom,
    prevD_eq h.hom
      (show (ComplexShape.down ℕ).Rel (i + 1) i by simp)] at hi
  rw [hi]
  simp only [ModuleCat.hom_add, LinearMap.add_apply, map_add]
  ac_rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualHomotopyPointwise
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.dualHomotopyPointwise target :: scope.openDecls } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable def dualCochainHomotopy
    {C D : ChainComplex (ModuleCat ℤ) ℕ} {f g : C ⟶ D}
    (h : _root_.Homotopy f g) :
    _root_.Homotopy (dualCochainMap f) (dualCochainMap g) where
  hom i j := dualHomotopyComponent h i j
  zero i j hij := by
    ext φ
    apply LinearMap.ext
    intro x
    change (show integerDual (D.X i) from φ) (h.hom j i x) = 0
    rw [h.zero j i]
    · simp
    · simpa only [ComplexShape.up_Rel, ComplexShape.down_Rel] using hij
  comm i := by
    rw [dNext_eq (dualHomotopyComponent h)
      (show (ComplexShape.up ℕ).Rel i (i + 1) by simp)]
    cases i with
    | zero =>
      rw [prevD_eq_zero (dualHomotopyComponent h) 0 (by
        simp [CochainComplex.prev_nat_zero])]
      simp only [dualCochainComplex, add_zero, Nat.reduceAdd]
      change ModuleCat.ofHom (dualDifferential (f.f 0)) =
        ModuleCat.ofHom (dualDifferential (D.d 1 0)) ≫
            ModuleCat.ofHom (dualDifferential (h.hom 0 1)) +
          ModuleCat.ofHom (dualDifferential (g.f 0))
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro x
      change φ (f.f 0 x) =
        φ ((h.hom 0 1 ≫ D.d 1 0) x) + φ (g.f 0 x)
      have hd00 : C.d 0 0 = 0 := C.shape 0 0 (by simp)
      simpa [hd00] using dualHomotopyPointwise h 0 φ x
    | succ i =>
      rw [prevD_eq (dualHomotopyComponent h)
        (show (ComplexShape.up ℕ).Rel i (i + 1) by simp)]
      simp only [dualCochainComplex, CochainComplex.of_d]
      change ModuleCat.ofHom (dualDifferential (f.f (i + 1))) =
        ModuleCat.ofHom (dualDifferential (D.d (i + 2) (i + 1))) ≫
            ModuleCat.ofHom (dualDifferential (h.hom (i + 1) (i + 2))) +
          ModuleCat.ofHom (dualDifferential (h.hom i (i + 1))) ≫
            ModuleCat.ofHom (dualDifferential (C.d (i + 1) i)) +
          ModuleCat.ofHom (dualDifferential (g.f (i + 1)))
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro x
      change φ (f.f (i + 1) x) =
        φ ((h.hom (i + 1) (i + 2) ≫ D.d (i + 2) (i + 1)) x) +
          φ ((C.d (i + 1) i ≫ h.hom i (i + 1)) x) +
            φ (g.f (i + 1) x)
      have hplus : i + 1 + 1 = i + 2 := by omega
      have hminus : i + 1 - 1 = i := by omega
      have hp := dualHomotopyPointwise h (i + 1) φ x
      rw [hplus, hminus] at hp
      exact hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.dualCochainHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.dualCochainHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.dualCochainHomotopy ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualCochainHomotopy

noncomputable def dualCochainHomotopyEquiv
    {C D : ChainComplex (ModuleCat ℤ) ℕ}
    (e : HomotopyEquiv C D) :
    HomotopyEquiv (dualCochainComplex D) (dualCochainComplex C) where
  hom := dualCochainMap e.hom
  inv := dualCochainMap e.inv
  homotopyHomInvId := by
    rw [← dualCochainMap_comp]
    exact (dualCochainHomotopy e.homotopyInvHomId).trans
      (_root_.Homotopy.ofEq (dualCochainMap_id _))
  homotopyInvHomId := by
    rw [← dualCochainMap_comp]
    exact (dualCochainHomotopy e.homotopyHomInvId).trans
      (_root_.Homotopy.ofEq (dualCochainMap_id _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.dualCochainHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.dualCochainHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.dualCochainHomotopyEquiv ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualCochainHomotopyEquiv



private noncomputable abbrev comparisonSingularChainComplex (X : TopCat) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj X

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.comparisonSingularChainComplex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.comparisonSingularChainComplex target :: scope.openDecls } }

noncomputable abbrev integerSingularChains (X : TopCat) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  comparisonSingularChainComplex X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerSingularChains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerSingularChains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerSingularChains ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerSingularChains

noncomputable def singularChainHomotopyEquivOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    HomotopyEquiv (comparisonSingularChainComplex (TopCat.of X))
      (comparisonSingularChainComplex (TopCat.of Y)) where
  hom := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom e.toFun)
  inv := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    rw [← Functor.map_comp]
    let H := Classical.choice e.left_inv
    let H' : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun)
        (𝟙 (TopCat.of X)) := H
    exact (TopCat.Homotopy.singularChainComplexFunctorObjMap H'
      (ModuleCat.of ℤ ℤ)).trans (_root_.Homotopy.ofEq
        (CategoryTheory.Functor.map_id
          ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)) (TopCat.of X)))
  homotopyInvHomId := by
    rw [← Functor.map_comp]
    let H := Classical.choice e.right_inv
    let H' : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun)
        (𝟙 (TopCat.of Y)) := H
    exact (TopCat.Homotopy.singularChainComplexFunctorObjMap H'
      (ModuleCat.of ℤ ℤ)).trans (_root_.Homotopy.ofEq
        (CategoryTheory.Functor.map_id
          ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)) (TopCat.of Y)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainHomotopyEquivOfHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainHomotopyEquivOfHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainHomotopyEquivOfHomotopyEquiv ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainHomotopyEquivOfHomotopyEquiv

noncomputable def singularCochainHomotopyEquivOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    HomotopyEquiv (singularCochainComplex (TopCat.of Y))
      (singularCochainComplex (TopCat.of X)) :=
  dualCochainHomotopyEquiv
    (singularChainHomotopyEquivOfHomotopyEquiv e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularCochainHomotopyEquivOfHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularCochainHomotopyEquivOfHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularCochainHomotopyEquivOfHomotopyEquiv ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularCochainHomotopyEquivOfHomotopyEquiv

noncomputable def singularCohomologyIsoOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    singularCohomology (TopCat.of Y) n ≅
      singularCohomology (TopCat.of X) n :=
  (singularCochainHomotopyEquivOfHomotopyEquiv e).toHomologyIso n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularCohomologyIsoOfHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularCohomologyIsoOfHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularCohomologyIsoOfHomotopyEquiv ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularCohomologyIsoOfHomotopyEquiv

noncomputable def singularCohomologyIsoOfChainComparison
    (X : TopCat) (C : ChainComplex (ModuleCat ℤ) ℕ)
    (comparison : HomotopyEquiv (integerSingularChains X) C) (n : ℕ) :
    singularCohomology X n ≅ (dualCochainComplex C).homology n :=
  (dualCochainHomotopyEquiv comparison).symm.toHomologyIso n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularCohomologyIsoOfChainComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularCohomologyIsoOfChainComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularCohomologyIsoOfChainComparison ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularCohomologyIsoOfChainComparison


noncomputable def singularCohomologyUnitTwoIsoZero :
    singularCohomology (TopCat.of Unit) 2 ≅ 0 :=
  (singularCohomologyIsoOfHomeomorph
      (Homeomorph.homeomorphOfUnique Unit PUnit) 2).symm ≪≫
    singularCohomologyPUnitTwoIsoZero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularCohomologyUnitTwoIsoZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularCohomologyUnitTwoIsoZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularCohomologyUnitTwoIsoZero ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularCohomologyUnitTwoIsoZero

theorem isZero_singularCohomology_two_of_contractible
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    IsZero (singularCohomology (TopCat.of X) 2) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  exact IsZero.of_iso (_root_.CategoryTheory.Limits.isZero_zero (ModuleCat ℤ))
    ((singularCohomologyIsoOfHomotopyEquiv e 2).symm ≪≫
      singularCohomologyUnitTwoIsoZero)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isZero_singularCohomology_two_of_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isZero_singularCohomology_two_of_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isZero_singularCohomology_two_of_contractible ``Submission.DifferentialGeometry.Topology.SphereSeparation.isZero_singularCohomology_two_of_contractible



noncomputable def sphereTwoPunctureHomeomorph (p : SphereTwo) :
    ({p}ᶜ : Set SphereTwo) ≃ₜ EuclideanSpace ℝ (Fin 2) := by
  letI : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by
    norm_num [EuclideanThree, Module.finrank_fin_fun]⟩
  exact
    (Homeomorph.setCongr (stereographic'_source (n := 2) p).symm).trans
      ((stereographic' 2 p).toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (stereographic'_target (n := 2) p)).trans
          (Homeomorph.Set.univ _)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureHomeomorph ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureHomeomorph


theorem sphereTwoPuncture_contractible (p : SphereTwo) :
    ContractibleSpace ({p}ᶜ : Set SphereTwo) :=
  (sphereTwoPunctureHomeomorph p).contractibleSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoPuncture_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoPuncture_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoPuncture_contractible ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoPuncture_contractible

theorem isZero_singularCohomology_sphereTwoPuncture_two (p : SphereTwo) :
    IsZero (singularCohomology (TopCat.of ({p}ᶜ : Set SphereTwo)) 2) := by
  let _ := sphereTwoPuncture_contractible p
  exact isZero_singularCohomology_two_of_contractible _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isZero_singularCohomology_sphereTwoPuncture_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isZero_singularCohomology_sphereTwoPuncture_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isZero_singularCohomology_sphereTwoPuncture_two ``Submission.DifferentialGeometry.Topology.SphereSeparation.isZero_singularCohomology_sphereTwoPuncture_two



noncomputable def singularChainsPUnitHomotopyEquivSingleZero :
    HomotopyEquiv (integerSingularChains (TopCat.of PUnit))
      ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0).obj
        (ModuleCat.of ℤ ℤ)) :=
  (HomotopyEquiv.ofIso
    ((AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) (TopCat.of PUnit)) ≪≫
      ChainComplex.alternatingConst.mapIso
        (_root_.CategoryTheory.Limits.coproductUniqueIso (fun _ : PUnit ↦ ModuleCat.of ℤ ℤ)))).trans
    (ChainComplex.alternatingConstHomotopyEquiv (ModuleCat.of ℤ ℤ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsPUnitHomotopyEquivSingleZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsPUnitHomotopyEquivSingleZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsPUnitHomotopyEquivSingleZero ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsPUnitHomotopyEquivSingleZero

noncomputable def singularChainsHomotopyEquivSingleZeroOfContractible
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    HomotopyEquiv (integerSingularChains (TopCat.of X))
      ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0).obj
        (ModuleCat.of ℤ ℤ)) := by
  let e : ContinuousMap.HomotopyEquiv X PUnit :=
    (Classical.choice (ContractibleSpace.hequiv_unit X)).trans
      (Homeomorph.homeomorphOfUnique Unit PUnit).toHomotopyEquiv
  exact (singularChainHomotopyEquivOfHomotopyEquiv e).trans
    singularChainsPUnitHomotopyEquivSingleZero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsHomotopyEquivSingleZeroOfContractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsHomotopyEquivSingleZeroOfContractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsHomotopyEquivSingleZeroOfContractible ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsHomotopyEquivSingleZeroOfContractible

noncomputable def singularChainsSphereTwoPunctureHomotopyEquivSingleZero
    (p : SphereTwo) :
    HomotopyEquiv
      (integerSingularChains (TopCat.of ({p}ᶜ : Set SphereTwo)))
      ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0).obj
        (ModuleCat.of ℤ ℤ)) := by
  let _ := sphereTwoPuncture_contractible p
  exact singularChainsHomotopyEquivSingleZeroOfContractible _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsSphereTwoPunctureHomotopyEquivSingleZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsSphereTwoPunctureHomotopyEquivSingleZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsSphereTwoPunctureHomotopyEquivSingleZero ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsSphereTwoPunctureHomotopyEquivSingleZero



def integerDualIntLinearEquiv :
    integerDual (ModuleCat.of ℤ ℤ) ≃ₗ[ℤ] ℤ where
  toFun f := f 1
  invFun z := LinearMap.mulLeft ℤ z
  left_inv f := by
    apply LinearMap.ext
    intro x
    change f 1 * x = f x
    rw [mul_comm, ← smul_eq_mul, ← f.map_smul]
    simp
  right_inv z := by simp
  map_add' f g := by simp
  map_smul' z f := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerDualIntLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerDualIntLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerDualIntLinearEquiv ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerDualIntLinearEquiv

noncomputable def sphereTwoCellularChainComplex :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0).obj
      (ModuleCat.of ℤ ℤ)) ⊞
    ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 2).obj
      (ModuleCat.of ℤ ℤ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoCellularChainComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoCellularChainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoCellularChainComplex ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoCellularChainComplex

private noncomputable def dualSingleCellDegreeIso (n i : ℕ) :
    (dualCochainComplex
        ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) n).obj
          (ModuleCat.of ℤ ℤ))).X i ≅
      ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.up ℕ) n).obj
        (ModuleCat.of ℤ ℤ)).X i := by
  by_cases h : i = n
  · subst i
    change ModuleCat.of ℤ
        (integerDual
          (((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) n).obj
            (ModuleCat.of ℤ ℤ)).X n)) ≅
      ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.up ℕ) n).obj
        (ModuleCat.of ℤ ℤ)).X n
    rw [HomologicalComplex.single_obj_X_self,
      HomologicalComplex.single_obj_X_self]
    exact integerDualIntLinearEquiv.toModuleIso
  · let C := (HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) n).obj
      (ModuleCat.of ℤ ℤ)
    let D := (HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.up ℕ) n).obj
      (ModuleCat.of ℤ ℤ)
    have hC : _root_.CategoryTheory.Limits.IsZero (C.X i) :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) n
        (ModuleCat.of ℤ ℤ) i h
    letI : Subsingleton (C.X i) := ModuleCat.subsingleton_of_isZero hC
    have hdual : _root_.CategoryTheory.Limits.IsZero (ModuleCat.of ℤ (integerDual (C.X i))) :=
      ModuleCat.isZero_of_subsingleton _
    have hD : _root_.CategoryTheory.Limits.IsZero (D.X i) :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) n
        (ModuleCat.of ℤ ℤ) i h
    exact hdual.isoZero ≪≫ hD.isoZero.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualSingleCellDegreeIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.dualSingleCellDegreeIso target :: scope.openDecls } }

noncomputable def dualSingleCellIso (n : ℕ) :
    dualCochainComplex
        ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) n).obj
          (ModuleCat.of ℤ ℤ)) ≅
      (HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.up ℕ) n).obj
        (ModuleCat.of ℤ ℤ) :=
  HomologicalComplex.Hom.isoOfComponents
    (dualSingleCellDegreeIso n) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      have hd :
          (dualCochainComplex
            ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) n).obj
              (ModuleCat.of ℤ ℤ))).d i (i + 1) = 0 := by
        simp only [dualCochainComplex, CochainComplex.of_d]
        rw [HomologicalComplex.single_obj_d]
        ext φ x
        change φ
          ((0 :
            (((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) n).obj
              (ModuleCat.of ℤ ℤ)).X (i + 1) ⟶
             ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) n).obj
              (ModuleCat.of ℤ ℤ)).X i)) x) = 0
        simp
      rw [HomologicalComplex.single_obj_d, _root_.CategoryTheory.Limits.comp_zero, hd, _root_.CategoryTheory.Limits.zero_comp])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.dualSingleCellIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.dualSingleCellIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.dualSingleCellIso ``Submission.DifferentialGeometry.Topology.SphereSeparation.dualSingleCellIso

noncomputable def sphereTwoCellularChainDualIso :
    dualCochainComplex sphereTwoCellularChainComplex ≅
      sphereTwoCellularCochainComplex :=
  dualCochainComplexBiprodIso
      ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0).obj
        (ModuleCat.of ℤ ℤ))
      ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 2).obj
        (ModuleCat.of ℤ ℤ)) ≪≫
    biprod.mapIso (dualSingleCellIso 0) (dualSingleCellIso 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoCellularChainDualIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoCellularChainDualIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoCellularChainDualIso ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoCellularChainDualIso

noncomputable def sphereTwoCohomologyTwoIsoIntOfCellularChainComparison
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex) :
    singularCohomology (TopCat.of SphereTwo) 2 ≅ ModuleCat.of ℤ ℤ :=
  sphereTwoCohomologyTwoIsoIntOfCellularComparison
    ((dualCochainHomotopyEquiv comparison).symm.trans
      (HomotopyEquiv.ofIso sphereTwoCellularChainDualIso))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoCohomologyTwoIsoIntOfCellularChainComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoCohomologyTwoIsoIntOfCellularChainComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoCohomologyTwoIsoIntOfCellularChainComparison ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoCohomologyTwoIsoIntOfCellularChainComparison

end DifferentialGeometry.Topology.SphereSeparation
