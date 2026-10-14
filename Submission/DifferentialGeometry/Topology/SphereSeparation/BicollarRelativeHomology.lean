import Mathlib.Analysis.Convex.Contractible
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Submission.DifferentialGeometry.Topology.SphereSeparation.BicollarOrientation
import Submission.DifferentialGeometry.Topology.SphereSeparation.ComponentCount
import Submission.DifferentialGeometry.Topology.SphereSeparation.ContractibleAmbient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Set

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem bicollar_finTwo_eq_zero_or_one (i : Fin 2) :
    i = 0 ∨ i = 1 := by
  refine Fin.cases (Or.inl rfl) (fun j ↦ ?_) i
  exact Fin.cases (Or.inr rfl) (fun k ↦ Fin.elim0 k) j

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.bicollar_finTwo_eq_zero_or_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.bicollar_finTwo_eq_zero_or_one target :: scope.openDecls } }


def centralSliceComplementLower {a : ℝ} (ha : 0 < a) :
    Set ((zeroSliceDomain ha)ᶜ : Set (SphereTwo × AxialInterval a)) :=
  {x | x.1.2 < axialZero ha}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementLower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementLower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementLower ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementLower


def centralSliceComplementUpper {a : ℝ} (ha : 0 < a) :
    Set ((zeroSliceDomain ha)ᶜ : Set (SphereTwo × AxialInterval a)) :=
  {x | axialZero ha < x.1.2}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementUpper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementUpper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementUpper ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementUpper

private theorem centralSliceComplementLower_isOpen {a : ℝ} (ha : 0 < a) :
    IsOpen (centralSliceComplementLower ha) := by
  exact isOpen_lt (by fun_prop) (by fun_prop)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementLower_isOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementLower_isOpen target :: scope.openDecls } }

private theorem centralSliceComplementUpper_isOpen {a : ℝ} (ha : 0 < a) :
    IsOpen (centralSliceComplementUpper ha) := by
  exact isOpen_lt (by fun_prop) (by fun_prop)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementUpper_isOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementUpper_isOpen target :: scope.openDecls } }

private theorem centralSliceComplementLower_compl {a : ℝ} (ha : 0 < a) :
    (centralSliceComplementLower ha)ᶜ = centralSliceComplementUpper ha := by
  ext x
  simp only [centralSliceComplementLower, centralSliceComplementUpper,
    _root_.Set.mem_compl_iff, Set.mem_ofPred_eq]
  have hx : x.1.2 ≠ axialZero ha := by
    intro hx
    apply x.2
    exact ⟨Set.mem_univ _, hx⟩
  constructor
  · intro h
    exact lt_of_le_of_ne (le_of_not_gt h) hx.symm
  · exact fun h₁ h₂ ↦ (not_lt_of_ge (le_of_lt h₁)) h₂

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementLower_compl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementLower_compl target :: scope.openDecls } }

private theorem centralSliceComplementUpper_compl {a : ℝ} (ha : 0 < a) :
    (centralSliceComplementUpper ha)ᶜ = centralSliceComplementLower ha := by
  rw [← centralSliceComplementLower_compl ha, compl_compl]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementUpper_compl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementUpper_compl target :: scope.openDecls } }

private theorem centralSliceComplementLower_isClopen {a : ℝ} (ha : 0 < a) :
    IsClopen (centralSliceComplementLower ha) := by
  refine ⟨?_, centralSliceComplementLower_isOpen ha⟩
  rw [← centralSliceComplementUpper_compl]
  exact (centralSliceComplementUpper_isOpen ha).isClosed_compl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementLower_isClopen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementLower_isClopen target :: scope.openDecls } }

private theorem centralSliceComplementUpper_isClopen {a : ℝ} (ha : 0 < a) :
    IsClopen (centralSliceComplementUpper ha) := by
  refine ⟨?_, centralSliceComplementUpper_isOpen ha⟩
  rw [← centralSliceComplementLower_compl]
  exact (centralSliceComplementLower_isOpen ha).isClosed_compl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementUpper_isClopen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementUpper_isClopen target :: scope.openDecls } }

private theorem subtypeVal_image_centralSliceComplementLower {a : ℝ}
    (ha : 0 < a) :
    Subtype.val '' centralSliceComplementLower ha =
      lowerHalfDomain (axialZero ha) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Set.mem_univ _, hy⟩
  · intro hx
    refine ⟨⟨x, ?_⟩, hx.2, rfl⟩
    intro hzero
    exact (ne_of_lt hx.2) hzero.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.subtypeVal_image_centralSliceComplementLower
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.subtypeVal_image_centralSliceComplementLower target :: scope.openDecls } }

private theorem subtypeVal_image_centralSliceComplementUpper {a : ℝ}
    (ha : 0 < a) :
    Subtype.val '' centralSliceComplementUpper ha =
      upperHalfDomain (axialZero ha) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Set.mem_univ _, hy⟩
  · intro hx
    refine ⟨⟨x, ?_⟩, hx.2, rfl⟩
    intro hzero
    exact (ne_of_gt hx.2) hzero.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.subtypeVal_image_centralSliceComplementUpper
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.subtypeVal_image_centralSliceComplementUpper target :: scope.openDecls } }

private theorem centralSliceComplementLower_isConnected {a : ℝ} (ha : 0 < a) :
    IsConnected (centralSliceComplementLower ha) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ht⟩ := (lowerAxis_connected (axialZero ha)).nonempty
    obtain ⟨p, hp⟩ := isConnected_sphereTwo.nonempty
    exact ⟨⟨⟨p, t⟩, by
      intro hzero
      exact (ne_of_lt ht) hzero.2⟩, ht⟩
  · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [subtypeVal_image_centralSliceComplementLower ha]
    exact (isConnected_sphereTwo.prod
      (lowerAxis_connected (axialZero ha))).isPreconnected

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementLower_isConnected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementLower_isConnected target :: scope.openDecls } }

private theorem centralSliceComplementUpper_isConnected {a : ℝ} (ha : 0 < a) :
    IsConnected (centralSliceComplementUpper ha) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ht⟩ := (upperAxis_connected (axialZero ha)).nonempty
    obtain ⟨p, hp⟩ := isConnected_sphereTwo.nonempty
    exact ⟨⟨⟨p, t⟩, by
      intro hzero
      exact (ne_of_gt ht) hzero.2⟩, ht⟩
  · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [subtypeVal_image_centralSliceComplementUpper ha]
    exact (isConnected_sphereTwo.prod
      (upperAxis_connected (axialZero ha))).isPreconnected

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementUpper_isConnected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementUpper_isConnected target :: scope.openDecls } }

noncomputable def centralSliceComplementComponentsEquivFinTwo
    {a : ℝ} (ha : 0 < a) :
    ConnectedComponents
        ((zeroSliceDomain ha)ᶜ : Set (SphereTwo × AxialInterval a)) ≃ Fin 2 := by
  let U : Fin 2 →
      Set ((zeroSliceDomain ha)ᶜ : Set (SphereTwo × AxialInterval a)) :=
    Fin.cases (centralSliceComplementLower ha)
      (fun _ ↦ centralSliceComplementUpper ha)
  apply ConnectedComponents.equivOfIsClopenOfIsConnected (U := U)
  · intro i
    rcases bicollar_finTwo_eq_zero_or_one i with rfl | rfl
    · exact centralSliceComplementLower_isClopen ha
    · exact centralSliceComplementUpper_isClopen ha
  · intro i j hij
    rcases bicollar_finTwo_eq_zero_or_one i with rfl | rfl <;>
      rcases bicollar_finTwo_eq_zero_or_one j with rfl | rfl
    · exact False.elim (hij rfl)
    · apply Set.disjoint_left.2
      intro x h₁ h₂
      change x.1.2 < axialZero ha at h₁
      change axialZero ha < x.1.2 at h₂
      exact (not_lt_of_ge (le_of_lt h₂)) h₁
    · apply Set.disjoint_left.2
      intro x h₁ h₂
      change axialZero ha < x.1.2 at h₁
      change x.1.2 < axialZero ha at h₂
      exact (not_lt_of_ge (le_of_lt h₁)) h₂
    · exact False.elim (hij rfl)
  · apply Set.eq_univ_of_forall
    intro x
    have hx : x.1.2 ≠ axialZero ha := by
      intro hx
      apply x.2
      exact ⟨Set.mem_univ _, hx⟩
    rcases lt_or_gt_of_ne hx with h | h
    · exact Set.mem_iUnion.2 ⟨0, h⟩
    · exact Set.mem_iUnion.2 ⟨1, h⟩
  · intro i
    rcases bicollar_finTwo_eq_zero_or_one i with rfl | rfl
    · exact centralSliceComplementLower_isConnected ha
    · exact centralSliceComplementUpper_isConnected ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementComponentsEquivFinTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementComponentsEquivFinTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementComponentsEquivFinTwo ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplementComponentsEquivFinTwo

theorem centralSliceComplement_reducedSingularH0_iso_int
    {a : ℝ} (ha : 0 < a) :
    Nonempty
      (reducedSingularH0
          (TopCat.of
            ((zeroSliceDomain ha)ᶜ : Set (SphereTwo × AxialInterval a))) ≅
        ModuleCat.of ℤ ℤ) := by
  let _ : LocallyPathConnectedSpace SphereTwo :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) SphereTwo
  let _ : LocallyPathConnectedSpace (AxialInterval a) :=
    ChartedSpace.locallyPathConnectedSpace ℝ (AxialInterval a)
  let _ : LocallyPathConnectedSpace
      ((zeroSliceDomain ha)ᶜ : Set (SphereTwo × AxialInterval a)) := by
    apply IsOpen.locallyPathConnectedSpace
    exact (isClosed_univ.prod isClosed_singleton).isOpen_compl
  exact reducedSingularH0_iso_int_of_connectedComponents_equiv_fin_two
    (TopCat.of ((zeroSliceDomain ha)ᶜ :
      Set (SphereTwo × AxialInterval a)))
    (centralSliceComplementComponentsEquivFinTwo ha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplement_reducedSingularH0_iso_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.centralSliceComplement_reducedSingularH0_iso_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplement_reducedSingularH0_iso_int ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplement_reducedSingularH0_iso_int


theorem axialInterval_contractibleSpace {a : ℝ} (ha : 0 < a) :
    ContractibleSpace (AxialInterval a) := by
  exact (convex_Ioo (-a) a).contractibleSpace
    ⟨0, neg_lt_zero.mpr ha, ha⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.axialInterval_contractibleSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.axialInterval_contractibleSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.axialInterval_contractibleSpace ``Submission.DifferentialGeometry.Topology.SphereSeparation.axialInterval_contractibleSpace

noncomputable def sphereTwoProductAxialHomotopyEquiv
    {a : ℝ} (ha : 0 < a) :
    ContinuousMap.HomotopyEquiv
      (SphereTwo × AxialInterval a) SphereTwo := by
  let _ : ContractibleSpace (AxialInterval a) :=
    axialInterval_contractibleSpace ha
  exact ((ContinuousMap.HomotopyEquiv.refl SphereTwo).prodCongr
      (Classical.choice (ContractibleSpace.hequiv_unit (AxialInterval a)))).trans
    (Homeomorph.prodUnique SphereTwo Unit).toHomotopyEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoProductAxialHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoProductAxialHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoProductAxialHomotopyEquiv ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoProductAxialHomotopyEquiv

theorem isZero_integerSingularHomology_sphereTwoProductAxial_one
    {a : ℝ} (ha : 0 < a)
    (hSphere : _root_.CategoryTheory.Limits.IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    _root_.CategoryTheory.Limits.IsZero
      (integerSingularHomology
        (TopCat.of (SphereTwo × AxialInterval a)) 1) :=
  IsZero.of_iso hSphere
    ((singularChainHomotopyEquivOfHomotopyEquiv
      (sphereTwoProductAxialHomotopyEquiv ha)).toHomologyIso 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_sphereTwoProductAxial_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_sphereTwoProductAxial_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_sphereTwoProductAxial_one ``Submission.DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_sphereTwoProductAxial_one

theorem isZero_integerSingularHomology_sphereTwo_one_of_cellularComparison
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex) :
    IsZero (integerSingularHomology (TopCat.of SphereTwo) 1) := by
  have hzero0 : _root_.CategoryTheory.Limits.IsZero
      (((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0).obj
        (ModuleCat.of ℤ ℤ)).X 1) :=
    HomologicalComplex.isZero_single_obj_X
      (ComplexShape.down ℕ) 0 (ModuleCat.of ℤ ℤ) 1 (by omega)
  have hzero2 : _root_.CategoryTheory.Limits.IsZero
      (((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 2).obj
        (ModuleCat.of ℤ ℤ)).X 1) :=
    HomologicalComplex.isZero_single_obj_X
      (ComplexShape.down ℕ) 2 (ModuleCat.of ℤ ℤ) 1 (by omega)
  have hX : _root_.CategoryTheory.Limits.IsZero (sphereTwoCellularChainComplex.X 1) := by
    let C₀ := (HomologicalComplex.single (ModuleCat ℤ)
      (ComplexShape.down ℕ) 0).obj (ModuleCat.of ℤ ℤ)
    let C₂ := (HomologicalComplex.single (ModuleCat ℤ)
      (ComplexShape.down ℕ) 2).obj (ModuleCat.of ℤ ℤ)
    let F := HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) 1
    have htarget : _root_.CategoryTheory.Limits.IsZero (F.obj C₀ ⊞ F.obj C₂) :=
      (_root_.CategoryTheory.Limits.biprod_isZero_iff _ _).2 ⟨hzero0, hzero2⟩
    exact IsZero.of_iso htarget (F.mapBiprod C₀ C₂)
  have hexact : sphereTwoCellularChainComplex.ExactAt 1 :=
    HomologicalComplex.ExactAt.of_isZero hX
  have hhom : _root_.CategoryTheory.Limits.IsZero (sphereTwoCellularChainComplex.homology 1) :=
    hexact.isZero_homology
  exact IsZero.of_iso hhom (comparison.toHomologyIso 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_sphereTwo_one_of_cellularComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_sphereTwo_one_of_cellularComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_sphereTwo_one_of_cellularComparison ``Submission.DifferentialGeometry.Topology.SphereSeparation.isZero_integerSingularHomology_sphereTwo_one_of_cellularComparison

theorem centralSliceComplement_relativeH1_iso_int
    {a : ℝ} (ha : 0 < a)
    (hH1 : _root_.CategoryTheory.Limits.IsZero
      (integerSingularHomology
        (TopCat.of (SphereTwo × AxialInterval a)) 1)) :
    Nonempty
      (relativeSingularHomologyOfSubspace
          ((zeroSliceDomain ha)ᶜ : Set (SphereTwo × AxialInterval a)) 1 ≅
        ModuleCat.of ℤ ℤ) := by
  let _ : LocallyPathConnectedSpace SphereTwo :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) SphereTwo
  let _ : LocallyPathConnectedSpace (AxialInterval a) :=
    ChartedSpace.locallyPathConnectedSpace ℝ (AxialInterval a)
  let _ : ConnectedSpace SphereTwo :=
    connectedSpace_iff_univ.mpr isConnected_sphereTwo
  let _ : ConnectedSpace (AxialInterval a) := by
    exact Subtype.connectedSpace (isConnected_Ioo (by linarith))
  let _ : PathConnectedSpace (SphereTwo × AxialInterval a) := by
    exact pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  exact ⟨relativeH1IsoReducedH0
      ((zeroSliceDomain ha)ᶜ : Set (SphereTwo × AxialInterval a)) hH1 ≪≫
    Classical.choice (centralSliceComplement_reducedSingularH0_iso_int ha)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplement_relativeH1_iso_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.centralSliceComplement_relativeH1_iso_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplement_relativeH1_iso_int ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplement_relativeH1_iso_int

theorem centralSliceComplement_relativeH1_iso_int_of_sphere
    {a : ℝ} (ha : 0 < a)
    (hSphere : _root_.CategoryTheory.Limits.IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    Nonempty
      (relativeSingularHomologyOfSubspace
          ((zeroSliceDomain ha)ᶜ : Set (SphereTwo × AxialInterval a)) 1 ≅
        ModuleCat.of ℤ ℤ) :=
  centralSliceComplement_relativeH1_iso_int ha
    (isZero_integerSingularHomology_sphereTwoProductAxial_one ha hSphere)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplement_relativeH1_iso_int_of_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.centralSliceComplement_relativeH1_iso_int_of_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.centralSliceComplement_relativeH1_iso_int_of_sphere ``Submission.DifferentialGeometry.Topology.SphereSeparation.centralSliceComplement_relativeH1_iso_int_of_sphere

end DifferentialGeometry.Topology.SphereSeparation
