import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCapProduct
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CapHomology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private local instance capIntegerComm (M : Type*) [AddCommGroup M] [h : Module ℤ M] :
    @SMulCommClass ℤ ℤ M h.toSMul h.toSMul :=
  @smulCommClass_self ℤ M inferInstance h.toMulAction

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.capIntegerComm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.capIntegerComm target :: scope.openDecls } }

private local instance capIntegerLinearModule (M N : Type*)
    [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N] :
    Module ℤ (M →ₗ[ℤ] N) := LinearMap.module

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.capIntegerLinearModule
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.capIntegerLinearModule target :: scope.openDecls } }

private local instance integralRelativeCycle_module (A : Set X) (n : ℕ) :
    Module ℤ (LinearMap.ker ((integralRelativeChains A).sc n).g.hom) :=
  (LinearMap.ker ((integralRelativeChains A).sc n).g.hom).module

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralRelativeCycle_module
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralRelativeCycle_module target :: scope.openDecls } }

private local instance capCocycle_module (n : ℕ) :
    Module ℤ (LinearMap.ker ((integralSingularCochains X).sc n).g.hom) :=
  (LinearMap.ker ((integralSingularCochains X).sc n).g.hom).module

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.capCocycle_module
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.capCocycle_module target :: scope.openDecls } }

private theorem cap_cocycle_closed (k : ℕ)
    (φ : LinearMap.ker ((integralSingularCochains X).sc k).g.hom) :
    integralSingularCoboundary X k (k + 1) φ.val = 0 := by
  have h := φ.property
  change integralSingularCoboundary X k ((ComplexShape.up ℕ).next k) φ.val = 0 at h
  rwa [CochainComplex.next] at h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.cap_cocycle_closed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.cap_cocycle_closed target :: scope.openDecls } }

private theorem relative_cap_cycle (A : Set X) (k m : ℕ)
    (φ : LinearMap.ker ((integralSingularCochains X).sc k).g.hom)
    (c : LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom) :
    integralRelativeCapProduct A k m φ.val c.val ∈
      LinearMap.ker ((integralRelativeChains A).sc m).g.hom := by
  change (integralRelativeChains A).d m ((ComplexShape.down ℕ).next m)
    (integralRelativeCapProduct A k m φ.val c.val) = 0
  cases m with
  | zero =>
    rw [ChainComplex.next_nat_zero, (integralRelativeChains A).shape 0 0 (by simp)]
    rfl
  | succ m =>
    rw [ChainComplex.next_nat_succ]
    apply integralRelativeCapProduct_boundary_eq_zero A k m φ.val (cap_cocycle_closed k φ)
    have hc := c.property
    change (integralRelativeChains A).d (k + m + 1)
      ((ComplexShape.down ℕ).next (k + m + 1)) c.val = 0 at hc
    rwa [ChainComplex.next_nat_succ] at hc

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.relative_cap_cycle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.relative_cap_cycle target :: scope.openDecls } }

def integralRelativeCapCycleMap (A : Set X) (k m : ℕ) :
    LinearMap.ker ((integralSingularCochains X).sc k).g.hom →ₗ[ℤ]
      LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom →ₗ[ℤ]
        LinearMap.ker ((integralRelativeChains A).sc m).g.hom := by
  let badd : ((integralSingularCochains X).sc k).X₂ →+
      (((integralRelativeChains A).sc (k + m)).X₂ →ₗ[ℤ]
        ((integralRelativeChains A).sc m).X₂) :=
    { toFun := fun φ => integralRelativeCapProduct A k m φ
      map_zero' := (integralRelativeCapProduct A k m).toAddMonoidHom.map_zero
      map_add' := (integralRelativeCapProduct A k m).toAddMonoidHom.map_add }
  let β : ((integralSingularCochains X).sc k).X₂ →ₗ[ℤ]
      ((integralRelativeChains A).sc (k + m)).X₂ →ₗ[ℤ]
        ((integralRelativeChains A).sc m).X₂ :=
    { toFun := badd
      map_add' := badd.map_add
      map_smul' := fun z φ => by
        simpa only [Int.cast_id, RingHom.id_apply] using! map_intCast_smul badd ℤ ℤ z φ }
  exact (β.compl₁₂
    (LinearMap.ker ((integralSingularCochains X).sc k).g.hom).subtype
    (LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom).subtype).codRestrict₂
      (LinearMap.ker ((integralRelativeChains A).sc m).g.hom).subtype
      Subtype.val_injective (fun φ c => ⟨⟨_, relative_cap_cycle A k m φ c⟩, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCapCycleMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCapCycleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCapCycleMap ``Submission.DifferentialGeometry.Topology.integralRelativeCapCycleMap

theorem integralRelativeCapCycleMap_apply (A : Set X) (k m : ℕ)
    (φ : LinearMap.ker ((integralSingularCochains X).sc k).g.hom)
    (c : LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom) :
    (integralRelativeCapCycleMap A k m φ c).val = integralRelativeCapProduct A k m φ.val c.val := by
  unfold integralRelativeCapCycleMap
  exact LinearMap.codRestrict₂_apply (R := ℤ) _
    (LinearMap.ker ((integralRelativeChains A).sc m).g.hom).subtype _ _ φ c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCapCycleMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCapCycleMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCapCycleMap_apply ``Submission.DifferentialGeometry.Topology.integralRelativeCapCycleMap_apply

private def relativeCapCycleClasses (A : Set X) (k m : ℕ) :
    LinearMap.ker ((integralSingularCochains X).sc k).g.hom →ₗ[ℤ]
      LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom →ₗ[ℤ]
        integralRelativeHomology m A :=
  (integralRelativeCapCycleMap A k m).compr₂ₛₗ (moduleHomologyClass ((integralRelativeChains A).sc m))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.relativeCapCycleClasses
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.relativeCapCycleClasses target :: scope.openDecls } }

private theorem chain_homology_class_eq_zero_iff
    (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ)
    (c : LinearMap.ker (K.sc n).g.hom) :
    moduleHomologyClass (K.sc n) c = 0 ↔ ∃ b : K.X (n + 1), K.d (n + 1) n b = c.val := by
  have h := moduleHomologyClass_eq_zero_iff (K.sc n) c
  change (_ ↔ ∃ b : K.X ((ComplexShape.down ℕ).prev n),
    K.d ((ComplexShape.down ℕ).prev n) n b = c.val) at h
  exact h.trans (congrArg (fun i => ∃ b : K.X i, K.d i n b = c.val)
    (ChainComplex.prev ℕ n)).to_iff

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.chain_homology_class_eq_zero_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.chain_homology_class_eq_zero_iff target :: scope.openDecls } }

private theorem relative_cap_boundary_is_boundary (A : Set X) (k m : ℕ)
    (φ : integralSingularCochain k X) (hφ : integralSingularCoboundary X k (k + 1) φ = 0)
    (c : (integralRelativeChains A).X (k + m + 1)) :
    ∃ b : (integralRelativeChains A).X (m + 1),
      (integralRelativeChains A).d (m + 1) m b =
        integralRelativeCapProduct A k m φ
          ((integralRelativeChains A).d (k + m + 1) (k + m) c) := by
  refine ⟨(-1 : ℤ) ^ k • integralRelativeCapProduct A k (m + 1) φ c, ?_⟩
  rw [map_zsmul, integralRelativeCapProduct_boundary, hφ, map_zero,
    LinearMap.zero_apply, zero_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.relative_cap_boundary_is_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.relative_cap_boundary_is_boundary target :: scope.openDecls } }

private theorem relative_cap_coboundary_is_boundary (A : Set X) (k m : ℕ)
    (φ : integralSingularCochain k X) (c : (integralRelativeChains A).X (k + m + 1))
    (hc : (integralRelativeChains A).d (k + m + 1) (k + m) c = 0) :
    ∃ b : (integralRelativeChains A).X (m + 1),
      (integralRelativeChains A).d (m + 1) m b =
        integralRelativeCapProduct A (k + 1) m (integralSingularCoboundary X k (k + 1) φ)
          (((integralRelativeChains A).XIsoOfEq
            (show k + m + 1 = (k + 1) + m by omega)).hom c) := by
  have h := integralRelativeCapProduct_boundary A k m φ c
  rw [hc, map_zero] at h
  refine ⟨-((-1 : ℤ) ^ k • integralRelativeCapProduct A k (m + 1) φ c), ?_⟩
  rw [map_neg, map_zsmul]
  exact (eq_neg_iff_add_eq_zero.mpr h.symm).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.relative_cap_coboundary_is_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.relative_cap_coboundary_is_boundary target :: scope.openDecls } }

private theorem relativeCapCycleClasses_boundary_right (A : Set X) (k m : ℕ)
    (b : ((integralRelativeChains A).sc (k + m)).X₁) :
    (relativeCapCycleClasses A k m).flip
      (((integralRelativeChains A).sc (k + m)).moduleCatToCycles b) = 0 := by
  apply LinearMap.ext
  intro φ
  change moduleHomologyClass ((integralRelativeChains A).sc m)
    (integralRelativeCapCycleMap A k m φ (((integralRelativeChains A).sc (k + m)).moduleCatToCycles b)) = 0
  apply (chain_homology_class_eq_zero_iff (integralRelativeChains A) m _).2
  rw [integralRelativeCapCycleMap_apply]
  let b' := ((integralRelativeChains A).xPrevIso
    (i := k + m + 1) (j := k + m) rfl).hom b
  have hb : (integralRelativeChains A).d (k + m + 1) (k + m) b' =
      (((integralRelativeChains A).sc (k + m)).moduleCatToCycles b).val := by
    change _ = (integralRelativeChains A).dTo (k + m) b
    rw [(integralRelativeChains A).dTo_eq (i := k + m + 1) rfl]
    rfl
  obtain ⟨a, ha⟩ := relative_cap_boundary_is_boundary A k m φ.val
    (cap_cocycle_closed k φ) b'
  exact ⟨a, ha.trans (congrArg (integralRelativeCapProduct A k m φ.val) hb)⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.relativeCapCycleClasses_boundary_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.relativeCapCycleClasses_boundary_right target :: scope.openDecls } }

private theorem relativeCapCycleClasses_boundary_left (A : Set X) (k m : ℕ)
    (ψ : ((integralSingularCochains X).sc k).X₁) :
    relativeCapCycleClasses A k m
      (((integralSingularCochains X).sc k).moduleCatToCycles ψ) = 0 := by
  cases k with
  | zero =>
    have hzero : ((integralSingularCochains X).sc 0).moduleCatToCycles ψ = 0 := by
      apply Subtype.ext
      change (integralSingularCochains X).dTo 0 ψ = 0
      rw [(integralSingularCochains X).dTo_eq_zero (by
        rw [CochainComplex.prev_nat_zero]
        simp)]
      rfl
    rw [hzero, map_zero]
  | succ k =>
    apply LinearMap.ext
    intro c
    change moduleHomologyClass ((integralRelativeChains A).sc m)
      (integralRelativeCapCycleMap A (k + 1) m
        (((integralSingularCochains X).sc (k + 1)).moduleCatToCycles ψ) c) = 0
    apply (chain_homology_class_eq_zero_iff (integralRelativeChains A) m _).2
    rw [integralRelativeCapCycleMap_apply]
    let ψ' := ((integralSingularCochains X).xPrevIso (i := k) (j := k + 1) rfl).hom ψ
    have hψ : integralSingularCoboundary X k (k + 1) ψ' =
        (((integralSingularCochains X).sc (k + 1)).moduleCatToCycles ψ).val := by
      change (integralSingularCochains X).d k (k + 1) ψ' =
        (integralSingularCochains X).dTo (k + 1) ψ
      rw [(integralSingularCochains X).dTo_eq (i := k) rfl]
      rfl
    let h : k + m + 1 = (k + 1) + m := by omega
    let ι := (integralRelativeChains A).XIsoOfEq h
    let c' := ι.inv c.val
    have hn : (ComplexShape.down ℕ).next ((k + 1) + m) = k + m := by
      rw [← h, ChainComplex.next_nat_succ]
    have hc := c.property
    change (integralRelativeChains A).d ((k + 1) + m)
      ((ComplexShape.down ℕ).next ((k + 1) + m)) c.val = 0 at hc
    rw [hn] at hc
    have hc' : (integralRelativeChains A).d (k + m + 1) (k + m) c' = 0 := by
      have heq := congrArg (fun f : (integralRelativeChains A).X ((k + 1) + m) ⟶
        (integralRelativeChains A).X (k + m) => f c.val)
        ((integralRelativeChains A).XIsoOfEq_inv_comp_d h (k + m))
      exact heq.trans hc
    have hback : ι.hom c' = c.val := by
      change (ι.inv ≫ ι.hom) c.val = c.val
      rw [Iso.inv_hom_id]
      rfl
    obtain ⟨b, hb⟩ := relative_cap_coboundary_is_boundary A k m ψ' c' hc'
    refine ⟨b, hb.trans ?_⟩
    change integralRelativeCapProduct A (k + 1) m
      (integralSingularCoboundary X k (k + 1) ψ') (ι.hom c') = _
    rw [hback, hψ]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.relativeCapCycleClasses_boundary_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.relativeCapCycleClasses_boundary_left target :: scope.openDecls } }

private local instance relativeCapQuotientModule (M : Type*) [AddCommGroup M]
    [Module ℤ M] (S : Submodule ℤ M) : Module ℤ (M ⧸ S) :=
  Submodule.Quotient.module S

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.relativeCapQuotientModule
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.relativeCapQuotientModule target :: scope.openDecls } }

private def relativeCapQuotientPairing (A : Set X) (k m : ℕ) :
    (LinearMap.ker ((integralSingularCochains X).sc k).g.hom ⧸
      LinearMap.range ((integralSingularCochains X).sc k).moduleCatToCycles) →ₗ[ℤ]
        (LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom ⧸
          LinearMap.range ((integralRelativeChains A).sc (k + m)).moduleCatToCycles) →ₗ[ℤ]
            integralRelativeHomology m A := by
  let S := (integralSingularCochains X).sc k
  let T := (integralRelativeChains A).sc (k + m)
  let β := relativeCapCycleClasses A k m
  have hS : LinearMap.range S.moduleCatToCycles ≤ β.ker := by
    rintro φ ⟨ψ, rfl⟩
    exact relativeCapCycleClasses_boundary_left A k m ψ
  have hT : LinearMap.range T.moduleCatToCycles ≤ β.flip.ker := by
    rintro c ⟨b, rfl⟩
    exact relativeCapCycleClasses_boundary_right A k m b
  exact β.liftQ₂ (LinearMap.range S.moduleCatToCycles)
    (LinearMap.range T.moduleCatToCycles) hS hT

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.relativeCapQuotientPairing
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.relativeCapQuotientPairing target :: scope.openDecls } }

def integralRelativeCohomologyCapProduct (A : Set X) (k m : ℕ) :
    integralSingularCohomology k X →ₗ[ℤ]
      integralRelativeHomology (k + m) A →ₗ[ℤ] integralRelativeHomology m A :=
  ((relativeCapQuotientPairing A k m).compl₂
    ((integralRelativeChains A).sc (k + m)).moduleCatHomologyIso.hom.hom).comp
      ((integralSingularCochains X).sc k).moduleCatHomologyIso.hom.hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct

theorem integralRelativeCohomologyCapProduct_class (A : Set X) (k m : ℕ)
    (φ : LinearMap.ker ((integralSingularCochains X).sc k).g.hom)
    (c : LinearMap.ker ((integralRelativeChains A).sc (k + m)).g.hom) :
    integralRelativeCohomologyCapProduct A k m
        (moduleHomologyClass ((integralSingularCochains X).sc k) φ)
        (moduleHomologyClass ((integralRelativeChains A).sc (k + m)) c) =
      moduleHomologyClass ((integralRelativeChains A).sc m) (integralRelativeCapCycleMap A k m φ c) :=
  congrArg₂ (fun a b => relativeCapQuotientPairing A k m a b)
    (moduleHomologyClass_quotient ((integralSingularCochains X).sc k) φ)
    (moduleHomologyClass_quotient ((integralRelativeChains A).sc (k + m)) c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_class then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_class"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_class ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_class

variable {Y : Type u} [TopologicalSpace Y]

theorem integralRelativeCohomologyCapProduct_natural (k m : ℕ)
    (f : ContinuousMap X Y) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B)
    (φ : integralSingularCohomology k Y) (c : integralRelativeHomology (k + m) A) :
    integralRelativeHomologyMap m f hf
        (integralRelativeCohomologyCapProduct A k m (integralSingularCohomologyMap k f φ) c) =
      integralRelativeCohomologyCapProduct B k m φ
        (integralRelativeHomologyMap (k + m) f hf c) := by
  obtain ⟨φ, rfl⟩ := moduleHomologyClass_surjective ((integralSingularCochains Y).sc k) φ
  obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective ((integralRelativeChains A).sc (k + m)) c
  let P := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) k).map
    (integralSingularCochainMap f)
  let Q := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ)
    (k + m)).map (integralRelativeChainMap f hf)
  let R := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) m).map
    (integralRelativeChainMap f hf)
  have hφ : integralSingularCohomologyMap k f
      (moduleHomologyClass ((integralSingularCochains Y).sc k) φ) =
      moduleHomologyClass ((integralSingularCochains X).sc k) (moduleCycleMap P φ) :=
    moduleHomologyClass_map P φ
  have hc : integralRelativeHomologyMap (k + m) f hf
      (moduleHomologyClass ((integralRelativeChains A).sc (k + m)) c) =
      moduleHomologyClass ((integralRelativeChains B).sc (k + m)) (moduleCycleMap Q c) :=
    moduleHomologyClass_map Q c
  rw [hφ, hc]
  erw [integralRelativeCohomologyCapProduct_class, integralRelativeCohomologyCapProduct_class]
  have hout := moduleHomologyClass_map R (integralRelativeCapCycleMap A k m (moduleCycleMap P φ) c)
  change integralRelativeHomologyMap m f hf _ = _ at hout
  erw [hout]
  congr 1
  apply Subtype.ext
  change (integralRelativeChainMap f hf).f m (integralRelativeCapCycleMap A k m (moduleCycleMap P φ) c).val = _
  rw [integralRelativeCapCycleMap_apply, integralRelativeCapCycleMap_apply]
  change (integralRelativeChainMap f hf).f m
    (integralRelativeCapProduct A k m (integralSingularCochainPullback k f φ.val) c.val) =
      integralRelativeCapProduct B k m φ.val ((integralRelativeChainMap f hf).f (k + m) c.val)
  exact congrArg (fun L : (integralRelativeChains A).X (k + m) →ₗ[ℤ]
    (integralRelativeChains B).X m => L c.val) (integralRelativeCapProduct_natural k m f hf φ.val)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_natural ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_natural

private theorem relativeHomologyClass_transport (A : Set X) {i j : ℕ} (h : i = j)
    (c : LinearMap.ker ((integralRelativeChains A).sc i).g.hom) :
    (_root_.CategoryTheory.eqToHom (congrArg (fun n => integralRelativeHomology n A) h))
        (moduleHomologyClass ((integralRelativeChains A).sc i) c) =
      moduleHomologyClass ((integralRelativeChains A).sc j)
        ⟨((integralRelativeChains A).XIsoOfEq h).hom c.val, by subst j; exact c.property⟩ := by
  subst j
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.relativeHomologyClass_transport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.relativeHomologyClass_transport target :: scope.openDecls } }

theorem integralRelativeCohomologyCapProduct_unit (A : Set X) (m : ℕ)
    (c : integralRelativeHomology (0 + m) A) :
    integralRelativeCohomologyCapProduct A 0 m (integralSingularCohomologyUnit X) c =
      (_root_.CategoryTheory.eqToHom (congrArg (fun n => integralRelativeHomology n A) (Nat.zero_add m))) c := by
  obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective ((integralRelativeChains A).sc (0 + m)) c
  unfold integralSingularCohomologyUnit
  rw [integralRelativeCohomologyCapProduct_class, relativeHomologyClass_transport A (Nat.zero_add m)]
  congr 1
  apply Subtype.ext
  rw [integralRelativeCapCycleMap_apply]
  change integralRelativeCapProduct A 0 m
    ((ULift.moduleEquiv : integralSingularCoefficients ≃ₗ[ℤ] ℤ).symm.toLinearMap.comp
      integralSingularAugmentation) c.val = _
  rw [integralRelativeCapProduct_augmentation]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_unit ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_unit

theorem integralRelativeCohomologyCapProduct_absoluteToRelative (A : Set X) (k m : ℕ)
    (φ : integralSingularCohomology k X) (c : integralSingularHomology (k + m) X) :
    integralRelativeCohomologyCapProduct A k m φ (integralAbsoluteToRelative (k + m) A c) =
      integralAbsoluteToRelative m A (integralSingularCohomologyCapProduct k m φ c) := by
  obtain ⟨φ, rfl⟩ := moduleHomologyClass_surjective ((integralSingularCochains X).sc k) φ
  obtain ⟨c, rfl⟩ := moduleHomologyClass_surjective ((integralSingularChains X).sc (k + m)) c
  let Q := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ)
    (k + m)).map (integralRelativeChainSequence A).g
  let R := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) m).map
    (integralRelativeChainSequence A).g
  have hc : integralAbsoluteToRelative (k + m) A
      (moduleHomologyClass ((integralSingularChains X).sc (k + m)) c) =
      moduleHomologyClass ((integralRelativeChains A).sc (k + m)) (moduleCycleMap Q c) :=
    moduleHomologyClass_map Q c
  rw [hc]
  erw [integralRelativeCohomologyCapProduct_class, integralSingularCohomologyCapProduct_class]
  have hout := moduleHomologyClass_map R
    (integralSingularCapCycleMap k m φ.val (cap_cocycle_closed k φ) c)
  change integralAbsoluteToRelative m A _ = _ at hout
  erw [hout]
  congr 1
  apply Subtype.ext
  erw [integralRelativeCapCycleMap_apply]
  change integralRelativeCapProduct A k m φ.val ((integralRelativeChainSequence A).g.f (k + m) c.val) =
    (integralRelativeChainSequence A).g.f m _
  exact integralRelativeCapProduct_π A k m φ.val c.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_absoluteToRelative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_absoluteToRelative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_absoluteToRelative ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyCapProduct_absoluteToRelative

end DifferentialGeometry.Topology

end
