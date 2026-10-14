import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CapHomology
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathChains
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ZeroAugmentation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology

universe u

namespace DifferentialGeometry.Topology

private theorem integralSingularCocycle_zero_eq_smul_augmentation
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (a : X)
    (φ : integralSingularCochain 0 X) (hφ : integralSingularCoboundary X 0 1 φ = 0) :
    φ = (φ (integralVertexChain a)).down •
      ((ULift.moduleEquiv : integralSingularCoefficients ≃ₗ[ℤ] ℤ).symm.toLinearMap.comp
        integralSingularAugmentation) := by
  apply (integralSingularChainBasis 0 X).ext
  intro σ
  rw [integralSingularChainBasis_apply]
  have h := LinearMap.congr_fun hφ
    (integralPathChain (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)))
  change φ ((integralSingularChains X).d 1 0
    (integralPathChain (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)))) = 0 at h
  rw [integralPathChain_boundary, map_sub, sub_eq_zero] at h
  have hv : φ (integralSimplexChain 0 σ) = φ (integralVertexChain a) := by
    simpa only [integralVertexChain, Equiv.symm_apply_apply] using h
  change φ (integralSimplexChain 0 σ) =
    (φ (integralVertexChain a)).down • ULift.up
      (integralSingularAugmentation (integralSimplexChain 0 σ))
  rw [integralSingularAugmentation_simplex, hv]
  apply ULift.down_injective
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularCocycle_zero_eq_smul_augmentation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularCocycle_zero_eq_smul_augmentation target :: scope.openDecls } }

private theorem integralSingularCohomologyClass_zero_eq_smul_unit
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (a : X)
    (φ : LinearMap.ker ((integralSingularCochains X).sc 0).g.hom) :
    moduleHomologyClass ((integralSingularCochains X).sc 0) φ =
      ((show integralSingularCochain 0 X from φ.val) (integralVertexChain a)).down •
        integralSingularCohomologyUnit X := by
  let ψ : integralSingularCochain 0 X := φ.val
  symm
  unfold integralSingularCohomologyUnit
  dsimp only
  erw [← map_zsmul]
  congr 1
  apply Subtype.ext
  change (ψ (integralVertexChain a)).down •
    ((ULift.moduleEquiv : integralSingularCoefficients ≃ₗ[ℤ] ℤ).symm.toLinearMap.comp
      integralSingularAugmentation) = φ.val
  apply (integralSingularCocycle_zero_eq_smul_augmentation a φ.val ?_).symm
  have h := φ.property
  change integralSingularCoboundary X 0 ((ComplexShape.up ℕ).next 0) φ.val = 0 at h
  rwa [CochainComplex.next] at h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyClass_zero_eq_smul_unit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularCohomologyClass_zero_eq_smul_unit target :: scope.openDecls } }

private theorem integralSingularCohomologyUnit_smul_surjective
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] :
    Function.Surjective (fun z : ℤ => z • integralSingularCohomologyUnit X) := by
  intro α
  obtain ⟨φ, rfl⟩ := moduleHomologyClass_surjective ((integralSingularCochains X).sc 0) α
  let a : X := Classical.choice inferInstance
  let ψ : integralSingularCochain 0 X := φ.val
  exact ⟨(ψ (integralVertexChain a)).down,
    (integralSingularCohomologyClass_zero_eq_smul_unit a φ).symm⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyUnit_smul_surjective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularCohomologyUnit_smul_surjective target :: scope.openDecls } }

private theorem integralSingularCohomologyUnit_smul_injective
    {X : Type u} [TopologicalSpace X] [Nonempty X] :
    Function.Injective (fun z : ℤ => z • integralSingularCohomologyUnit X) := by
  intro z w h
  let a : X := Classical.choice inferInstance
  let c := integralZeroChainClass (integralVertexChain a)
  have heq := congrArg (fun α => integralSingularCohomologyCapProduct 0 0 α c) h
  erw [map_zsmul, map_zsmul] at heq
  change z • integralSingularCohomologyCapProduct 0 0 (integralSingularCohomologyUnit X) c =
    w • integralSingularCohomologyCapProduct 0 0 (integralSingularCohomologyUnit X) c at heq
  rw [integralSingularCohomologyCapProduct_unit] at heq
  have ha := congrArg integralZeroAugmentation heq
  change integralZeroAugmentation (z • c) = integralZeroAugmentation (w • c) at ha
  rw [map_zsmul, map_zsmul] at ha
  change z • integralZeroAugmentation (integralZeroChainClass (integralVertexChain a)) =
    w • integralZeroAugmentation (integralZeroChainClass (integralVertexChain a)) at ha
  simpa only [integralZeroAugmentation_vertex, smul_eq_mul, mul_one] using ha

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyUnit_smul_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularCohomologyUnit_smul_injective target :: scope.openDecls } }

private theorem integralSingularCohomologyUnit_span_apply
    (X : Type u) [TopologicalSpace X] (z : ℤ) :
    LinearMap.toSpanSingleton ℤ (integralSingularCohomology 0 X)
      (integralSingularCohomologyUnit X) z = z • integralSingularCohomologyUnit X := by
  change (ModuleCat.isModule (integralSingularCohomology 0 X)).smul z
    (integralSingularCohomologyUnit X) = _
  exact int_smul_eq_zsmul _ z _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyUnit_span_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularCohomologyUnit_span_apply target :: scope.openDecls } }

def integralSingularCohomologyZeroEquiv
    (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] :
    integralSingularCohomology 0 X ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℤ (integralSingularCohomology 0 X)
      (integralSingularCohomologyUnit X))
    ⟨by
      intro z w h
      rw [integralSingularCohomologyUnit_span_apply,
        integralSingularCohomologyUnit_span_apply] at h
      exact integralSingularCohomologyUnit_smul_injective h, by
      intro α
      obtain ⟨z, hz⟩ := integralSingularCohomologyUnit_smul_surjective α
      exact ⟨z, (integralSingularCohomologyUnit_span_apply X z).trans hz⟩⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv

theorem integralSingularCohomologyZeroEquiv_symm_apply
    (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (z : ℤ) :
    (integralSingularCohomologyZeroEquiv X).symm z = z • integralSingularCohomologyUnit X := by
  change LinearMap.toSpanSingleton ℤ (integralSingularCohomology 0 X)
    (integralSingularCohomologyUnit X) z = _
  exact integralSingularCohomologyUnit_span_apply X z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_symm_apply ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_symm_apply

theorem integralSingularCohomologyZeroEquiv_unit
    (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] :
    integralSingularCohomologyZeroEquiv X (integralSingularCohomologyUnit X) = 1 := by
  apply (integralSingularCohomologyZeroEquiv X).symm.injective
  rw [LinearEquiv.symm_apply_apply, integralSingularCohomologyZeroEquiv_symm_apply, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_unit ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_unit

theorem integralSingularCohomologyZeroEquiv_class
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (a : X)
    (φ : LinearMap.ker ((integralSingularCochains X).sc 0).g.hom) :
    integralSingularCohomologyZeroEquiv X
        (moduleHomologyClass ((integralSingularCochains X).sc 0) φ) =
      ((show integralSingularCochain 0 X from φ.val) (integralVertexChain a)).down := by
  rw [integralSingularCohomologyClass_zero_eq_smul_unit a φ, map_zsmul,
    integralSingularCohomologyZeroEquiv_unit]
  simp only [zsmul_eq_mul, mul_one, Int.cast_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_class then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_class"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_class ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_class

theorem integralSingularCohomologyZeroEquiv_natural
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : ContinuousMap X Y)
    (α : integralSingularCohomology 0 Y) :
    integralSingularCohomologyZeroEquiv X (integralSingularCohomologyMap 0 f α) =
      integralSingularCohomologyZeroEquiv Y α := by
  obtain ⟨z, rfl⟩ := integralSingularCohomologyUnit_smul_surjective α
  rw [map_zsmul, integralSingularCohomologyMap_unit, map_zsmul, map_zsmul,
    integralSingularCohomologyZeroEquiv_unit, integralSingularCohomologyZeroEquiv_unit]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_natural ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyZeroEquiv_natural

theorem integralSingularCohomologyCapProduct_zero
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (m : ℕ)
    (α : integralSingularCohomology 0 X) (c : integralSingularHomology (0 + m) X) :
    integralSingularCohomologyCapProduct 0 m α c =
      integralSingularCohomologyZeroEquiv X α •
        (_root_.CategoryTheory.eqToHom (congrArg (fun n => integralSingularHomology n X) (Nat.zero_add m))) c := by
  obtain ⟨z, rfl⟩ := integralSingularCohomologyUnit_smul_surjective α
  erw [map_zsmul]
  change z • integralSingularCohomologyCapProduct 0 m (integralSingularCohomologyUnit X) c = _
  rw [integralSingularCohomologyCapProduct_unit, map_zsmul,
    integralSingularCohomologyZeroEquiv_unit]
  simp only [zsmul_eq_mul, mul_one, Int.cast_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyCapProduct_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyCapProduct_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyCapProduct_zero ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyCapProduct_zero

theorem integralSingularCohomologyCapProduct_zero_bijective_iff
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (m : ℕ)
    (c : integralSingularHomology (0 + m) X) :
    Function.Bijective (fun α : integralSingularCohomology 0 X =>
      integralSingularCohomologyCapProduct 0 m α c) ↔
      Function.Bijective (fun z : ℤ => z •
        (_root_.CategoryTheory.eqToHom (congrArg (fun n => integralSingularHomology n X) (Nat.zero_add m))) c) := by
  have hu : Function.Bijective (fun z : ℤ => z • integralSingularCohomologyUnit X) :=
    ⟨integralSingularCohomologyUnit_smul_injective, integralSingularCohomologyUnit_smul_surjective⟩
  rw [← Function.Bijective.of_comp_iff
    (fun α : integralSingularCohomology 0 X => integralSingularCohomologyCapProduct 0 m α c) hu]
  have heq : (fun α : integralSingularCohomology 0 X => integralSingularCohomologyCapProduct 0 m α c) ∘
      (fun z : ℤ => z • integralSingularCohomologyUnit X) =
      (fun z : ℤ => z •
        (_root_.CategoryTheory.eqToHom (congrArg (fun n => integralSingularHomology n X) (Nat.zero_add m))) c) := by
    funext z
    dsimp only [Function.comp_apply]
    rw [integralSingularCohomologyCapProduct_zero, map_zsmul,
      integralSingularCohomologyZeroEquiv_unit]
    simp only [zsmul_eq_mul, mul_one, Int.cast_id]
  rw [heq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyCapProduct_zero_bijective_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyCapProduct_zero_bijective_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyCapProduct_zero_bijective_iff ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyCapProduct_zero_bijective_iff

theorem integralSingularCohomologyMap_zero_injective_of_pathConnectedSpace
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [Nonempty Y] (f : ContinuousMap Y X) :
    Function.Injective (integralSingularCohomologyMap 0 f) := by
  let g : ContinuousMap X Y := ContinuousMap.const X (Classical.choice inferInstance)
  have hcomp : (integralSingularCohomologyMap 0 g).comp
      (integralSingularCohomologyMap 0 f) = LinearMap.id := by
    rw [← integralSingularCohomologyMap_comp]
    ext α
    apply (integralSingularCohomologyZeroEquiv X).injective
    exact integralSingularCohomologyZeroEquiv_natural (f.comp g) α
  intro α β h
  have hh := congrArg (integralSingularCohomologyMap 0 g) h
  change ((integralSingularCohomologyMap 0 g).comp
    (integralSingularCohomologyMap 0 f)) α =
      ((integralSingularCohomologyMap 0 g).comp (integralSingularCohomologyMap 0 f)) β at hh
  simpa only [hcomp, LinearMap.id_apply] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyMap_zero_injective_of_pathConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyMap_zero_injective_of_pathConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyMap_zero_injective_of_pathConnectedSpace ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyMap_zero_injective_of_pathConnectedSpace

end DifferentialGeometry.Topology

end
