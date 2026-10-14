import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainMaps
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CarrierRestriction
import Mathlib.Algebra.Homology.ShortComplex.Exact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace DifferentialGeometry.Topology

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def integralRelativeCochains (A : Set X) : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  _root_.CategoryTheory.Limits.kernel (integralSingularCochainMap (singularSubspaceInclusion A))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCochains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCochains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCochains ``Submission.DifferentialGeometry.Topology.integralRelativeCochains

def integralRelativeCochainInclusion (A : Set X) :
    integralRelativeCochains A ⟶ integralSingularCochains X :=
  kernel.ι (integralSingularCochainMap (singularSubspaceInclusion A))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCochainInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCochainInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCochainInclusion ``Submission.DifferentialGeometry.Topology.integralRelativeCochainInclusion

theorem integralRelativeCochainInclusion_comp (A : Set X) :
    integralRelativeCochainInclusion A ≫
      integralSingularCochainMap (singularSubspaceInclusion A) = 0 :=
  kernel.condition _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCochainInclusion_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCochainInclusion_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCochainInclusion_comp ``Submission.DifferentialGeometry.Topology.integralRelativeCochainInclusion_comp

theorem integralSingularCochainMap_pair_square (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralSingularCochainMap (singularSubspaceInclusion B) ≫
        integralSingularCochainMap (singularPairRestriction f hf) =
      integralSingularCochainMap f ≫ integralSingularCochainMap (singularSubspaceInclusion A) := by
  rw [← integralSingularCochainMap_comp, ← integralSingularCochainMap_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCochainMap_pair_square then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCochainMap_pair_square"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCochainMap_pair_square ``Submission.DifferentialGeometry.Topology.integralSingularCochainMap_pair_square

def integralRelativeCochainMap (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeCochains B ⟶ integralRelativeCochains A :=
  kernel.map _ _ (integralSingularCochainMap f)
    (integralSingularCochainMap (singularPairRestriction f hf))
    (integralSingularCochainMap_pair_square f hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCochainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCochainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCochainMap ``Submission.DifferentialGeometry.Topology.integralRelativeCochainMap

theorem integralRelativeCochainMap_inclusion (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeCochainMap f hf ≫ integralRelativeCochainInclusion A =
      integralRelativeCochainInclusion B ≫ integralSingularCochainMap f :=
  kernel.lift_ι _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCochainMap_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCochainMap_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCochainMap_inclusion ``Submission.DifferentialGeometry.Topology.integralRelativeCochainMap_inclusion

theorem integralRelativeCochainMap_id (A : Set X) :
    integralRelativeCochainMap (ContinuousMap.id X) (show Set.MapsTo (ContinuousMap.id X) A A
      from fun _ h => h) = 𝟙 _ := by
  apply (_root_.CategoryTheory.cancel_mono (kernel.ι
    (integralSingularCochainMap (singularSubspaceInclusion A)))).mp
  change integralRelativeCochainMap (ContinuousMap.id X) (show Set.MapsTo (ContinuousMap.id X) A A
    from fun _ h => h) ≫
    integralRelativeCochainInclusion A = 𝟙 _ ≫ integralRelativeCochainInclusion A
  rw [integralRelativeCochainMap_inclusion, integralSingularCochainMap_id]
  simp only [Category.comp_id, Category.id_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCochainMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCochainMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCochainMap_id ``Submission.DifferentialGeometry.Topology.integralRelativeCochainMap_id

theorem integralRelativeCochainMap_comp (f : ContinuousMap X Y) (g : ContinuousMap Y Z)
    {A : Set X} {B : Set Y} {C : Set Z} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    integralRelativeCochainMap (g.comp f) (hg.comp hf) =
      integralRelativeCochainMap g hg ≫ integralRelativeCochainMap f hf := by
  apply (_root_.CategoryTheory.cancel_mono (kernel.ι
    (integralSingularCochainMap (singularSubspaceInclusion A)))).mp
  change integralRelativeCochainMap (g.comp f) (hg.comp hf) ≫
    integralRelativeCochainInclusion A =
      (integralRelativeCochainMap g hg ≫ integralRelativeCochainMap f hf) ≫
        integralRelativeCochainInclusion A
  rw [integralRelativeCochainMap_inclusion, Category.assoc,
    integralRelativeCochainMap_inclusion, ← Category.assoc,
    integralRelativeCochainMap_inclusion, Category.assoc, integralSingularCochainMap_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCochainMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCochainMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCochainMap_comp ``Submission.DifferentialGeometry.Topology.integralRelativeCochainMap_comp

def integralRelativeCohomology (n : ℕ) (A : Set X) : ModuleCat.{u} ℤ :=
  (integralRelativeCochains A).homology n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomology ``Submission.DifferentialGeometry.Topology.integralRelativeCohomology

def integralRelativeCohomologyMap (n : ℕ) (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeCohomology n B →ₗ[ℤ] integralRelativeCohomology n A :=
  (HomologicalComplex.homologyMap (integralRelativeCochainMap f hf) n).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyMap ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyMap

theorem integralRelativeCohomologyMap_id (n : ℕ) (A : Set X) :
    integralRelativeCohomologyMap n (ContinuousMap.id X)
      (show Set.MapsTo (ContinuousMap.id X) A A from fun _ h => h) = LinearMap.id := by
  unfold integralRelativeCohomologyMap
  rw [integralRelativeCochainMap_id, HomologicalComplex.homologyMap_id]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyMap_id ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyMap_id

theorem integralRelativeCohomologyMap_comp (n : ℕ)
    (f : ContinuousMap X Y) (g : ContinuousMap Y Z)
    {A : Set X} {B : Set Y} {C : Set Z} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    integralRelativeCohomologyMap n (g.comp f) (hg.comp hf) =
      (integralRelativeCohomologyMap n f hf).comp (integralRelativeCohomologyMap n g hg) := by
  unfold integralRelativeCohomologyMap
  rw [integralRelativeCochainMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyMap_comp ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyMap_comp

def integralRelativeToAbsoluteCohomology (n : ℕ) (A : Set X) :
    integralRelativeCohomology n A →ₗ[ℤ] integralSingularCohomology n X :=
  (HomologicalComplex.homologyMap (integralRelativeCochainInclusion A) n).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomology ``Submission.DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomology

theorem integralRelativeToAbsoluteCohomology_natural (n : ℕ) (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    (integralRelativeToAbsoluteCohomology n A).comp (integralRelativeCohomologyMap n f hf) =
      (integralSingularCohomologyMap n f).comp (integralRelativeToAbsoluteCohomology n B) := by
  have h := congrArg (fun k => HomologicalComplex.homologyMap k n)
    (integralRelativeCochainMap_inclusion f hf)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact congrArg ModuleCat.Hom.hom h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomology_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomology_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomology_natural ``Submission.DifferentialGeometry.Topology.integralRelativeToAbsoluteCohomology_natural

theorem integralRelativeCochainMap_apply (n : ℕ) (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B)
    (φ : (integralRelativeCochains B).X n) (c : (integralSingularChains X).X n) :
    DFunLike.coe (F := integralSingularCochain n X)
      ((integralRelativeCochainInclusion A).f n ((integralRelativeCochainMap f hf).f n φ)) c =
      DFunLike.coe (F := integralSingularCochain n Y) ((integralRelativeCochainInclusion B).f n φ)
        ((integralSingularChainMap f).f n c) := by
  have h := congrArg (fun k => k.f n) (integralRelativeCochainMap_inclusion f hf)
  exact congrArg (fun k => DFunLike.coe (F := integralSingularCochain n X) (k φ) c) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCochainMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCochainMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCochainMap_apply ``Submission.DifferentialGeometry.Topology.integralRelativeCochainMap_apply

section

open _root_.Set _root_.Module

private def integralSingularSubspaceChainRetraction
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X) :
    (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains A).X n := by
  classical
  exact (integralSingularChainBasis n X).constr ℕ (fun σ =>
    if hσ : _root_.Set.range (integralSingularSimplexEquiv n X σ) ⊆ A then
      integralSimplexChain n (integralSingularSimplexRestriction n A σ hσ) else 0)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularSubspaceChainRetraction
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularSubspaceChainRetraction target :: scope.openDecls } }

private theorem integralSingularSubspaceChainRetraction_simplex
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X)
    (σ : integralSingularSimplex n X)
    (hσ : _root_.Set.range (integralSingularSimplexEquiv n X σ) ⊆ A) :
    integralSingularSubspaceChainRetraction n A (integralSimplexChain n σ) =
      integralSimplexChain n (integralSingularSimplexRestriction n A σ hσ) := by
  classical
  rw [← integralSingularChainBasis_apply, integralSingularSubspaceChainRetraction,
    Basis.constr_basis, dif_pos hσ]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularSubspaceChainRetraction_simplex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularSubspaceChainRetraction_simplex target :: scope.openDecls } }

private theorem integralSingularSubspaceChainRetraction_inclusion
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X) :
    (integralSingularSubspaceChainRetraction n A).comp
        ((integralSingularChainMap (singularSubspaceInclusion A)).f n).hom =
      LinearMap.id := by
  apply (integralSingularChainBasis n A).ext
  intro σ
  have hσ : _root_.Set.range (integralSingularSimplexEquiv n X
      (integralSingularSimplexMap n (singularSubspaceInclusion A) σ)) ⊆ A := by
    rintro _ ⟨t, rfl⟩
    rw [integralSingularSimplexMap_apply]
    exact (integralSingularSimplexEquiv n A σ t).property
  simp only [LinearMap.comp_apply, LinearMap.id_apply, integralSingularChainBasis_apply,
    integralSimplexChain_map]
  rw [integralSingularSubspaceChainRetraction_simplex n A _ hσ]
  apply integralSingularChainInclusion_injective n A
  rw [integralSimplexChain_map, integralSingularSimplexRestriction_inclusion,
    integralSimplexChain_map]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularSubspaceChainRetraction_inclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularSubspaceChainRetraction_inclusion target :: scope.openDecls } }

theorem integralSingularCochainPullback_subspace_surjective
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X) :
    Function.Surjective (integralSingularCochainPullback n (singularSubspaceInclusion A)) := by
  intro φ
  refine ⟨φ.comp (integralSingularSubspaceChainRetraction n A), ?_⟩
  apply LinearMap.ext
  intro c
  change φ (integralSingularSubspaceChainRetraction n A
    ((integralSingularChainMap (singularSubspaceInclusion A)).f n c)) = φ c
  exact congrArg φ (LinearMap.congr_fun
    (integralSingularSubspaceChainRetraction_inclusion n A) c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCochainPullback_subspace_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCochainPullback_subspace_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCochainPullback_subspace_surjective ``Submission.DifferentialGeometry.Topology.integralSingularCochainPullback_subspace_surjective

end

def integralRelativeCochainSequence (A : Set X) :
    ShortComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (integralRelativeCochainInclusion A)
    (integralSingularCochainMap (singularSubspaceInclusion A))
    (integralRelativeCochainInclusion_comp A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCochainSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCochainSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCochainSequence ``Submission.DifferentialGeometry.Topology.integralRelativeCochainSequence

theorem integralRelativeCochainSequence_shortExact (A : Set X) :
    (integralRelativeCochainSequence A).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let S := integralRelativeCochainSequence A
  let F := HomologicalComplex.eval (ModuleCat.{u} ℤ) (.up ℕ) n
  have hker : _root_.CategoryTheory.Limits.IsLimit (KernelFork.ofι S.f S.zero) := _root_.CategoryTheory.Limits.kernelIsKernel _
  refine
    { exact := (S.map F).exact_of_f_is_kernel (KernelFork.mapIsLimit _ hker F)
      mono_f := ?_
      epi_g := ?_ }
  · change _root_.CategoryTheory.Mono (F.map (kernel.ι
      (integralSingularCochainMap (singularSubspaceInclusion A))))
    infer_instance
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact integralSingularCochainPullback_subspace_surjective n A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCochainSequence_shortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCochainSequence_shortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCochainSequence_shortExact ``Submission.DifferentialGeometry.Topology.integralRelativeCochainSequence_shortExact

theorem integralRelativeCochainInclusion_range (n : ℕ) (A : Set X) :
    LinearMap.range ((integralRelativeCochainInclusion A).f n).hom =
      LinearMap.ker (integralSingularCochainPullback n (singularSubspaceInclusion A)) := by
  have h := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (integralRelativeCochainSequence_shortExact A) n
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h.exact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCochainInclusion_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCochainInclusion_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCochainInclusion_range ``Submission.DifferentialGeometry.Topology.integralRelativeCochainInclusion_range

def integralRelativeCochainSequenceMap (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeCochainSequence B ⟶ integralRelativeCochainSequence A where
  τ₁ := integralRelativeCochainMap f hf
  τ₂ := integralSingularCochainMap f
  τ₃ := integralSingularCochainMap (singularPairRestriction f hf)
  comm₁₂ := integralRelativeCochainMap_inclusion f hf
  comm₂₃ := (integralSingularCochainMap_pair_square f hf).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCochainSequenceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCochainSequenceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCochainSequenceMap ``Submission.DifferentialGeometry.Topology.integralRelativeCochainSequenceMap

def integralRelativeCohomologyConnecting (n : ℕ) (A : Set X) :
    integralSingularCohomology n A →ₗ[ℤ] integralRelativeCohomology (n + 1) A :=
  ((integralRelativeCochainSequence_shortExact A).δ n (n + 1) (by simp)).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyConnecting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyConnecting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyConnecting ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyConnecting

theorem integralRelativeCohomologyConnecting_natural (n : ℕ) (f : ContinuousMap X Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    (integralRelativeCohomologyMap (n + 1) f hf).comp (integralRelativeCohomologyConnecting n B) =
      (integralRelativeCohomologyConnecting n A).comp
        (integralSingularCohomologyMap n (singularPairRestriction f hf)) := by
  exact congrArg ModuleCat.Hom.hom
    (HomologicalComplex.HomologySequence.δ_naturality (integralRelativeCochainSequenceMap f hf)
      (integralRelativeCochainSequence_shortExact B) (integralRelativeCochainSequence_shortExact A)
        n (n + 1) (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyConnecting_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyConnecting_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyConnecting_natural ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyConnecting_natural

theorem integralRelativeCohomology_exact_absolute (n : ℕ) (A : Set X) :
    Function.Exact (integralRelativeToAbsoluteCohomology n A)
      (integralSingularCohomologyMap n (singularSubspaceInclusion A)) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeCochainSequence_shortExact A).homology_exact₂ n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomology_exact_absolute then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomology_exact_absolute"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomology_exact_absolute ``Submission.DifferentialGeometry.Topology.integralRelativeCohomology_exact_absolute

theorem integralRelativeCohomology_exact_subspace (n : ℕ) (A : Set X) :
    Function.Exact (integralSingularCohomologyMap n (singularSubspaceInclusion A))
      (integralRelativeCohomologyConnecting n A) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeCochainSequence_shortExact A).homology_exact₃ n (n + 1) (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomology_exact_subspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomology_exact_subspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomology_exact_subspace ``Submission.DifferentialGeometry.Topology.integralRelativeCohomology_exact_subspace

theorem integralRelativeCohomology_exact_relative (n : ℕ) (A : Set X) :
    Function.Exact (integralRelativeCohomologyConnecting n A)
      (integralRelativeToAbsoluteCohomology (n + 1) A) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeCochainSequence_shortExact A).homology_exact₁ n (n + 1) (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomology_exact_relative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomology_exact_relative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomology_exact_relative ``Submission.DifferentialGeometry.Topology.integralRelativeCohomology_exact_relative

end DifferentialGeometry.Topology

end
