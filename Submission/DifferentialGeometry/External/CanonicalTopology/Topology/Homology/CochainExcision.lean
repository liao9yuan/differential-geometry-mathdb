import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallHomology
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainHomotopy
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Homology.Opposite
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCochains
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallRelative
import Mathlib.CategoryTheory.Limits.Yoneda
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OpenExcision
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeFunctoriality
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalHomology
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeComparison
import Mathlib.Topology.Sets.Compacts

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Module _root_.Set

universe u v

namespace DifferentialGeometry.Topology

private theorem integralSingularSmallChains_projective
    {X : Type u} [TopologicalSpace X] {ι : Type v} (n : ℕ) (U : ι → Set X) :
    Projective (ModuleCat.of ℤ (integralSingularSmallChains n U)) := by
  classical
  let s : Set (integralSingularSimplex n X) :=
    {σ | ∃ i, Set.range (integralSingularSimplexEquiv n X σ) ⊆ U i}
  let S := Submodule.span ℤ (Set.range (fun σ : s => integralSingularChainBasis n X σ.val))
  let : Module ℤ S := S.module
  let b : _root_.Module.Basis s ℤ S := Basis.span ((integralSingularChainBasis n X).linearIndependent.comp
    (fun σ : s => σ.val) Subtype.val_injective)
  have hS : S = integralSingularSmallChains n U := by
    rw [integralSingularSmallChains_eq_span_basis, Set.image_eq_range]
  exact ModuleCat.projective_of_free (b.map (LinearEquiv.ofEq S _ hS))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularSmallChains_projective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularSmallChains_projective target :: scope.openDecls } }

private theorem exists_integralSingularSmallHomotopyEquiv
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ e : HomotopyEquiv (integralSingularSmallComplex U) (integralSingularChains X),
      e.hom = integralSingularSmallInclusion U := by
  let (n : ℕ) : _root_.CategoryTheory.Projective ((integralSingularSmallComplex U).X n) :=
    integralSingularSmallChains_projective n U
  exact (ChainComplex.quasiIso_iff_of_projective (integralSingularSmallInclusion U)).mp
    (integralSingularSmallInclusion_quasiIso U hU hcover)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.exists_integralSingularSmallHomotopyEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.exists_integralSingularSmallHomotopyEquiv target :: scope.openDecls } }

private abbrev integralChainDual (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) :
    CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  (((_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
    (.up ℕ)).obj K.op

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralChainDual
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralChainDual target :: scope.openDecls } }

private def integralChainDualMap {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L) :
    integralChainDual L ⟶ integralChainDual K :=
  (((_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
    (.up ℕ)).map ((HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)).map f.op)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralChainDualMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralChainDualMap target :: scope.openDecls } }

private def integralChainDualHomotopyEquiv
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (e : HomotopyEquiv K L) :
    HomotopyEquiv (integralChainDual L) (integralChainDual K) where
  hom := integralChainDualMap e.hom
  inv := integralChainDualMap e.inv
  homotopyHomInvId := by
    let F := (_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients
    let G := HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)
    change Homotopy
      ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map (G.map e.hom.op) ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map (G.map e.inv.op)) (𝟙 _)
    rw [← (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map_comp,
      ← (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map_id]
    apply F.mapHomotopy
    rw [← G.map_comp, ← G.map_id]
    simpa only [_root_.CategoryTheory.op_comp, _root_.CategoryTheory.op_id] using e.homotopyInvHomId.op
  homotopyInvHomId := by
    let F := (_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients
    let G := HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)
    change Homotopy
      ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map (G.map e.inv.op) ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map (G.map e.hom.op)) (𝟙 _)
    rw [← (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map_comp,
      ← (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map_id]
    apply F.mapHomotopy
    rw [← G.map_comp, ← G.map_id]
    simpa only [_root_.CategoryTheory.op_comp, _root_.CategoryTheory.op_id] using e.homotopyHomInvId.op

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralChainDualHomotopyEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralChainDualHomotopyEquiv target :: scope.openDecls } }

private def integralDualShortSequence
    (S : _root_.CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} ℤ) (ComplexShape.down ℕ).symm) :=
  (S.op.map (HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ))).map
    (((_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
      (ComplexShape.down ℕ).symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralDualShortSequence
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralDualShortSequence target :: scope.openDecls } }

private theorem integralDualShortSequence_shortExact_of_surjective
    (S : _root_.CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)) (hS : S.ShortExact)
    (hsurj : ∀ n, Function.Surjective ((integralDualShortSequence S).g.f n)) :
    (integralDualShortSequence S).ShortExact := by
  let F := (_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients
  have : _root_.CategoryTheory.Limits.PreservesLimits (F ⋙ _root_.CategoryTheory.forget (ModuleCat.{u} ℤ)) :=
    inferInstanceAs (_root_.CategoryTheory.Limits.PreservesLimits (yoneda.obj integralSingularCoefficients))
  have : _root_.CategoryTheory.Limits.PreservesLimits F := _root_.CategoryTheory.Limits.preservesLimits_of_reflects_of_preserves F (_root_.CategoryTheory.forget _)
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let T := (S.map (HomologicalComplex.eval (ModuleCat.{u} ℤ) (.down ℕ) n)).op
  have hT : T.ShortExact :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n).op
  have := hT.mono_f
  change (T.map F).ShortExact
  exact
    { exact := hT.exact.map_of_mono_of_preservesKernel F hT.mono_f inferInstance
      mono_f := inferInstanceAs (_root_.CategoryTheory.Mono (F.map T.f))
      epi_g := (ModuleCat.epi_iff_surjective _).mpr (hsurj n) }

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralDualShortSequence_shortExact_of_surjective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralDualShortSequence_shortExact_of_surjective target :: scope.openDecls } }

private theorem integralRelativeDualSequence_shortExact
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    (integralDualShortSequence (integralRelativeChainSequence A)).ShortExact := by
  apply integralDualShortSequence_shortExact_of_surjective _
    (integralRelativeChainSequence_shortExact A)
  intro n φ
  obtain ⟨ψ, hψ⟩ := integralSingularCochainPullback_subspace_surjective n A φ.hom
  refine ⟨ModuleCat.ofHom ψ, ?_⟩
  exact ModuleCat.hom_ext hψ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralRelativeDualSequence_shortExact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralRelativeDualSequence_shortExact target :: scope.openDecls } }

private theorem integralSmallRelativeDualSequence_shortExact
    {X : Type u} [TopologicalSpace X] {ι : Type v} (U : ι → Set X) (i : ι) :
    (integralDualShortSequence (integralSmallRelativeSequence U i)).ShortExact := by
  apply integralDualShortSequence_shortExact_of_surjective _
    (integralSmallRelativeSequence_shortExact U i)
  intro n φ
  obtain ⟨ψ, hψ⟩ := integralSingularCochainPullback_subspace_surjective n (U i) φ.hom
  refine ⟨ModuleCat.ofHom (ψ.comp (integralSingularSmallChains n U).subtype), ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact LinearMap.congr_fun hψ c

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSmallRelativeDualSequence_shortExact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSmallRelativeDualSequence_shortExact target :: scope.openDecls } }

private theorem quasiIso_first_of_shortExact
    {c : ComplexShape ℕ} {S T : _root_.CategoryTheory.ShortComplex (HomologicalComplex (ModuleCat.{u} ℤ) c)}
    (φ : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact)
    (h₂ : QuasiIso φ.τ₂) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₁ := by
  let F := HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) c
  have h := HomologicalComplex.HomologySequence.quasiIso_τ₃
    (F.mapShortComplex.map (ShortComplex.opMap φ))
    (hT.op.map_of_exact F) (hS.op.map_of_exact F)
    (inferInstanceAs (QuasiIso (F.map φ.τ₃.op)))
    (inferInstanceAs (QuasiIso (F.map φ.τ₂.op)))
  exact (HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₁).mp h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.quasiIso_first_of_shortExact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.quasiIso_first_of_shortExact target :: scope.openDecls } }

private def integralSmallRelativeDualSequenceComparison
    {X : Type u} [TopologicalSpace X] {ι : Type v} (U : ι → Set X) (i : ι) :
    integralDualShortSequence (integralRelativeChainSequence (U i)) ⟶
      integralDualShortSequence (integralSmallRelativeSequence U i) :=
  ((((_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).mapShortComplex).map
    ((HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)).mapShortComplex.map
      (ShortComplex.opMap (integralSmallRelativeSequenceComparison U i)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSmallRelativeDualSequenceComparison
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSmallRelativeDualSequenceComparison target :: scope.openDecls } }

private theorem integralSmallRelativeDualComparison_quasiIso
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (i : ι) (hU : ∀ j, IsOpen (U j))
    (hcover : ∀ x, ∃ j, x ∈ U j) :
    QuasiIso (integralChainDualMap (integralSmallRelativeComparison U i)) := by
  change QuasiIso (integralSmallRelativeDualSequenceComparison U i).τ₁
  apply quasiIso_first_of_shortExact (integralSmallRelativeDualSequenceComparison U i)
    (integralRelativeDualSequence_shortExact (U i))
    (integralSmallRelativeDualSequence_shortExact U i)
  · obtain ⟨e, he⟩ := exists_integralSingularSmallHomotopyEquiv U hU hcover
    change QuasiIso (integralChainDualMap (integralSingularSmallInclusion U))
    rw [← he]
    exact inferInstanceAs (QuasiIso (integralChainDualHomotopyEquiv e).hom)
  · exact inferInstanceAs (QuasiIso
      (integralChainDualHomotopyEquiv (HomotopyEquiv.refl (integralSingularChains (U i)))).hom)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSmallRelativeDualComparison_quasiIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSmallRelativeDualComparison_quasiIso target :: scope.openDecls } }

private theorem integralChainDualMap_comp
    {K L M : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L) (g : L ⟶ M) :
    integralChainDualMap (f ≫ g) = integralChainDualMap g ≫ integralChainDualMap f := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralChainDualMap_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralChainDualMap_comp target :: scope.openDecls } }

private theorem integralRelativeDualMap_openExcision
    {X : Type u} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = _root_.Set.univ) :
    QuasiIso (integralChainDualMap
      (integralRelativeChainMap (singularSubspaceInclusion B)
        (subspaceIntersection_mapsTo A B))) := by
  have hU : ∀ i, IsOpen (twoSetCover A B i) := by
    intro i
    cases i with
    | false => exact hA
    | true => exact hB
  have hc : ∀ x, ∃ i, x ∈ twoSetCover A B i := by
    intro x
    have hx : x ∈ A ∪ B := hcover.symm ▸ _root_.Set.mem_univ x
    rcases hx with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  have := integralSmallRelativeDualComparison_quasiIso (twoSetCover A B) _root_.Bool.false hU hc
  have : _root_.CategoryTheory.IsIso (integralChainDualMap (integralExcisionSmallMap A B)) := by
    change _root_.CategoryTheory.IsIso
      ((((_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
        (ComplexShape.down ℕ).symm).map
          ((HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)).map
            (integralExcisionSmallMap A B).op))
    infer_instance
  rw [← integralExcisionSmallMap_comparison, integralChainDualMap_comp]
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralRelativeDualMap_openExcision
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralRelativeDualMap_openExcision target :: scope.openDecls } }

private def integralRelativeCochainsDualIso {X : Type u} [TopologicalSpace X] (A : Set X) :
    integralChainDual (integralRelativeChains A) ≅ integralRelativeCochains A := by
  have hS := integralRelativeDualSequence_shortExact A
  exact KernelFork.mapIsoOfIsLimit
    (kf' := KernelFork.ofι (integralRelativeCochainSequence A).f
      (integralRelativeCochainSequence A).zero)
    hS.fIsKernel (integralRelativeCochainSequence_shortExact A).fIsKernel
    (Arrow.isoMk (integralSingularCochainsDualIso X) (integralSingularCochainsDualIso A)
      (integralSingularCochainsDualIso_natural (singularSubspaceInclusion A)).symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralRelativeCochainsDualIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralRelativeCochainsDualIso target :: scope.openDecls } }

private theorem integralRelativeCochainsDualIso_hom_inclusion
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    (integralRelativeCochainsDualIso A).hom ≫ integralRelativeCochainInclusion A =
      integralChainDualMap (integralRelativeChainSequence A).g ≫
        (integralSingularCochainsDualIso X).hom := by
  let S := integralDualShortSequence (integralRelativeChainSequence A)
  let T := integralRelativeCochainSequence A
  let φ : Arrow.mk S.g ≅ Arrow.mk T.g :=
    Arrow.isoMk (integralSingularCochainsDualIso X) (integralSingularCochainsDualIso A)
      (integralSingularCochainsDualIso_natural (singularSubspaceInclusion A)).symm
  change (KernelFork.ofι S.f S.zero).mapOfIsLimit
      (integralRelativeCochainSequence_shortExact A).fIsKernel φ.hom ≫
      (KernelFork.ofι T.f T.zero).ι = _
  erw [KernelFork.mapOfIsLimit_ι]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralRelativeCochainsDualIso_hom_inclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralRelativeCochainsDualIso_hom_inclusion target :: scope.openDecls } }

private theorem integralRelativeCochainsDualIso_natural
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : ContinuousMap X Y) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralChainDualMap (integralRelativeChainMap f hf) ≫
        (integralRelativeCochainsDualIso A).hom =
      (integralRelativeCochainsDualIso B).hom ≫ integralRelativeCochainMap f hf := by
  have : _root_.CategoryTheory.Mono (integralRelativeCochainInclusion A) :=
    (integralRelativeCochainSequence_shortExact A).mono_f
  have hπ : (integralRelativeChainSequence A).g ≫ integralRelativeChainMap f hf =
      integralSingularChainMap f ≫ (integralRelativeChainSequence B).g :=
    integralRelativeChainMap_π f hf
  apply (_root_.CategoryTheory.cancel_mono (integralRelativeCochainInclusion A)).mp
  rw [Category.assoc, integralRelativeCochainsDualIso_hom_inclusion]
  rw [Category.assoc, integralRelativeCochainMap_inclusion]
  rw [← Category.assoc (integralRelativeCochainsDualIso B).hom
    (integralRelativeCochainInclusion B) (integralSingularCochainMap f),
    integralRelativeCochainsDualIso_hom_inclusion]
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  exact congrArg (fun k : integralSingularChains X ⟶ integralRelativeChains B =>
    φ.hom (k.f n c)) hπ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralRelativeCochainsDualIso_natural
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralRelativeCochainsDualIso_natural target :: scope.openDecls } }


theorem integralRelativeCochainMap_openExcision
    {X : Type u} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    QuasiIso (integralRelativeCochainMap (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B)) := by
  have := integralRelativeDualMap_openExcision A B hA hB hcover
  have heq : integralRelativeCochainMap (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B) =
      (integralRelativeCochainsDualIso A).inv ≫
        integralChainDualMap (integralRelativeChainMap (singularSubspaceInclusion B)
          (subspaceIntersection_mapsTo A B)) ≫
        (integralRelativeCochainsDualIso (subspaceIntersection A B)).hom := by
    apply (_root_.CategoryTheory.cancel_epi (integralRelativeCochainsDualIso A).hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (integralRelativeCochainsDualIso_natural (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B)).symm
  rw [heq]
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCochainMap_openExcision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCochainMap_openExcision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCochainMap_openExcision ``Submission.DifferentialGeometry.Topology.integralRelativeCochainMap_openExcision

theorem integralRelativeCohomologyMap_openExcision
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    Function.Bijective (integralRelativeCohomologyMap n (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B)) := by
  have := integralRelativeCochainMap_openExcision A B hA hB hcover
  exact (ConcreteCategory.isIso_iff_bijective _).mp (inferInstanceAs (_root_.CategoryTheory.IsIso
    (HomologicalComplex.homologyMap (integralRelativeCochainMap (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B)) n)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyMap_openExcision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyMap_openExcision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyMap_openExcision ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyMap_openExcision

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Module _root_.Set

universe u v

namespace DifferentialGeometry.Topology

theorem integralRelativeCohomologyMap_point_neighborhood_bijective
    {X : Type u} [TopologicalSpace X] [T1Space X] (n : ℕ) (x : X)
    (U : Set X) (hU : IsOpen U) (hx : x ∈ U) :
    Function.Bijective (integralRelativeCohomologyMap n (singularSubspaceInclusion U)
      (neighborhoodPointComplement_mapsTo x U hx)) := by
  have hcover : ({x}ᶜ : Set X) ∪ U = univ := by
    apply _root_.Set.eq_univ_of_forall
    intro y
    by_cases hy : y = x
    · exact Or.inr (hy.symm ▸ hx)
    · exact Or.inl hy
  have h := integralRelativeCohomologyMap_openExcision n ({x}ᶜ : Set X) U
    isClosed_singleton.isOpen_compl hU hcover
  have H : ∀ hf : _root_.Set.MapsTo (singularSubspaceInclusion U)
      (subspaceIntersection ({x}ᶜ : Set X) U) ({x}ᶜ : Set X),
      Function.Bijective (integralRelativeCohomologyMap n (singularSubspaceInclusion U) hf) :=
    fun _ => h
  rw [subspaceIntersection_point_complement x U hx] at H
  exact H _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyMap_point_neighborhood_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyMap_point_neighborhood_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyMap_point_neighborhood_bijective ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyMap_point_neighborhood_bijective

theorem integralRelativeCohomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : Set X) (hK : IsClosed (f '' K)) :
    Function.Bijective (integralRelativeCohomologyMap n f
      (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective) :
        MapsTo f Kᶜ (f '' K)ᶜ)) := by
  let A : Set Y := (f '' K)ᶜ
  let B : Set Y := _root_.Set.range f
  let e : X ≃ₜ B := hf.isEmbedding.toHomeomorph
  let g : ContinuousMap X B := ⟨e, e.continuous⟩
  have hg : _root_.Set.MapsTo g Kᶜ (subspaceIntersection A B) := by
    intro x hx
    exact _root_.Set.image_compl_subset hf.injective ⟨x, hx, rfl⟩
  let es : ↥(Kᶜ) ≃ₜ subspaceIntersection A B := e.subtype (fun x => by
    constructor
    · exact fun hx => hg hx
    · intro hx hxK
      exact hx ⟨x, hxK, rfl⟩)
  have hgbij : Function.Bijective (integralRelativeCohomologyMap n g hg) := by
    apply integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
    · intro k
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv e.toHomotopyEquiv k
    · intro k
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv es.toHomotopyEquiv k
  have hcover : A ∪ B = univ := by
    apply _root_.Set.eq_univ_of_forall
    intro y
    by_cases hy : y ∈ f '' K
    · obtain ⟨x, hx, rfl⟩ := hy
      exact Or.inr ⟨x, rfl⟩
    · exact Or.inl hy
  have hibij := integralRelativeCohomologyMap_openExcision n A B
    hK.isOpen_compl hf.isOpen_range hcover
  have heq := integralRelativeCohomologyMap_comp n g (singularSubspaceInclusion B)
    hg (subspaceIntersection_mapsTo A B)
  change integralRelativeCohomologyMap n f _ = _ at heq
  rw [heq]
  exact hgbij.comp hibij

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image

theorem integralRelativeCohomologyMap_bijective_of_isOpenEmbedding
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : TopologicalSpace.Compacts X) :
    Function.Bijective (integralRelativeCohomologyMap n f
      (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective) :
        MapsTo f (K : Set X)ᶜ (f '' (K : Set X))ᶜ)) :=
  integralRelativeCohomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image n f hf
    (K : Set X) (K.isCompact.image f.continuous).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyMap_bijective_of_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyMap_bijective_of_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyMap_bijective_of_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyMap_bijective_of_isOpenEmbedding

end DifferentialGeometry.Topology

end
