import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Instances.Quotient
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

open _root_.IsLocalDiffeomorph in
theorem IsLocalDiffeomorph.contMDiff_of_comp_of_surjective
    {k : Type*} [NontriviallyNormedField k]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace k F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace k G]
    {H : Type*} [TopologicalSpace H]
    {H' : Type*} [TopologicalSpace H']
    {H'' : Type*} [TopologicalSpace H'']
    {I : ModelWithCorners k E H}
    {J : ModelWithCorners k F H'}
    {K : ModelWithCorners k G H''}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    {n : WithTop ℕ∞} {f : M → N}
    (hf : IsLocalDiffeomorph I J n f)
    (hsurj : Function.Surjective f) {g : N → P}
    (hcomp : ContMDiff I K n (g ∘ f)) : ContMDiff J K n g := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  have hlocal := hf x
  have hsmooth : ContMDiffAt J K n
      ((g ∘ f) ∘ hlocal.localInverse) (f x) :=
    hcomp.contMDiffAt.comp (f x) hlocal.localInverse_contMDiffAt
  apply hsmooth.congr_of_eventuallyEq
  simpa only [Function.comp_id, Function.comp_assoc] using
    (hlocal.localInverse_eventuallyEq_right.fun_comp g).symm

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsLocalDiffeomorph
  let env ← Lean.getEnv
  if env.contains `IsLocalDiffeomorph.contMDiff_of_comp_of_surjective then
    throwError "Refusing to shadow existing declaration IsLocalDiffeomorph.contMDiff_of_comp_of_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalDiffeomorph.contMDiff_of_comp_of_surjective ``Submission.IsLocalDiffeomorph.contMDiff_of_comp_of_surjective

open _root_.IsLocalDiffeomorph in
theorem IsLocalDiffeomorph.contMDiff_of_continuous_of_comp
    {k : Type*} [NontriviallyNormedField k]
    {D : Type*} [NormedAddCommGroup D] [NormedSpace k D]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace k F]
    {G : Type*} [TopologicalSpace G]
    {H : Type*} [TopologicalSpace H]
    {H' : Type*} [TopologicalSpace H']
    {L : ModelWithCorners k D G}
    {I : ModelWithCorners k E H}
    {J : ModelWithCorners k F H'}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace G Q]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {m n : WithTop ℕ∞} {f : M → N} {h : Q → M}
    (hf : IsLocalDiffeomorph I J n f)
    (hh : Continuous h)
    (hcomp : ContMDiff L J m (f ∘ h))
    (hmn : m ≤ n) : ContMDiff L I m h := by
  intro x
  have hlocal := hf (h x)
  have hsmooth : ContMDiffAt L I m
      (hlocal.localInverse ∘ (f ∘ h)) x :=
    (hlocal.localInverse_contMDiffAt.of_le hmn).comp x hcomp.contMDiffAt
  apply hsmooth.congr_of_eventuallyEq
  have hevent : ∀ᶠ y in 𝓝 x, h y ∈ hlocal.localInverse.target :=
    hh.continuousAt
      (hlocal.localInverse.open_target.mem_nhds
        hlocal.localInverse_mem_target)
  filter_upwards [hevent] with y hy
  change h y = hlocal.localInverse (f (h y))
  exact (hlocal.localInverse_left_inv hy).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsLocalDiffeomorph.contMDiff_of_continuous_of_comp then
    throwError "Refusing to shadow existing declaration IsLocalDiffeomorph.contMDiff_of_continuous_of_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalDiffeomorph.contMDiff_of_continuous_of_comp ``Submission.IsLocalDiffeomorph.contMDiff_of_continuous_of_comp

class ContMDiffConstSMul {k : Type*} [NontriviallyNormedField k]
    {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
    (I : ModelWithCorners k E H) (n : WithTop ℕ∞)
    (G : Type*) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [SMul G M] : Prop where
  contMDiff_const_smul : ∀ g : G, ContMDiff I I n fun x : M => g • x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffConstSMul then
    throwError "Refusing to shadow existing declaration ContMDiffConstSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffConstSMul ``Submission.ContMDiffConstSMul

private lemma symm_trans_trans_mem_maximalAtlas_of_contMDiffOn
    {k : Type*} [NontriviallyNormedField k]
    {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
    {I : ModelWithCorners k E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞}
    [hM : IsManifold I n M]
    {phi phi' : OpenPartialHomeomorph M H}
    (hphi : phi ∈ IsManifold.maximalAtlas I n M)
    (hphi' : phi' ∈ IsManifold.maximalAtlas I n M)
    {f : OpenPartialHomeomorph M M}
    (hf : ContMDiffOn I I n f f.source)
    (hf' : ContMDiffOn I I n f.symm f.target) :
    phi.symm.trans (f.trans phi') ∈ IsManifold.maximalAtlas I n H := by
  let _ := hM
  refine (phi.symm.trans (f.trans phi')).mem_maximalAtlas_of_contMDiffOn ?_ ?_
  · exact (contMDiffOn_of_mem_maximalAtlas hphi').comp
      (hf.comp ((contMDiffOn_symm_of_mem_maximalAtlas hphi).mono fun z hz => hz.1)
        fun z hz => hz.2.1)
      fun z hz => hz.2.2
  · exact (contMDiffOn_of_mem_maximalAtlas hphi).comp
      (hf'.comp ((contMDiffOn_symm_of_mem_maximalAtlas hphi').mono fun z hz => hz.1.1)
        fun z hz => hz.1.2)
      fun z hz => hz.2

run_cmd do
  let target := ``Submission.symm_trans_trans_mem_maximalAtlas_of_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `symm_trans_trans_mem_maximalAtlas_of_contMDiffOn target :: scope.openDecls } }

private lemma symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
    {k : Type*} [NontriviallyNormedField k]
    {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
    {I : ModelWithCorners k E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞}
    [IsManifold I n M]
    {phi phi' : OpenPartialHomeomorph M H}
    (hphi : phi ∈ IsManifold.maximalAtlas I n M)
    (hphi' : phi' ∈ IsManifold.maximalAtlas I n M)
    {f : OpenPartialHomeomorph M M}
    (hf : ContMDiffOn I I n f f.source)
    (hf' : ContMDiffOn I I n f.symm f.target) :
    phi.symm.trans (f.trans phi') ∈ contDiffGroupoid n I := by
  simpa [OpenPartialHomeomorph.refl_trans, OpenPartialHomeomorph.refl_symm] using
    IsManifold.compatible_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (chartedSpaceSelf_atlas.mpr rfl))
      (symm_trans_trans_mem_maximalAtlas_of_contMDiffOn hphi hphi' hf hf')

run_cmd do
  let target := ``Submission.symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn target :: scope.openDecls } }

namespace MulAction
open _root_.MulAction

variable {M : Type*} [TopologicalSpace M]
  {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M]
  {H : Type*} [TopologicalSpace H] [ChartedSpace H M]

open _root_.MulAction in
private abbrev QuotientType := orbitRel.Quotient G M

run_cmd do
  let target := ``Submission.MulAction.QuotientType
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.QuotientType target :: scope.openDecls } }

open _root_.MulAction in
private theorem quotientMap_isLocalHomeomorph :
    IsLocalHomeomorph (Quotient.mk (_root_.MulAction.orbitRel G M)) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap.isLocalHomeomorph

run_cmd do
  let target := ``Submission.MulAction.quotientMap_isLocalHomeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.quotientMap_isLocalHomeomorph target :: scope.openDecls } }

open _root_.MulAction in
private noncomputable abbrev quotientRepresentative
    (x : QuotientType (G := G) (M := M)) : M :=
  (Quotient.mk_surjective (s := _root_.MulAction.orbitRel G M)).hasRightInverse.choose x

run_cmd do
  let target := ``Submission.MulAction.quotientRepresentative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.quotientRepresentative target :: scope.openDecls } }

namespace orbitRel.Quotient
open _root_.MulAction _root_.MulAction.orbitRel _root_.MulAction.orbitRel.Quotient

variable {x : QuotientType (G := G) (M := M)}

open _root_.MulAction _root_.MulAction.orbitRel _root_.MulAction.orbitRel.Quotient in
private noncomputable abbrev localInverseAt
    (x : QuotientType (G := G) (M := M)) :
    OpenPartialHomeomorph (QuotientType (G := G) (M := M)) M :=
  quotientMap_isLocalHomeomorph.localInverseAt (quotientRepresentative x)

run_cmd do
  let target := ``Submission.MulAction.orbitRel.Quotient.localInverseAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.orbitRel.Quotient.localInverseAt target :: scope.openDecls } }

open _root_.MulAction _root_.MulAction.orbitRel _root_.MulAction.orbitRel.Quotient in
private lemma localInverseAt_apply_mk {g : G} {m : M}
    (hm : g • m ∈ (localInverseAt x).target) :
    localInverseAt x (Quotient.mk'' m) = g • m := by
  change localInverseAt x (⟦m⟧ : QuotientType (G := G) (M := M)) = g • m
  rw [← orbitRel.Quotient.quotient_smul_eq (g := g),
    ← quotientMap_isLocalHomeomorph.localInverseAt_symm,
    (localInverseAt x).right_inv hm]

run_cmd do
  let target := ``Submission.MulAction.orbitRel.Quotient.localInverseAt_apply_mk
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.orbitRel.Quotient.localInverseAt_apply_mk target :: scope.openDecls } }

open _root_.MulAction _root_.MulAction.orbitRel _root_.MulAction.orbitRel.Quotient in
private lemma localInverseAt_symm_trans_eqOn_smul
    (x y : QuotientType (G := G) (M := M)) (g : G) :
    ((g • ·) ⁻¹' (localInverseAt y).target).EqOn
      ((localInverseAt x).symm.trans (localInverseAt y)) (g • ·) := by
  intro m hm
  simpa only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    quotientMap_isLocalHomeomorph.localInverseAt_symm]
    using localInverseAt_apply_mk hm

run_cmd do
  let target := ``Submission.MulAction.orbitRel.Quotient.localInverseAt_symm_trans_eqOn_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.orbitRel.Quotient.localInverseAt_symm_trans_eqOn_smul target :: scope.openDecls } }

open _root_.MulAction _root_.MulAction.orbitRel _root_.MulAction.orbitRel.Quotient in
private lemma exists_smul_mem_localInverseAt_target {m : M}
    (hm : (Quotient.mk'' m : QuotientType (G := G) (M := M)) ∈
      (localInverseAt x).source) :
    ∃ g : G, g • m ∈ (localInverseAt x).target := by
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp ((MulAction.orbitRel_apply).mp
    (Quotient.exact
      (quotientMap_isLocalHomeomorph.apply_localInverseAt_of_mem hm)))
  exact ⟨g, by simpa [hg] using (localInverseAt x).map_source hm⟩

run_cmd do
  let target := ``Submission.MulAction.orbitRel.Quotient.exists_smul_mem_localInverseAt_target
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.orbitRel.Quotient.exists_smul_mem_localInverseAt_target target :: scope.openDecls } }

variable (x y : QuotientType (G := G) (M := M))

open _root_.MulAction _root_.MulAction.orbitRel _root_.MulAction.orbitRel.Quotient in
private noncomputable def transitionMap : OpenPartialHomeomorph H H :=
  (chartAt H (quotientRepresentative x)).symm.trans
    (((localInverseAt x).symm.trans (localInverseAt y)).trans
      (chartAt H (quotientRepresentative y)))

run_cmd do
  let target := ``Submission.MulAction.orbitRel.Quotient.transitionMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.orbitRel.Quotient.transitionMap target :: scope.openDecls } }

open _root_.MulAction _root_.MulAction.orbitRel _root_.MulAction.orbitRel.Quotient in
private lemma transitionMap_eqOn_smul (g : G) :
    ((chartAt H (quotientRepresentative x)).symm ⁻¹'
      ((g • ·) ⁻¹' (localInverseAt y).target)).EqOn
      (transitionMap x y)
      ((chartAt H (quotientRepresentative x)).symm.trans
        (((Homeomorph.smul g).toOpenPartialHomeomorph).trans
          (chartAt H (quotientRepresentative y)))) := by
  intro h hh
  simp only [transitionMap, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  simpa using congrArg (chartAt H (quotientRepresentative y))
    (localInverseAt_symm_trans_eqOn_smul x y g hh)

run_cmd do
  let target := ``Submission.MulAction.orbitRel.Quotient.transitionMap_eqOn_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.orbitRel.Quotient.transitionMap_eqOn_smul target :: scope.openDecls } }

open _root_.MulAction _root_.MulAction.orbitRel _root_.MulAction.orbitRel.Quotient in
private lemma transitionMap_locally_smul {h : H}
    (hh : h ∈ (transitionMap x y).source) :
    ∃ g : G,
      h ∈ (chartAt H (quotientRepresentative x)).symm ⁻¹'
        ((g • ·) ⁻¹' (localInverseAt y).target) ∧
      ((chartAt H (quotientRepresentative x)).symm ⁻¹'
        ((g • ·) ⁻¹' (localInverseAt y).target)).EqOn
        (transitionMap x y)
        ((chartAt H (quotientRepresentative x)).symm.trans
          (((Homeomorph.smul g).toOpenPartialHomeomorph).trans
            (chartAt H (quotientRepresentative y)))) := by
  simp only [transitionMap, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
    Set.mem_preimage] at hh
  obtain ⟨_, ⟨_, hmid⟩, _⟩ := hh
  obtain ⟨g, hg⟩ := exists_smul_mem_localInverseAt_target
    (by rwa [quotientMap_isLocalHomeomorph.localInverseAt_symm] at hmid)
  exact ⟨g, hg, transitionMap_eqOn_smul x y g⟩

run_cmd do
  let target := ``Submission.MulAction.orbitRel.Quotient.transitionMap_locally_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.orbitRel.Quotient.transitionMap_locally_smul target :: scope.openDecls } }

end orbitRel.Quotient

variable {k : Type*} [NontriviallyNormedField k]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  (I : ModelWithCorners k E H) {n : WithTop ℕ∞} [IsManifold I n M]

open _root_.MulAction.orbitRel.Quotient _root_.Submission.MulAction.orbitRel.Quotient

open _root_.MulAction in
instance isManifold_quotient_of_contMDiffConstSMul
    [ContMDiffConstSMul I n G M] :
    IsManifold I n (orbitRel.Quotient G M) where
  compatible := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    rw [(localInverseAt x).trans_symm_eq_symm_trans_symm,
      (chartAt H (quotientRepresentative x)).symm.trans_assoc,
      ← (localInverseAt x).symm.trans_assoc]
    apply StructureGroupoid.locality
    intro _ hh
    obtain ⟨g0, hg0, hg0'⟩ := transitionMap_locally_smul x y hh
    have hto : IsOpen ((chartAt H (quotientRepresentative x)).symm.source ∩
        (chartAt H (quotientRepresentative x)).symm ⁻¹'
          ((g0 • ·) ⁻¹' (localInverseAt y).target)) :=
      (chartAt H (quotientRepresentative x)).symm.isOpen_inter_preimage
        ((localInverseAt y).open_target.preimage (_root_.ContinuousConstSMul.continuous_const_smul g0))
    refine ⟨_, hto, ⟨hh.1, hg0⟩, ?_⟩
    refine StructureGroupoid.restr_mem_of_eqOn
      (symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
        (IsManifold.chart_mem_maximalAtlas (quotientRepresentative x))
        (IsManifold.chart_mem_maximalAtlas (quotientRepresentative y)) ?_ ?_)
      hto (hg0'.mono Set.inter_subset_right).symm ?_
    · rw [Homeomorph.toOpenPartialHomeomorph_apply]
      exact (ContMDiffConstSMul.contMDiff_const_smul g0).contMDiffOn
    · rw [Homeomorph.toOpenPartialHomeomorph_symm_apply]
      exact (ContMDiffConstSMul.contMDiff_const_smul g0⁻¹).contMDiffOn
    · intro h' ⟨⟨hQ1, _, hQ4⟩, _, hcert⟩
      exact ⟨hQ1, Set.mem_univ _,
        by simpa [← localInverseAt_symm_trans_eqOn_smul x y g0 hcert] using hQ4⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MulAction.isManifold_quotient_of_contMDiffConstSMul then
    throwError "Refusing to shadow existing declaration MulAction.isManifold_quotient_of_contMDiffConstSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `MulAction.isManifold_quotient_of_contMDiffConstSMul ``Submission.MulAction.isManifold_quotient_of_contMDiffConstSMul

open _root_.MulAction in
private noncomputable def quotientChartPartialDiffeomorph
    [ContMDiffConstSMul I n G M]
    (x : QuotientType (G := G) (M := M)) :
    PartialDiffeomorph I I (QuotientType (G := G) (M := M)) M n := by
  let e : OpenPartialHomeomorph (QuotientType (G := G) (M := M)) M :=
    (chartAt H x).trans (chartAt H (quotientRepresentative x)).symm
  exact
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := by
        rw [show e.source = (chartAt H x).source ∩
            (chartAt H x) ⁻¹' (chartAt H (quotientRepresentative x)).target by
          exact OpenPartialHomeomorph.trans_source _ _]
        exact contMDiffOn_chart_symm.comp
          (contMDiffOn_chart.mono Set.inter_subset_left) fun _ hy => hy.2
      contMDiffOn_invFun := by
        rw [show e.target = (chartAt H (quotientRepresentative x)).source ∩
            (chartAt H (quotientRepresentative x)) ⁻¹' (chartAt H x).target by
          exact OpenPartialHomeomorph.trans_target _ _]
        exact contMDiffOn_chart_symm.comp
          (contMDiffOn_chart.mono Set.inter_subset_left) fun _ hy => hy.2 }

run_cmd do
  let target := ``Submission.MulAction.quotientChartPartialDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.quotientChartPartialDiffeomorph target :: scope.openDecls } }

open _root_.MulAction in
private lemma quotientChartPartialDiffeomorph_mem_source
    [ContMDiffConstSMul I n G M]
    (x : QuotientType (G := G) (M := M)) :
    x ∈ (quotientChartPartialDiffeomorph (n := n) I x).source := by
  change x ∈ ((chartAt H x).trans
    (chartAt H (quotientRepresentative x)).symm).source
  rw [OpenPartialHomeomorph.trans_source]
  refine ⟨mem_chart_source H x, ?_⟩
  have hx := (chartAt H x).map_source (mem_chart_source H x)
  change (chartAt H x) x ∈
    ((localInverseAt x).trans (chartAt H (quotientRepresentative x))).target at hx
  rw [OpenPartialHomeomorph.trans_target] at hx
  exact hx.1

run_cmd do
  let target := ``Submission.MulAction.quotientChartPartialDiffeomorph_mem_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.quotientChartPartialDiffeomorph_mem_source target :: scope.openDecls } }

open _root_.MulAction in
private lemma quotientChartPartialDiffeomorph_apply
    [ContMDiffConstSMul I n G M]
    (x : QuotientType (G := G) (M := M))
    {y : QuotientType (G := G) (M := M)}
    (hy : y ∈ (quotientChartPartialDiffeomorph (n := n) I x).source) :
    quotientChartPartialDiffeomorph (n := n) I x y = localInverseAt x y := by
  change ((chartAt H x).trans
    (chartAt H (quotientRepresentative x)).symm) y = localInverseAt x y
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  apply (chartAt H (quotientRepresentative x)).left_inv
  have hy' := hy
  change y ∈ ((chartAt H x).trans
    (chartAt H (quotientRepresentative x)).symm).source at hy'
  rw [OpenPartialHomeomorph.trans_source] at hy'
  have hyx := hy'.1
  change y ∈ ((localInverseAt x).trans
    (chartAt H (quotientRepresentative x))).source at hyx
  rw [OpenPartialHomeomorph.trans_source] at hyx
  exact hyx.2

run_cmd do
  let target := ``Submission.MulAction.quotientChartPartialDiffeomorph_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.quotientChartPartialDiffeomorph_apply target :: scope.openDecls } }

open _root_.MulAction in
private lemma quotientChartPartialDiffeomorph_apply_self
    [ContMDiffConstSMul I n G M]
    (x : QuotientType (G := G) (M := M)) :
    quotientChartPartialDiffeomorph (n := n) I x x = quotientRepresentative x := by
  rw [quotientChartPartialDiffeomorph_apply (n := n) I x
    (quotientChartPartialDiffeomorph_mem_source (n := n) I x)]
  change quotientMap_isLocalHomeomorph.localInverseAt
    (quotientRepresentative x) x = quotientRepresentative x
  have hx : Quotient.mk (_root_.MulAction.orbitRel G M) (quotientRepresentative x) = x :=
    (Quotient.mk_surjective
      (s := _root_.MulAction.orbitRel G M)).hasRightInverse.choose_spec x
  calc
    _ = quotientMap_isLocalHomeomorph.localInverseAt
        (quotientRepresentative x)
        (Quotient.mk (_root_.MulAction.orbitRel G M) (quotientRepresentative x)) :=
      congrArg _ hx.symm
    _ = quotientRepresentative x :=
      IsLocalHomeomorph.localInverseAt_apply_self
        (f := Quotient.mk (_root_.MulAction.orbitRel G M)) quotientMap_isLocalHomeomorph

run_cmd do
  let target := ``Submission.MulAction.quotientChartPartialDiffeomorph_apply_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.quotientChartPartialDiffeomorph_apply_self target :: scope.openDecls } }

open _root_.MulAction in
private lemma quotientChartPartialDiffeomorph_symm_apply
    [ContMDiffConstSMul I n G M]
    (x : QuotientType (G := G) (M := M)) {m : M}
    (hm : m ∈ (quotientChartPartialDiffeomorph (n := n) I x).target) :
    (quotientChartPartialDiffeomorph (n := n) I x).symm m =
      (Quotient.mk'' m : QuotientType (G := G) (M := M)) := by
  change ((chartAt H x).trans
    (chartAt H (quotientRepresentative x)).symm).symm m = Quotient.mk'' m
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  have hm' := hm
  change m ∈ ((chartAt H x).trans
    (chartAt H (quotientRepresentative x)).symm).target at hm'
  rw [OpenPartialHomeomorph.trans_target] at hm'
  change (chartAt H x).symm ((chartAt H (quotientRepresentative x)) m) =
    Quotient.mk'' m
  change (((localInverseAt x).trans
    (chartAt H (quotientRepresentative x))).symm)
      ((chartAt H (quotientRepresentative x)) m) = Quotient.mk'' m
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  rw [(chartAt H (quotientRepresentative x)).left_inv hm'.1]
  rw [quotientMap_isLocalHomeomorph.localInverseAt_symm]

run_cmd do
  let target := ``Submission.MulAction.quotientChartPartialDiffeomorph_symm_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.quotientChartPartialDiffeomorph_symm_apply target :: scope.openDecls } }

open _root_.MulAction in
noncomputable def smulDiffeomorph
    [ContMDiffConstSMul I n G M] (g : G) : M ≃ₘ^n⟮I, I⟯ M where
  toEquiv := MulAction.toPerm g
  contMDiff_toFun := ContMDiffConstSMul.contMDiff_const_smul g
  contMDiff_invFun := ContMDiffConstSMul.contMDiff_const_smul g⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MulAction.smulDiffeomorph then
    throwError "Refusing to shadow existing declaration MulAction.smulDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `MulAction.smulDiffeomorph ``Submission.MulAction.smulDiffeomorph

omit [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M]
  [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]
  [IsManifold I n M] in
open _root_.MulAction in
@[simp] theorem smulDiffeomorph_apply
    [ContMDiffConstSMul I n G M] (g : G) (x : M) :
    smulDiffeomorph (n := n) I g x = g • x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MulAction.smulDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration MulAction.smulDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `MulAction.smulDiffeomorph_apply ``Submission.MulAction.smulDiffeomorph_apply

omit [TopologicalSpace M] [ProperlyDiscontinuousSMul G M]
  [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M]
  [LocallyCompactSpace M] in
open _root_.MulAction in
private lemma exists_smul_eq_quotientRepresentative (m : M) :
    ∃ g : G, g • m =
      quotientRepresentative (Quotient.mk'' m : QuotientType (G := G) (M := M)) := by
  apply MulAction.mem_orbit_iff.mp
  apply MulAction.orbitRel_apply.mp
  apply Quotient.exact
  exact (Quotient.mk_surjective
    (s := _root_.MulAction.orbitRel G M)).hasRightInverse.choose_spec (Quotient.mk'' m)

run_cmd do
  let target := ``Submission.MulAction.exists_smul_eq_quotientRepresentative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MulAction.exists_smul_eq_quotientRepresentative target :: scope.openDecls } }

open _root_.MulAction in
theorem isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    [ContMDiffConstSMul I n G M] :
    IsLocalDiffeomorph I I n (Quotient.mk (_root_.MulAction.orbitRel G M)) := by
  intro m
  let x : QuotientType (G := G) (M := M) := Quotient.mk'' m
  obtain ⟨g, hg⟩ :=
    exists_smul_eq_quotientRepresentative (G := G) (M := M) m
  let phi := quotientChartPartialDiffeomorph (n := n) I x
  let psi := (smulDiffeomorph I g).toPartialDiffeomorph.trans phi.symm
  refine ⟨psi, ?_, ?_⟩
  · have hx : x ∈ phi.source :=
      quotientChartPartialDiffeomorph_mem_source (n := n) I x
    have hrepresentative : quotientRepresentative x ∈ phi.target := by
      have hmap := phi.map_source hx
      rw [quotientChartPartialDiffeomorph_apply_self (n := n) I x] at hmap
      exact hmap
    change m ∈ Set.univ ∩ (fun y : M => g • y) ⁻¹' phi.target
    exact ⟨Set.mem_univ _, by simpa [x] using hg.symm ▸ hrepresentative⟩
  · intro y hy
    have hgy : g • y ∈ phi.target := by
      change y ∈ Set.univ ∩ (fun z : M => g • z) ⁻¹' phi.target at hy
      exact hy.2
    change Quotient.mk (_root_.MulAction.orbitRel G M) y = phi.symm (g • y)
    rw [quotientChartPartialDiffeomorph_symm_apply (n := n) I x hgy]
    exact orbitRel.Quotient.quotient_smul_eq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul then
    throwError "Refusing to shadow existing declaration MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul ``Submission.MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul

open _root_.MulAction _root_.MulAction.orbitRel _root_.MulAction.orbitRel.Quotient in
noncomputable instance orbitRel.Quotient.sigmaCompactSpace
    [SigmaCompactSpace M] :
    SigmaCompactSpace (orbitRel.Quotient G M) :=
  ⟨by
    rw [← isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective.range_eq]
    exact isSigmaCompact_range
      isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MulAction.orbitRel.Quotient.sigmaCompactSpace then
    throwError "Refusing to shadow existing declaration MulAction.orbitRel.Quotient.sigmaCompactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `MulAction.orbitRel.Quotient.sigmaCompactSpace ``Submission.MulAction.orbitRel.Quotient.sigmaCompactSpace

end MulAction
