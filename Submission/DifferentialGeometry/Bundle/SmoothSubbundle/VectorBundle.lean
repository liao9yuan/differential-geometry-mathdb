import Submission.DifferentialGeometry.Bundle.SmoothSubbundle.LocalFrame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Set
open scoped _root_.Manifold _root_.Topology

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable {n : WithTop ℕ∞} {ι : Type*} {S : ∀ x, Submodule 𝕜 (V x)}
variable {s : ι → (x : M) → V x} {W : Set M}

namespace IsSubbundleFrameOn

def pretrivialization [Finite ι]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W) (hW : IsOpen W) :
    Pretrivialization (ι → 𝕜) (TotalSpace.proj : _root_.Bundle.TotalSpace (ι → 𝕜) (fun x => S x) → M) := by
  classical
  exact
    { toFun := fun z => (z.1, fun i => hs.coeff i z.1 z.2)
      invFun := fun z => ⟨z.1, if hx : z.1 ∈ W then (hs.toBasisAt hx).equivFun.symm z.2 else 0⟩
      source := TotalSpace.proj ⁻¹' W
      target := W ×ˢ _root_.Set.univ
      map_source' := fun _ h => ⟨h, _root_.Set.mem_univ _⟩
      map_target' := fun _ h => h.1
      left_inv' := fun ⟨x, v⟩ hx => by
        simp only [_root_.Set.mem_preimage] at hx
        simp only [TotalSpace.mk_inj, dif_pos hx, hs.coeff_apply_of_mem hx]
        exact (hs.toBasisAt hx).equivFun.symm_apply_apply v
      right_inv' := fun ⟨x, v⟩ hx => by
        simp only [Prod.mk_right_inj, dif_pos hx.1]
        funext i
        simp only [coeff, dif_pos hx.1]
        exact (hs.toBasisAt hx.1).coord_equivFun_symm i v
      open_target := hW.prod isOpen_univ
      baseSet := W
      open_baseSet := hW
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ => rfl }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsSubbundleFrameOn.pretrivialization then
    throwError "Refusing to shadow existing declaration IsSubbundleFrameOn.pretrivialization"
  Lean.modifyEnv fun env => Lean.addAlias env `IsSubbundleFrameOn.pretrivialization ``Submission.IsSubbundleFrameOn.pretrivialization

instance pretrivialization_isLinear [Finite ι]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W) (hW : IsOpen W) :
    (hs.pretrivialization hW).IsLinear 𝕜 where
  linear x _ := by
    refine ⟨?_, ?_⟩
    · intro v w
      funext i
      exact map_add (hs.coeff i x) v w
    · intro c v
      funext i
      exact map_smul (hs.coeff i x) c v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsSubbundleFrameOn.pretrivialization_isLinear then
    throwError "Refusing to shadow existing declaration IsSubbundleFrameOn.pretrivialization_isLinear"
  Lean.modifyEnv fun env => Lean.addAlias env `IsSubbundleFrameOn.pretrivialization_isLinear ``Submission.IsSubbundleFrameOn.pretrivialization_isLinear

@[simp]
theorem pretrivialization_apply [Finite ι]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W) (hW : IsOpen W)
    (z : _root_.Bundle.TotalSpace (ι → 𝕜) (fun x => S x)) :
    hs.pretrivialization hW z = (z.1, fun i => hs.coeff i z.1 z.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsSubbundleFrameOn.pretrivialization_apply then
    throwError "Refusing to shadow existing declaration IsSubbundleFrameOn.pretrivialization_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `IsSubbundleFrameOn.pretrivialization_apply ``Submission.IsSubbundleFrameOn.pretrivialization_apply

theorem pretrivialization_symm_coe [Fintype ι]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W) (hW : IsOpen W)
    {x : M} (hx : x ∈ W) (c : ι → 𝕜) :
    ((hs.pretrivialization hW).symm x c : V x) = ∑ i, c i • s i x := by
  classical
  have hmk := (hs.pretrivialization hW).mk_symm hx c
  change (⟨x, (hs.pretrivialization hW).symm x c⟩ : _root_.Bundle.TotalSpace (ι → 𝕜) (fun x => S x)) =
    ⟨x, if hx : x ∈ W then (hs.toBasisAt hx).equivFun.symm c else 0⟩ at hmk
  simp only [TotalSpace.mk_inj, dif_pos hx] at hmk
  rw [hmk, Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, toBasisAt_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsSubbundleFrameOn.pretrivialization_symm_coe then
    throwError "Refusing to shadow existing declaration IsSubbundleFrameOn.pretrivialization_symm_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `IsSubbundleFrameOn.pretrivialization_symm_coe ``Submission.IsSubbundleFrameOn.pretrivialization_symm_coe

theorem pretrivialization_symm_eq_sum [Fintype ι]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W) (hW : IsOpen W)
    {x : M} (hx : x ∈ W) (c : ι → 𝕜) :
    (hs.pretrivialization hW).symm x c = ∑ i, c i • hs.subtypeSection i x := by
  apply Subtype.ext
  rw [hs.pretrivialization_symm_coe hW hx]
  simp only [Submodule.coe_sum, Submodule.coe_smul, subtypeSection_coe_of_mem hs hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsSubbundleFrameOn.pretrivialization_symm_eq_sum then
    throwError "Refusing to shadow existing declaration IsSubbundleFrameOn.pretrivialization_symm_eq_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `IsSubbundleFrameOn.pretrivialization_symm_eq_sum ``Submission.IsSubbundleFrameOn.pretrivialization_symm_eq_sum

theorem pretrivialization_totalSpaceMk_isInducing [Finite ι]
    [CompleteSpace 𝕜] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W) (hW : IsOpen W)
    {x : M} (hx : x ∈ W) :
    Topology.IsInducing (hs.pretrivialization hW ∘ TotalSpace.mk x) := by
  let _ : T2Space (V x) := FiberBundle.t2Space F V x
  have heq : hs.pretrivialization hW ∘ TotalSpace.mk x =
      fun v => (x, (hs.toBasisAt hx).equivFunL v) := by
    funext v
    simp only [Function.comp_apply, pretrivialization_apply, coeff_apply_of_mem hs hx]
    rfl
  rw [heq]
  exact Topology.isInducing_const_prod.mpr (hs.toBasisAt hx).equivFunL.toHomeomorph.isInducing

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsSubbundleFrameOn.pretrivialization_totalSpaceMk_isInducing then
    throwError "Refusing to shadow existing declaration IsSubbundleFrameOn.pretrivialization_totalSpaceMk_isInducing"
  Lean.modifyEnv fun env => Lean.addAlias env `IsSubbundleFrameOn.pretrivialization_totalSpaceMk_isInducing ``Submission.IsSubbundleFrameOn.pretrivialization_totalSpaceMk_isInducing

variable [CompleteSpace 𝕜]

def pretrivializationCoordChange [Finite ι]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    {t : ι → (x : M) → V x} {W' : Set M}
    (ht : IsSubbundleFrameOn (I := I) (F := F) (n := n) S t W')
    (x : M) : (ι → 𝕜) →L[𝕜] (ι → 𝕜) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  exact (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := ι → 𝕜) ι).symm
    (fun i j => ht.coeff j x (hs.subtypeSection i x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsSubbundleFrameOn.pretrivializationCoordChange then
    throwError "Refusing to shadow existing declaration IsSubbundleFrameOn.pretrivializationCoordChange"
  Lean.modifyEnv fun env => Lean.addAlias env `IsSubbundleFrameOn.pretrivializationCoordChange ``Submission.IsSubbundleFrameOn.pretrivializationCoordChange

theorem pretrivializationCoordChange_apply [Finite ι]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    {t : ι → (x : M) → V x} {W' : Set M}
    (ht : IsSubbundleFrameOn (I := I) (F := F) (n := n) S t W')
    (hW : IsOpen W) (hW' : IsOpen W') {x : M} (hx : x ∈ W) (c : ι → 𝕜) :
    hs.pretrivializationCoordChange ht x c =
      (ht.pretrivialization hW' ⟨x, (hs.pretrivialization hW).symm x c⟩).2 := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  change (LinearEquiv.piRing 𝕜 (ι → 𝕜) ι 𝕜).symm
      (fun i j => ht.coeff j x (hs.subtypeSection i x)) c = _
  rw [LinearEquiv.piRing_symm_apply, pretrivialization_apply,
    hs.pretrivialization_symm_eq_sum hW hx]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsSubbundleFrameOn.pretrivializationCoordChange_apply then
    throwError "Refusing to shadow existing declaration IsSubbundleFrameOn.pretrivializationCoordChange_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `IsSubbundleFrameOn.pretrivializationCoordChange_apply ``Submission.IsSubbundleFrameOn.pretrivializationCoordChange_apply

theorem contMDiffOn_pretrivializationCoordChange
    [Fintype ι] [FiniteDimensional 𝕜 F] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I]
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s W)
    {t : ι → (x : M) → V x} {W' : Set M}
    (ht : IsSubbundleFrameOn (I := I) (F := F) (n := n) S t W')
    (hW : IsOpen W) (hW' : IsOpen W') :
    ContMDiffOn I 𝓘(𝕜, (ι → 𝕜) →L[𝕜] (ι → 𝕜)) n
      (hs.pretrivializationCoordChange ht) (W ∩ W') := by
  classical
  have hcols : ContMDiffOn I 𝓘(𝕜, ι → ι → 𝕜) n
      (fun x i j => ht.coeff j x (hs.subtypeSection i x)) (W ∩ W') := by
    apply contMDiffOn_pi_space.mpr
    intro i
    apply contMDiffOn_pi_space.mpr
    intro j
    exact ht.contMDiffOn_coeff_of_subset (hW.inter hW') _root_.Set.inter_subset_right
      (hs.subtypeSection i) ((hs.contMDiffOn_subtypeSection_coe i).mono _root_.Set.inter_subset_left) j
  have hmap := (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := ι → 𝕜) ι).symm.toContinuousLinearMap
    |>.contMDiff.comp_contMDiffOn hcols
  refine hmap.congr ?_
  intro x hx
  change hs.pretrivializationCoordChange ht x =
    (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := ι → 𝕜) ι).symm
      (fun i j => ht.coeff j x (hs.subtypeSection i x))
  dsimp only [pretrivializationCoordChange]
  congr 1
  rw [Subsingleton.elim (Fintype.ofFinite ι) (inferInstance : Fintype ι)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsSubbundleFrameOn.contMDiffOn_pretrivializationCoordChange then
    throwError "Refusing to shadow existing declaration IsSubbundleFrameOn.contMDiffOn_pretrivializationCoordChange"
  Lean.modifyEnv fun env => Lean.addAlias env `IsSubbundleFrameOn.contMDiffOn_pretrivializationCoordChange ``Submission.IsSubbundleFrameOn.contMDiffOn_pretrivializationCoordChange

end IsSubbundleFrameOn

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
variable [VectorBundle 𝕜 F V] {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]

namespace ContMDiffVectorSubbundle

def vectorPrebundle (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n)) :
    VectorPrebundle 𝕜 (Fin S.rank → 𝕜) (fun x => S.fiber x) := by
  let U : M → Set M := fun x => (S.exists_frame x).choose
  let s : M → Fin S.rank → (x : M) → V x := fun x => (S.exists_frame x).choose_spec.choose
  have hU (x : M) : IsOpen (U x) := (S.exists_frame x).choose_spec.choose_spec.1
  have hxU (x : M) : x ∈ U x := (S.exists_frame x).choose_spec.choose_spec.2.1
  have hs (x : M) : IsSubbundleFrameOn (I := I) (F := F) (n := n) S.fiber (s x) (U x) :=
    (S.exists_frame x).choose_spec.choose_spec.2.2
  exact
    { pretrivializationAtlas := {e | ∃ (W : Set M) (t : Fin S.rank → (x : M) → V x)
          (hW : IsOpen W) (ht : IsSubbundleFrameOn (I := I) (F := F) (n := n) S.fiber t W),
          e = ht.pretrivialization hW}
      pretrivialization_linear' := by
        rintro e ⟨W, t, hW, ht, rfl⟩
        infer_instance
      pretrivializationAt := fun x => (hs x).pretrivialization (hU x)
      mem_base_pretrivializationAt := hxU
      pretrivialization_mem_atlas := fun x => ⟨U x, s x, hU x, hs x, rfl⟩
      exists_coordChange := by
        rintro e ⟨W, t, hW, ht, rfl⟩ e' ⟨W', t', hW', ht', rfl⟩
        refine ⟨ht.pretrivializationCoordChange ht',
          (ht.contMDiffOn_pretrivializationCoordChange ht' hW hW').continuousOn, ?_⟩
        intro x hx c
        exact ht.pretrivializationCoordChange_apply ht' hW hW' hx.1 c
      totalSpaceMk_isInducing := fun x =>
        (hs x).pretrivialization_totalSpaceMk_isInducing (hU x) (hxU x) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.vectorPrebundle then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.vectorPrebundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.vectorPrebundle ``Submission.ContMDiffVectorSubbundle.vectorPrebundle

instance vectorPrebundle_isContMDiff
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n)) :
    S.vectorPrebundle.IsContMDiff I n where
  exists_contMDiffCoordChange := by
    rintro e ⟨W, t, hW, ht, rfl⟩ e' ⟨W', t', hW', ht', rfl⟩
    refine ⟨ht.pretrivializationCoordChange ht',
      ht.contMDiffOn_pretrivializationCoordChange ht' hW hW', ?_⟩
    intro x hx c
    exact ht.pretrivializationCoordChange_apply ht' hW hW' hx.1 c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.vectorPrebundle_isContMDiff then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.vectorPrebundle_isContMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.vectorPrebundle_isContMDiff ``Submission.ContMDiffVectorSubbundle.vectorPrebundle_isContMDiff

@[instance_reducible]
def totalSpaceTopology
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n)) :
    TopologicalSpace (_root_.Bundle.TotalSpace (Fin S.rank → 𝕜) (fun x => S.fiber x)) :=
  S.vectorPrebundle.totalSpaceTopology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.totalSpaceTopology then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.totalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.totalSpaceTopology ``Submission.ContMDiffVectorSubbundle.totalSpaceTopology

@[instance_reducible]
def fiberBundle
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n)) :
    letI := S.totalSpaceTopology
    FiberBundle (Fin S.rank → 𝕜) (fun x => S.fiber x) :=
  S.vectorPrebundle.toFiberBundle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.fiberBundle then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.fiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.fiberBundle ``Submission.ContMDiffVectorSubbundle.fiberBundle

theorem vector_bundle
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n)) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    VectorBundle 𝕜 (Fin S.rank → 𝕜) (fun x => S.fiber x) :=
  S.vectorPrebundle.toVectorBundle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.vector_bundle then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.vector_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.vector_bundle ``Submission.ContMDiffVectorSubbundle.vector_bundle

theorem contMDiffVectorBundle
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n)) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    ContMDiffVectorBundle n (Fin S.rank → 𝕜) (fun x => S.fiber x) I :=
  S.vectorPrebundle.contMDiffVectorBundle I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.contMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.contMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.contMDiffVectorBundle ``Submission.ContMDiffVectorSubbundle.contMDiffVectorBundle

end ContMDiffVectorSubbundle

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
variable [VectorBundle 𝕜 F V] {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]

namespace ContMDiffVectorSubbundle

def frameTrivialization
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    {W : Set M} {s : Fin S.rank → (x : M) → V x}
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S.fiber s W) (hW : IsOpen W) :
    letI := S.totalSpaceTopology
    _root_.Bundle.Trivialization (Fin S.rank → 𝕜)
      (TotalSpace.proj : _root_.Bundle.TotalSpace (Fin S.rank → 𝕜) (fun x => S.fiber x) → M) :=
  S.vectorPrebundle.trivializationOfMemPretrivializationAtlas ⟨W, s, hW, hs, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.frameTrivialization then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.frameTrivialization"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.frameTrivialization ``Submission.ContMDiffVectorSubbundle.frameTrivialization

instance frameTrivialization_memAtlas
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    {W : Set M} {s : Fin S.rank → (x : M) → V x}
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S.fiber s W) (hW : IsOpen W) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    MemTrivializationAtlas (S.frameTrivialization hs hW) := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  exact ⟨hs.pretrivialization hW, ⟨W, s, hW, hs, rfl⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.frameTrivialization_memAtlas then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.frameTrivialization_memAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.frameTrivialization_memAtlas ``Submission.ContMDiffVectorSubbundle.frameTrivialization_memAtlas

@[simp]
theorem frameTrivialization_apply
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    {W : Set M} {s : Fin S.rank → (x : M) → V x}
    (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S.fiber s W) (hW : IsOpen W)
    (z : _root_.Bundle.TotalSpace (Fin S.rank → 𝕜) (fun x => S.fiber x)) :
    S.frameTrivialization hs hW z = (z.1, fun i => hs.coeff i z.1 z.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.frameTrivialization_apply then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.frameTrivialization_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.frameTrivialization_apply ``Submission.ContMDiffVectorSubbundle.frameTrivialization_apply

theorem contMDiff_subtypeVal
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n)) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ContMDiff (I.prod 𝓘(𝕜, Fin S.rank → 𝕜)) (I.prod 𝓘(𝕜, F)) n
      (fun z : _root_.Bundle.TotalSpace (Fin S.rank → 𝕜) (fun x => S.fiber x) =>
        (⟨z.1, (z.2 : V z.1)⟩ : _root_.Bundle.TotalSpace F V)) := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  intro z
  obtain ⟨W, s, hW, hzW, hs⟩ := S.exists_frame z.1
  let e := S.frameTrivialization hs hW
  let q := _root_.FiberBundle.trivializationAt F V z.1
  have hzq : z.1 ∈ q.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F V z.1
  have hze : z ∈ e.source := hzW
  have hproj : ContMDiffAt (I.prod 𝓘(𝕜, Fin S.rank → 𝕜)) I n
      (TotalSpace.proj : _root_.Bundle.TotalSpace (Fin S.rank → 𝕜) (fun x => S.fiber x) → M) z :=
    Bundle.contMDiffAt_proj (fun x => S.fiber x)
  have hcoord : ContMDiffAt (I.prod 𝓘(𝕜, Fin S.rank → 𝕜))
      𝓘(𝕜, Fin S.rank → 𝕜) n (fun p => (e p).2) z :=
    ((e.contMDiffAt_iff (f := id) hze).mp contMDiffAt_id).2
  have hframe (i : Fin S.rank) : ContMDiffAt I 𝓘(𝕜, F) n
      (fun x => (q (TotalSpace.mk' F x (s i x))).2) z.1 :=
    (q.contMDiffAt_section_iff hzq).mp ((hs.contMDiffOn i).contMDiffAt (hW.mem_nhds hzW))
  have hsum : ContMDiffAt (I.prod 𝓘(𝕜, Fin S.rank → 𝕜)) 𝓘(𝕜, F) n
      (fun p => ∑ i, (e p).2 i • (q (TotalSpace.mk' F p.1 (s i p.1))).2) z := by
    exact ContMDiffAt.sum fun i _ =>
      (contMDiffAt_pi_space.mp hcoord i).smul ((hframe i).comp z hproj)
  apply (q.contMDiffAt_iff (f := fun p : _root_.Bundle.TotalSpace (Fin S.rank → 𝕜) (fun x => S.fiber x) =>
    (⟨p.1, (p.2 : V p.1)⟩ : _root_.Bundle.TotalSpace F V)) (q.mem_source.mpr hzq)).mpr
  refine ⟨hproj, hsum.congr_of_eventuallyEq ?_⟩
  filter_upwards [hproj.continuousAt ((hW.inter q.open_baseSet).mem_nhds ⟨hzW, hzq⟩)] with p hp
  have heq := congrArg (q.linearMapAt 𝕜 p.1) (hs.coeff_sum_eq hp.1 p.2)
  simpa only [map_sum, map_smul, q.coe_linearMapAt_of_mem hp.2,
    e, frameTrivialization_apply] using heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.contMDiff_subtypeVal then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.contMDiff_subtypeVal"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.contMDiff_subtypeVal ``Submission.ContMDiffVectorSubbundle.contMDiff_subtypeVal

theorem contMDiffOn_section_iff
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    (U : Set M) (hU : IsOpen U) (σ : (x : M) → S.fiber x) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ContMDiffOn I (I.prod 𝓘(𝕜, Fin S.rank → 𝕜)) n
      (fun x => TotalSpace.mk' (Fin S.rank → 𝕜) x (σ x)) U ↔
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F x (σ x : V x)) U := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  constructor
  · intro hσ
    exact S.contMDiff_subtypeVal.comp_contMDiffOn hσ
  · intro hσ x hx
    obtain ⟨W, s, hW, hxW, hs⟩ := S.exists_frame x
    let e := S.frameTrivialization hs hW
    have hc : ContMDiffOn I 𝓘(𝕜, Fin S.rank → 𝕜) n
        (fun y i => hs.coeff i y (σ y)) (U ∩ W) := by
      apply contMDiffOn_pi_space.mpr
      intro i
      exact hs.contMDiffOn_coeff_of_subset (hU.inter hW) _root_.Set.inter_subset_right σ
        (hσ.mono _root_.Set.inter_subset_left) i
    have he : ContMDiffAt I 𝓘(𝕜, Fin S.rank → 𝕜) n
        (fun y => (e (TotalSpace.mk' (Fin S.rank → 𝕜) y (σ y))).2) x :=
      hc.contMDiffAt ((hU.inter hW).mem_nhds ⟨hx, hxW⟩)
    exact ((e.contMDiffAt_section_iff hxW).mpr he).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.contMDiffOn_section_iff then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.contMDiffOn_section_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.contMDiffOn_section_iff ``Submission.ContMDiffVectorSubbundle.contMDiffOn_section_iff

theorem contMDiff_section_iff
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    (σ : (x : M) → S.fiber x) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ContMDiff I (I.prod 𝓘(𝕜, Fin S.rank → 𝕜)) n
      (fun x => TotalSpace.mk' (Fin S.rank → 𝕜) x (σ x)) ↔
    ContMDiff I (I.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F x (σ x : V x)) := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  simpa only [contMDiffOn_univ] using S.contMDiffOn_section_iff _root_.Set.univ isOpen_univ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.contMDiff_section_iff then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.contMDiff_section_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.contMDiff_section_iff ``Submission.ContMDiffVectorSubbundle.contMDiff_section_iff

end ContMDiffVectorSubbundle

end

section

private theorem isInducing_of_local_leftInverse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    (h : ∀ x : X, ∃ (U : Set Y) (g : Y → X), U ∈ 𝓝 (f x) ∧
      Filter.Tendsto g (𝓝 (f x)) (𝓝 x) ∧ ∀ y, f y ∈ U → g (f y) = y) :
    Topology.IsInducing f := by
  apply Topology.isInducing_iff_nhds.mpr
  intro x
  refine le_antisymm hf.continuousAt.le_comap ?_
  obtain ⟨U, g, hU, hg, hgf⟩ := h x
  have ht : Filter.Tendsto (g ∘ f) (Filter.comap f (𝓝 (f x))) (𝓝 x) :=
    hg.comp Filter.tendsto_comap
  have heq : (g ∘ f) =ᶠ[Filter.comap f (𝓝 (f x))] id := by
    filter_upwards [Filter.preimage_mem_comap hU] with y hy
    exact hgf y hy
  simpa only [Filter.tendsto_id'] using ht.congr' heq

run_cmd do
  let target := ``Submission.isInducing_of_local_leftInverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `isInducing_of_local_leftInverse target :: scope.openDecls } }

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
variable [VectorBundle 𝕜 F V] {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]

namespace ContMDiffVectorSubbundle

theorem isEmbedding_subtypeVal
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n)) :
    letI := S.totalSpaceTopology
    Topology.IsEmbedding
      (fun z : _root_.Bundle.TotalSpace (Fin S.rank → 𝕜) (fun x => S.fiber x) =>
        (⟨z.1, (z.2 : V z.1)⟩ : _root_.Bundle.TotalSpace F V)) := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  let f : _root_.Bundle.TotalSpace (Fin S.rank → 𝕜) (fun x => S.fiber x) → _root_.Bundle.TotalSpace F V :=
    fun z => ⟨z.1, (z.2 : V z.1)⟩
  have hf : Continuous f := S.contMDiff_subtypeVal.continuous
  have hfind : Topology.IsInducing f := by
    apply isInducing_of_local_leftInverse f hf
    intro z
    obtain ⟨W, s, hW, hzW, hs⟩ := S.exists_frame z.1
    obtain ⟨U, B, hU, hzU, hUW, hB, hcoeff⟩ :=
      hs.exists_contMDiffOn_coeff_extension hW hzW
    let e := S.frameTrivialization hs hW
    let q := _root_.FiberBundle.trivializationAt F V z.1
    let O : Set (_root_.Bundle.TotalSpace F V) := TotalSpace.proj ⁻¹' U
    let g : _root_.Bundle.TotalSpace F V → _root_.Bundle.TotalSpace (Fin S.rank → 𝕜) (fun x => S.fiber x) :=
      fun p => e.toOpenPartialHomeomorph.symm (p.1, B p.1 ((q p).2))
    have hO : IsOpen O := hU.preimage (FiberBundle.continuous_proj F V)
    have hfzO : f z ∈ O := hzU
    have hgf (p : _root_.Bundle.TotalSpace (Fin S.rank → 𝕜) (fun x => S.fiber x)) (hp : f p ∈ O) :
        g (f p) = p := by
      change e.toOpenPartialHomeomorph.symm (p.1, B p.1 ((q (f p)).2)) = p
      rw [hcoeff p.1 hp p.2]
      change e.toOpenPartialHomeomorph.symm (e p) = p
      exact e.left_inv ((hUW hp).1 : p ∈ e.source)
    have hproj : ContinuousAt (TotalSpace.proj : _root_.Bundle.TotalSpace F V → M) (f z) :=
      (FiberBundle.continuous_proj F V).continuousAt
    have hzq : f z ∈ q.source := q.mem_source.mpr (hUW hzU).2
    have hq : ContinuousAt (fun p : _root_.Bundle.TotalSpace F V => (q p).2) (f z) :=
      (q.continuousOn.continuousAt (q.open_source.mem_nhds hzq)).snd
    have hBz : ContinuousAt B z.1 := hB.continuousOn.continuousAt (hU.mem_nhds hzU)
    have hpair : ContinuousAt
        (fun p : _root_.Bundle.TotalSpace F V => (p.1, B p.1 ((q p).2))) (f z) :=
      hproj.prodMk ((hBz.comp (f := (TotalSpace.proj : _root_.Bundle.TotalSpace F V → M)) hproj).clm_apply hq)
    have htarget : ((f z).1, B (f z).1 ((q (f z)).2)) ∈ e.target :=
      ⟨hzW, _root_.Set.mem_univ _⟩
    have hg : ContinuousAt g (f z) :=
      (e.toOpenPartialHomeomorph.continuousOn_symm.continuousAt
        (e.open_target.mem_nhds htarget)).comp
          (f := fun p : _root_.Bundle.TotalSpace F V => (p.1, B p.1 ((q p).2))) hpair
    exact ⟨O, g, hO.mem_nhds hfzO, by simpa only [hgf z hfzO] using hg.tendsto, hgf⟩
  refine ⟨hfind, ?_⟩
  rintro ⟨x, v⟩ ⟨y, w⟩ h
  have hxy : x = y := congrArg TotalSpace.proj h
  subst y
  have hvw : (v : V x) = (w : V x) := by
    simpa only [f, TotalSpace.mk_inj] using h
  congr 1
  exact Subtype.ext hvw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.isEmbedding_subtypeVal then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.isEmbedding_subtypeVal"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.isEmbedding_subtypeVal ``Submission.ContMDiffVectorSubbundle.isEmbedding_subtypeVal

end ContMDiffVectorSubbundle

end
