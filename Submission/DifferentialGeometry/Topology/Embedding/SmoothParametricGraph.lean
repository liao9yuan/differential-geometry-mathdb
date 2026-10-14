import Submission.DifferentialGeometry.Topology.Embedding.FiniteDimension
import Submission.DifferentialGeometry.Topology.Embedding.ParametricGraph
import Submission.DifferentialGeometry.Topology.Embedding.Retraction
import Submission.DifferentialGeometry.Topology.Embedding.Extension
import Submission.DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import Submission.DifferentialGeometry.Analysis.Calculus.Inverse.MovingImplicit
import Mathlib.Analysis.InnerProductSpace.PiL2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

namespace Manifold
open _root_.Manifold

section

open _root_.Set _root_.Submission.Set

open _root_.Manifold in
private theorem isLocalDiffeomorphAt_of_contDiffOn_invertible
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {A : W → W} {D : Set W} {z : W} (hD : IsOpen D) (hz : z ∈ D)
    (hA : ContDiffOn ℝ ∞ A D) (hinv : (fderiv ℝ A z).IsInvertible) :
    IsLocalDiffeomorphAt 𝓘(ℝ, W) 𝓘(ℝ, W) ∞ A z := by
  let V : Set W := D ∩ (fderiv ℝ A) ⁻¹' _root_.Set.range ((↑) : (W ≃L[ℝ] W) → W →L[ℝ] W)
  have hV : IsOpen V :=
    (hA.continuousOn_fderiv_of_isOpen hD (by simp)).isOpen_inter_preimage
      hD ContinuousLinearEquiv.isOpen
  have hsm : ContMDiffOn 𝓘(ℝ, W) 𝓘(ℝ, W) ∞ A V :=
    (hA.mono _root_.Set.inter_subset_left).contMDiffOn
  apply DifferentialGeometry.Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty hV hsm
    (fun y hy => ?_) ⟨z, hz, hinv⟩
  simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id,
    PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.id_comp,
    Function.comp_id, id_eq] using
      (show (fderiv ℝ A y).IsInvertible from hy.2)

run_cmd do
  let target := ``Submission.Manifold.isLocalDiffeomorphAt_of_contDiffOn_invertible
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.isLocalDiffeomorphAt_of_contDiffOn_invertible target :: scope.openDecls } }

open _root_.Manifold in
private theorem isImmersionAtOfComplement_parametric_graph_of_local_extension
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {e : P × M → V} {t : P} {x : M}
    (hi : _root_.Manifold.IsImmersionAtOfComplement F I 𝓘(ℝ, V) ∞ (fun y => e (t, y)) x)
    {U : Set V} (hU : IsOpen U) (hxU : e (t, x) ∈ U) {A : P × V → V}
    (hA : ContDiffOn ℝ ∞ A (_root_.Set.univ ×ˢ U)) (hA0 : ∀ v, A (t, v) = v)
    (hmatch : ∀ᶠ q : P × M in 𝓝 (t, x), A (q.1, e (t, q.2)) = e q) :
    _root_.Manifold.IsImmersionAtOfComplement (PUnit × F) (𝓘(ℝ, P).prod I)
      (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞ (fun q => (q.1, e q)) (t, x) := by
  let D : Set (P × V) := _root_.Set.univ ×ˢ U
  have hD : IsOpen D := isOpen_univ.prod hU
  have hpD : (t, e (t, x)) ∈ D := ⟨mem_univ _, hxU⟩
  have hAd : DifferentiableAt ℝ A (t, e (t, x)) :=
    (hA.contDiffAt (hD.mem_nhds hpD)).differentiableAt (by simp)
  have hAt : (fun z => A (t, z)) = id := funext hA0
  have hpartial : DifferentialGeometry.Analysis.partialFDeriv₂ A t (e (t, x)) =
      ContinuousLinearMap.id ℝ V :=
    DifferentialGeometry.Analysis.partialFDeriv₂_eq hAd
      (by simpa only [hAt] using hasFDerivAt_id (e (t, x)))
  have hpartialInv :
      (DifferentialGeometry.Analysis.partialFDeriv₂ A t (e (t, x))).IsInvertible := by
    rw [hpartial]
    exact ⟨ContinuousLinearEquiv.refl ℝ V, rfl⟩
  have hpinv := DifferentialGeometry.Analysis.pinnedFDeriv_inv hAd hpartialInv
  have hpfd : HasFDerivAt (DifferentialGeometry.Analysis.pinnedRootMap A)
      ((fderiv ℝ A (t, e (t, x))).prod (ContinuousLinearMap.fst ℝ P V)) (t, e (t, x)) :=
    hAd.hasFDerivAt.prodMk (hasFDerivAt_fst (p := (t, e (t, x))))
  have hblock : ((fderiv ℝ A (t, e (t, x))).prod
      (ContinuousLinearMap.fst ℝ P V)).IsInvertible := by
    rwa [hpfd.fderiv] at hpinv
  let Ψ : P × V → P × V := fun q => (q.1, A q)
  have hΨ : ContDiffOn ℝ ∞ Ψ D := contDiff_fst.contDiffOn.prodMk hA
  have hΨfd : HasFDerivAt Ψ ((ContinuousLinearEquiv.prodComm ℝ V P).toContinuousLinearMap.comp
      ((fderiv ℝ A (t, e (t, x))).prod (ContinuousLinearMap.fst ℝ P V))) (t, e (t, x)) :=
    (ContinuousLinearEquiv.prodComm ℝ V P).hasFDerivAt.comp (t, e (t, x)) hpfd
  have hΨinv : (fderiv ℝ Ψ (t, e (t, x))).IsInvertible := by
    rw [hΨfd.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv.comp hblock
  have hΨlocal : IsLocalDiffeomorphAt (𝓘(ℝ, P).prod 𝓘(ℝ, V))
      (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞ Ψ (t, e (t, x)) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact isLocalDiffeomorphAt_of_contDiffOn_invertible hD hpD hΨ hΨinv
  let G0 : P × M → P × V := Prod.map id (fun y => e (t, y))
  have hG0 : _root_.Manifold.IsImmersionAtOfComplement (PUnit × F) (𝓘(ℝ, P).prod I)
      (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞ G0 (t, x) :=
    (IsImmersionOfComplement.id (I := 𝓘(ℝ, P)) (M := P) (n := ∞) t).prodMap hi
  apply (hG0.isLocalDiffeomorphAt_comp hΨlocal).congr_of_eventuallyEq
  filter_upwards [hmatch] with q hq
  change (q.1, A (q.1, e (t, q.2))) = (q.1, e q)
  exact congrArg (Prod.mk q.1) hq

run_cmd do
  let target := ``Submission.Manifold.isImmersionAtOfComplement_parametric_graph_of_local_extension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.isImmersionAtOfComplement_parametric_graph_of_local_extension target :: scope.openDecls } }

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {e : P × M → V} {t : P} {x : M}

open _root_.Manifold in
private theorem isImmersionAtOfComplement_parametric_graph
    (he : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : Topology.IsEmbedding (fun y => e (t, y)))
    (hi : _root_.Manifold.IsImmersionOfComplement F I 𝓘(ℝ, V) ∞ (fun y => e (t, y))) :
    _root_.Manifold.IsImmersionAtOfComplement (PUnit × F) (𝓘(ℝ, P).prod I)
      (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞ (fun q => (q.1, e q)) (t, x) := by
  classical
  have h0 : _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun y => e (t, y)) :=
    ⟨hi.isImmersion, hf⟩
  obtain ⟨U, hxU, r, hr, -, hfix⟩ := h0.exists_contMDiff_local_retraction x
  let R : V → M := Subtype.val.extend r (fun _ => x)
  have hR (q : U) : R q = r q := Subtype.val_injective.extend_apply r (fun _ => x) q
  have hRsub : ContMDiff 𝓘(ℝ, V) I ∞ (fun q : U => R q) := hr.congr hR
  have hRsm : ContMDiffOn 𝓘(ℝ, V) I ∞ R U := by
    intro z hz
    exact (contMDiffAt_subtype_iff.mp (hRsub ⟨z, hz⟩)).contMDiffWithinAt
  let D : Set (P × V) := _root_.Set.univ ×ˢ (U : Set V)
  have hfst : ContMDiff 𝓘(ℝ, P × V) 𝓘(ℝ, P) ∞ Prod.fst := contDiff_fst.contMDiff
  have hsnd : ContMDiff 𝓘(ℝ, P × V) 𝓘(ℝ, V) ∞ Prod.snd := contDiff_snd.contMDiff
  have hRv : ContMDiffOn 𝓘(ℝ, P × V) I ∞ (fun q => R q.2) D :=
    hRsm.comp hsnd.contMDiffOn (fun _ hq => hq.2)
  have hEr : ContMDiffOn 𝓘(ℝ, P × V) 𝓘(ℝ, V) ∞
      (fun q => e (q.1, R q.2)) D :=
    he.comp_contMDiffOn (hfst.contMDiffOn.prodMk hRv)
  have hE0 : ContMDiffOn 𝓘(ℝ, P × V) 𝓘(ℝ, V) ∞
      (fun q => e (t, R q.2)) D :=
    he.comp_contMDiffOn (contMDiffOn_const.prodMk hRv)
  let A : P × V → V := fun q => q.2 + e (q.1, R q.2) - e (t, R q.2)
  have hA : ContDiffOn ℝ ∞ A D :=
    (contDiff_snd.contDiffOn.add hEr.contDiffOn).sub hE0.contDiffOn
  apply isImmersionAtOfComplement_parametric_graph_of_local_extension
    (hi x) U.isOpen hxU hA (fun z => add_sub_cancel_right z (e (t, R z)))
  have hmem : ∀ᶠ q : P × M in 𝓝 (t, x), e (t, q.2) ∈ U :=
    (hf.continuous.comp continuous_snd).continuousAt.preimage_mem_nhds
      (U.isOpen.mem_nhds hxU)
  filter_upwards [hmem] with q hq
  change e (t, q.2) + e (q.1, R (e (t, q.2))) - e (t, R (e (t, q.2))) = e q
  rw [hR ⟨e (t, q.2), hq⟩, hfix q.2 hq]
  exact add_sub_cancel_left _ _

run_cmd do
  let target := ``Submission.Manifold.isImmersionAtOfComplement_parametric_graph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.isImmersionAtOfComplement_parametric_graph target :: scope.openDecls } }

end

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {e : P × M → V}

open _root_.Manifold in
theorem isImmersionOfComplement_parametric_graph_of_finrank_eq
    {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
    (hdim : Module.finrank ℝ C = Module.finrank ℝ V - Module.finrank ℝ E)
    (he : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun y => e (t, y))) :
    _root_.Manifold.IsImmersionOfComplement C (𝓘(ℝ, P).prod I)
      (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞ (fun q => (q.1, e q)) := by
  rintro ⟨t, x⟩
  have hi : _root_.Manifold.IsImmersionOfComplement C I 𝓘(ℝ, V) ∞ (fun y => e (t, y)) :=
    (hf t).isImmersion.isImmersionOfComplement_of_finrank_eq hdim
  have hg : _root_.Manifold.IsImmersionAtOfComplement (PUnit.{1} × C) (𝓘(ℝ, P).prod I)
      (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞ (fun q => (q.1, e q)) (t, x) :=
    isImmersionAtOfComplement_parametric_graph he (hf t).isEmbedding hi
  exact hg.trans_F (ContinuousLinearEquiv.uniqueProd ℝ C PUnit.{1})

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.isImmersionOfComplement_parametric_graph_of_finrank_eq then
    throwError "Refusing to shadow existing declaration Manifold.isImmersionOfComplement_parametric_graph_of_finrank_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.isImmersionOfComplement_parametric_graph_of_finrank_eq ``Submission.Manifold.isImmersionOfComplement_parametric_graph_of_finrank_eq

open _root_.Manifold in
theorem isSmoothEmbedding_parametric_graph [CompactSpace M]
    (he : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun y => e (t, y))) :
    _root_.Manifold.IsSmoothEmbedding (𝓘(ℝ, P).prod I) (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞
      (fun q => (q.1, e q)) := by
  have hi : _root_.Manifold.IsImmersionOfComplement
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ V - Module.finrank ℝ E)))
      (𝓘(ℝ, P).prod I) (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞ (fun q => (q.1, e q)) :=
    isImmersionOfComplement_parametric_graph_of_finrank_eq (by simp) he hf
  exact ⟨hi.isImmersion,
    (Topology.isClosedEmbedding_parametric_graph he.continuous
      (fun t => (hf t).isEmbedding.injective)).isEmbedding⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.isSmoothEmbedding_parametric_graph then
    throwError "Refusing to shadow existing declaration Manifold.isSmoothEmbedding_parametric_graph"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.isSmoothEmbedding_parametric_graph ``Submission.Manifold.isSmoothEmbedding_parametric_graph

end Manifold

section
namespace Manifold
open _root_.Manifold

open _root_.Manifold in
private theorem isImmersionAtOfComplement_parametric_graph_halfspace
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    {V C : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {e : P × M → V} {p : P} {x : M}
    (h : _root_.Manifold.IsImmersionAtOfComplement C (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun y => e (p, y)) x)
    (he : ContMDiff (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e) :
    _root_.Manifold.IsImmersionAtOfComplement (PUnit.{1} × C) (𝓘(ℝ, P).prod (𝓡∂ (d + 1)))
      (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞ (fun q => (q.1, e q)) (p, x) := by
  obtain ⟨U, hU, hxU, A, hA, hA0, hmatch⟩ :=
    h.exists_contDiffOn_parametric_extension_halfspace he
  exact isImmersionAtOfComplement_parametric_graph_of_local_extension h hU hxU hA hA0 hmatch

run_cmd do
  let target := ``Submission.Manifold.isImmersionAtOfComplement_parametric_graph_halfspace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.isImmersionAtOfComplement_parametric_graph_halfspace target :: scope.openDecls } }

open _root_.Manifold in
private theorem isImmersionOfComplement_parametric_graph_halfspace_of_finrank_eq
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    {V C : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
    {e : P × M → V}
    (hdim : Module.finrank ℝ C = Module.finrank ℝ V - (d + 1))
    (he : ContMDiff (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ p, _root_.Manifold.IsImmersion (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun y => e (p, y))) :
    _root_.Manifold.IsImmersionOfComplement C (𝓘(ℝ, P).prod (𝓡∂ (d + 1)))
      (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞ (fun q => (q.1, e q)) := by
  rintro ⟨p, x⟩
  have hi : _root_.Manifold.IsImmersionOfComplement C (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun y => e (p, y)) :=
    (hf p).isImmersionOfComplement_of_finrank_eq (by simpa using hdim)
  have hg : _root_.Manifold.IsImmersionAtOfComplement (PUnit.{1} × C) (𝓘(ℝ, P).prod (𝓡∂ (d + 1)))
      (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞ (fun q => (q.1, e q)) (p, x) :=
    isImmersionAtOfComplement_parametric_graph_halfspace (hi x) he
  exact hg.trans_F (ContinuousLinearEquiv.uniqueProd ℝ C PUnit.{1})

run_cmd do
  let target := ``Submission.Manifold.isImmersionOfComplement_parametric_graph_halfspace_of_finrank_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.isImmersionOfComplement_parametric_graph_halfspace_of_finrank_eq target :: scope.openDecls } }

open _root_.Manifold in
theorem isImmersion_parametric_graph_halfspace
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : P × M → V}
    (he : ContMDiff (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ p, _root_.Manifold.IsImmersion (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun y => e (p, y))) :
    _root_.Manifold.IsImmersion (𝓘(ℝ, P).prod (𝓡∂ (d + 1)))
      (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞ (fun q => (q.1, e q)) := by
  have hi : _root_.Manifold.IsImmersionOfComplement
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ V - (d + 1))))
      (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞
      (fun q => (q.1, e q)) :=
    isImmersionOfComplement_parametric_graph_halfspace_of_finrank_eq (by simp) he hf
  exact hi.isImmersion

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.isImmersion_parametric_graph_halfspace then
    throwError "Refusing to shadow existing declaration Manifold.isImmersion_parametric_graph_halfspace"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.isImmersion_parametric_graph_halfspace ``Submission.Manifold.isImmersion_parametric_graph_halfspace

open _root_.Manifold in
theorem isSmoothEmbedding_parametric_graph_halfspace
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : P × M → V}
    (he : ContMDiff (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ p, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun y => e (p, y))) :
    _root_.Manifold.IsSmoothEmbedding (𝓘(ℝ, P).prod (𝓡∂ (d + 1)))
      (𝓘(ℝ, P).prod 𝓘(ℝ, V)) ∞ (fun q => (q.1, e q)) := by
  exact ⟨isImmersion_parametric_graph_halfspace he (fun p => (hf p).isImmersion),
    (Topology.isClosedEmbedding_parametric_graph he.continuous
      (fun p => (hf p).isEmbedding.injective)).isEmbedding⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.isSmoothEmbedding_parametric_graph_halfspace then
    throwError "Refusing to shadow existing declaration Manifold.isSmoothEmbedding_parametric_graph_halfspace"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.isSmoothEmbedding_parametric_graph_halfspace ``Submission.Manifold.isSmoothEmbedding_parametric_graph_halfspace

end Manifold

end
