import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Topology.Compactness.LocallyCompact
import Submission.DifferentialGeometry.Topology.Manifold.CompactSectionExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.Function _root_.Manifold _root_.Module
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Topology

universe uE uH uM

variable {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private def bumpCoordinateMap {ι : Type*} {S : Set M}
    (f : SmoothBumpCovering ι I M S) : M → ι → E × ℝ :=
  fun x i => (f i x • extChartAt I (f.c i) x, f i x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.bumpCoordinateMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.bumpCoordinateMap target :: scope.openDecls } }

private theorem contMDiff_bumpCoordinateMap {ι : Type*} [Fintype ι] {S : Set M}
    (f : SmoothBumpCovering ι I M S) :
    ContMDiff I 𝓘(ℝ, ι → E × ℝ) ∞ (bumpCoordinateMap f) :=
  contMDiff_pi_space.mpr fun i =>
    ((f i).contMDiff_smul contMDiffOn_extChartAt).prodMk_space (f i).contMDiff

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.contMDiff_bumpCoordinateMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.contMDiff_bumpCoordinateMap target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private theorem hasCompactSupport_bumpCoordinateMap {ι : Type*} [Finite ι] {S : Set M}
    (f : SmoothBumpCovering ι I M S) : HasCompactSupport (bumpCoordinateMap f) := by
  apply HasCompactSupport.intro (isCompact_iUnion fun i => (f i).hasCompactSupport)
  intro x hx
  funext i
  have hi : f i x = 0 := by
    by_contra hne
    exact hx (mem_iUnion.mpr ⟨i, subset_closure hne⟩)
  simp only [bumpCoordinateMap, hi, zero_smul, Pi.zero_apply, Prod.zero_eq_mk]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.hasCompactSupport_bumpCoordinateMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.hasCompactSupport_bumpCoordinateMap target :: scope.openDecls } }

omit [IsManifold I ∞ M] [T2Space M] in
private theorem injOn_bumpCoordinateMap {ι : Type*} {S : Set M}
    (f : SmoothBumpCovering ι I M S) : _root_.Set.InjOn (bumpCoordinateMap f) S := by
  intro x hx y _ hxy
  have hi := congrFun hxy (f.ind x hx)
  obtain ⟨hcoord, hscalar⟩ := Prod.mk_inj.mp hi
  rw [f.apply_ind x hx] at hscalar
  rw [← hscalar, f.apply_ind x hx, one_smul, one_smul] at hcoord
  exact (extChartAt I (f.c (f.ind x hx))).injOn (f.mem_extChartAt_ind_source x hx)
    (f.mem_extChartAt_source_of_eq_one hscalar.symm) hcoord

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.injOn_bumpCoordinateMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.injOn_bumpCoordinateMap target :: scope.openDecls } }

private theorem injective_mfderiv_bumpCoordinateMap {ι : Type*} [Fintype ι] {S : Set M}
    (f : SmoothBumpCovering ι I M S) (x : M) (hx : x ∈ S) :
    Injective (mfderiv I 𝓘(ℝ, ι → E × ℝ) (bumpCoordinateMap f) x) := by
  let P : (ι → E × ℝ) →L[ℝ] E :=
    (ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.proj (f.ind x hx))
  have hcomp : P.comp (mfderiv I 𝓘(ℝ, ι → E × ℝ) (bumpCoordinateMap f) x) =
      mfderiv I I (chartAt H (f.c (f.ind x hx))) x := by
    have hp := P.hasMFDerivAt.comp x
      ((contMDiff_bumpCoordinateMap f).mdifferentiableAt (by simp)).hasMFDerivAt
    convert! hasMFDerivAt_unique hp ?_
    apply (hasMFDerivAt_extChartAt (f.mem_chartAt_ind_source x hx)).congr_of_eventuallyEq
    filter_upwards [f.eventuallyEq_one x hx] with y hy
    simp only [P, bumpCoordinateMap, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply, Function.comp_apply]
    rw [hy, Pi.one_apply, one_smul]
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  rw [← (mdifferentiable_chart (f.c (f.ind x hx))).ker_mfderiv_eq_bot
    (f.mem_chartAt_ind_source x hx), ← hcomp]
  exact LinearMap.ker_le_ker_comp _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.injective_mfderiv_bumpCoordinateMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.injective_mfderiv_bumpCoordinateMap target :: scope.openDecls } }

theorem exists_contMDiff_embedding_on_nhds_of_isCompact {K : Set M} (hK : IsCompact K) :
    ∃ (N : TopologicalSpace.Opens M) (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n)),
      K ⊆ N ∧ ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧
      HasCompactSupport e ∧ _root_.Topology.IsEmbedding (fun x : N => e x) ∧
      ∀ x ∈ N, _root_.Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x) := by
  classical
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  obtain ⟨t, f, _⟩ := exists_finite_smoothBumpCovering_of_isCompact (I := I) hL
    (fun _ => _root_.Set.univ) (fun _ _ => Filter.univ_mem)
  let ι := ↥t
  let V := ι → E × ℝ
  let : IsNoetherian ℝ (E × ℝ) := IsNoetherian.iff_fg.2 inferInstance
  let : FiniteDimensional ℝ V := IsNoetherian.iff_fg.1 inferInstance
  let n := _root_.Module.finrank ℝ V
  let T : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e : M → EuclideanSpace ℝ (Fin n) := T ∘ (bumpCoordinateMap f)
  have he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e :=
    T.toDiffeomorph.contMDiff.comp (contMDiff_bumpCoordinateMap f)
  have hinj : _root_.Set.InjOn e L := by
    intro x hx y hy hxy
    exact (injOn_bumpCoordinateMap f) hx hy (T.injective hxy)
  let N : TopologicalSpace.Opens M := ⟨interior L, isOpen_interior⟩
  have hN : (N : Set M) ⊆ L := interior_subset
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hEL : _root_.Topology.IsEmbedding (fun x : L => e x) :=
    ((he.continuous.comp continuous_subtype_val).isClosedEmbedding
      (fun x y hxy => Subtype.ext (hinj x.property y.property hxy))).isEmbedding
  have hEN : _root_.Topology.IsEmbedding (fun x : N => e x) :=
    hEL.comp (_root_.Topology.IsEmbedding.inclusion hN)
  refine ⟨N, n, e, hKL, he,
    (hasCompactSupport_bumpCoordinateMap f).comp_left T.map_zero, hEN, ?_⟩
  intro x hx
  have hd : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x =
      T.toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, V) (bumpCoordinateMap f) x) := by
    rw [mfderiv_comp x T.differentiableAt.mdifferentiableAt
      ((contMDiff_bumpCoordinateMap f).mdifferentiableAt (by simp)), T.mfderiv_eq]
    rfl
  rw [hd]
  exact T.injective.comp (injective_mfderiv_bumpCoordinateMap f x (hN hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_contMDiff_embedding_on_nhds_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_contMDiff_embedding_on_nhds_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_contMDiff_embedding_on_nhds_of_isCompact ``Submission.DifferentialGeometry.Topology.exists_contMDiff_embedding_on_nhds_of_isCompact

theorem exists_contMDiff_compactly_supported_euclidean_embedding_comp
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (γ : C(X, M)) (hγ : _root_.Topology.IsEmbedding γ) :
    ∃ (n : ℕ) (Φ : M → EuclideanSpace ℝ (Fin n)),
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Φ ∧
      HasCompactSupport Φ ∧ _root_.Topology.IsEmbedding (Φ ∘ γ) := by
  obtain ⟨N, n, Φ, hKN, hΦ, hΦc, hΦN, _⟩ :=
    exists_contMDiff_embedding_on_nhds_of_isCompact (I := I) (isCompact_range γ.continuous)
  refine ⟨n, Φ, hΦ, hΦc, ?_⟩
  apply ((hΦ.continuous.comp γ.continuous).isClosedEmbedding ?_).isEmbedding
  intro x y hxy
  have hx : γ x ∈ N := hKN (_root_.Set.mem_range_self x)
  have hy : γ y ∈ N := hKN (_root_.Set.mem_range_self y)
  have heq : (⟨γ x, hx⟩ : N) = ⟨γ y, hy⟩ := hΦN.injective hxy
  exact hγ.injective (congrArg Subtype.val heq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_contMDiff_compactly_supported_euclidean_embedding_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_contMDiff_compactly_supported_euclidean_embedding_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_contMDiff_compactly_supported_euclidean_embedding_comp ``Submission.DifferentialGeometry.Topology.exists_contMDiff_compactly_supported_euclidean_embedding_comp

end DifferentialGeometry.Topology

end

end
