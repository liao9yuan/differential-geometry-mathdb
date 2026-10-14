import Submission.DifferentialGeometry.Topology.Embedding.Extension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace Manifold
open _root_.Manifold

open _root_.Manifold in
private theorem exists_contDiff_compact_eq_nhds_of_extension
    {M V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞} {f : M → V} {g : M → F} {K : Set M} {O U C : Set V} {G W : V → F}
    (hG : ContDiff ℝ n G) (hGc : HasCompactSupport G) (hGO : tsupport G ⊆ O)
    (hGg : _root_.Set.EqOn (G ∘ f) g K) (hO : IsOpen O) (hU : IsOpen U)
    (hC : IsCompact C) (hCU : C ⊆ U ∩ O) (hW : ContDiffOn ℝ n W U)
    (hWg : ∀ x ∈ K, f x ∈ U → W (f x) = g x) :
    ∃ G : V → F, ContDiff ℝ n G ∧ HasCompactSupport G ∧ tsupport G ⊆ O ∧
      EqOn (G ∘ f) g K ∧ G =ᶠ[𝓝ˢ C] W := by
  obtain ⟨χ, hχ, hχc, hχone, hχsupp, _⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hC (hU.inter hO) hCU
  have hχn : ContDiff ℝ n χ := hχ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hcor : ContDiff ℝ n (fun z => χ z • (W z - G z)) := by
    apply contDiffOn_univ.mp
    apply DifferentialGeometry.Analysis.contDiffOn_cutoff_smul hU hχn
      (hχsupp.trans _root_.Set.inter_subset_left)
    simpa only [_root_.Set.univ_inter] using hW.sub hG.contDiffOn
  refine ⟨fun z => G z + χ z • (W z - G z), hG.add hcor,
    hGc.add hχc.smul_right, ?_, ?_, ?_⟩
  · exact (tsupport_add _ _).trans (_root_.Set.union_subset hGO
      ((tsupport_smul_subset_left _ _).trans (hχsupp.trans _root_.Set.inter_subset_right)))
  · intro x hx
    change G (f x) + χ (f x) • (W (f x) - G (f x)) = g x
    rw [show G (f x) = g x from hGg hx]
    by_cases hxU : f x ∈ U
    · rw [hWg x hx hxU, sub_self, smul_zero, add_zero]
    · have hχzero : χ (f x) = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hxU (hχsupp h).1)
      rw [hχzero, zero_smul, add_zero]
  · filter_upwards [hχone] with z hz
    simp only [hz, Pi.one_apply, one_smul]
    rw [add_comm, sub_add_cancel]

run_cmd do
  let target := ``Submission.Manifold.exists_contDiff_compact_eq_nhds_of_extension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.exists_contDiff_compact_eq_nhds_of_extension target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞} {f : M → V} {g : M → F} {K : Set M}

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.exists_contDiff_compact_extension_eq_nhds
    (hf : _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) n f) (hg : ContMDiff I 𝓘(ℝ, F) n g)
    (hK : IsCompact K) {O U C : Set V} (hO : IsOpen O)
    (hKO : f '' (K ∩ tsupport g) ⊆ O) (hU : IsOpen U)
    (hC : IsCompact C) (hCU : C ⊆ U ∩ O) {W : V → F}
    (hW : ContDiffOn ℝ n W U)
    (hWg : ∀ x ∈ K, f x ∈ U → W (f x) = g x) :
    ∃ G : V → F, ContDiff ℝ n G ∧ HasCompactSupport G ∧ tsupport G ⊆ O ∧
      EqOn (G ∘ f) g K ∧ G =ᶠ[𝓝ˢ C] W := by
  obtain ⟨G, hG, hGc, hGO, hGg⟩ :=
    hf.exists_contDiff_compact_extension_of_tsupport_image_subset hg hK hO hKO
  exact exists_contDiff_compact_eq_nhds_of_extension hG hGc hGO hGg hO hU hC hCU hW hWg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.exists_contDiff_compact_extension_eq_nhds then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.exists_contDiff_compact_extension_eq_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.exists_contDiff_compact_extension_eq_nhds ``Submission.Manifold.IsSmoothEmbedding.exists_contDiff_compact_extension_eq_nhds

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.exists_contDiff_compact_extension_prod_halfspace_eq_nhds
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (ModelProd P (EuclideanHalfSpace (d + 1))) N]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : N → V} {g : N → F} {K : Set N}
    (hf : _root_.Manifold.IsSmoothEmbedding (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ f)
    (hg : ContMDiff (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ g)
    (hK : IsCompact K) {O U C : Set V} (hO : IsOpen O)
    (hKO : f '' (K ∩ tsupport g) ⊆ O) (hU : IsOpen U)
    (hC : IsCompact C) (hCU : C ⊆ U ∩ O) {W : V → F}
    (hW : ContDiffOn ℝ ∞ W U)
    (hWg : ∀ x ∈ K, f x ∈ U → W (f x) = g x) :
    ∃ G : V → F, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ tsupport G ⊆ O ∧
      EqOn (G ∘ f) g K ∧ G =ᶠ[𝓝ˢ C] W := by
  obtain ⟨G, hG, hGc, hGO, hGg⟩ :=
    hf.exists_contDiff_compact_extension_prod_halfspace_of_tsupport_image_subset hg hK hO hKO
  exact exists_contDiff_compact_eq_nhds_of_extension (n := ⊤) hG hGc hGO hGg hO hU hC hCU hW hWg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.exists_contDiff_compact_extension_prod_halfspace_eq_nhds then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.exists_contDiff_compact_extension_prod_halfspace_eq_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.exists_contDiff_compact_extension_prod_halfspace_eq_nhds ``Submission.Manifold.IsSmoothEmbedding.exists_contDiff_compact_extension_prod_halfspace_eq_nhds

end Manifold
