import Submission.DifferentialGeometry.Topology.Embedding.ParametricVelocity
import Submission.DifferentialGeometry.Topology.Embedding.RelativeExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

namespace Manifold
open _root_.Manifold

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {e : ℝ × M → V}

open _root_.Manifold in
theorem exists_contDiff_compact_velocity_extension_eq_nhds
    (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {K : Set (ℝ × M)} (hK : IsCompact K)
    {O U C : Set (ℝ × V)} (hO : IsOpen O)
    (hKO : (fun q : ℝ × M => (q.1, e q)) ''
      (K ∩ tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O)
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U ∩ O)
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ q ∈ K, (q.1, e q) ∈ U → W (q.1, e q) = deriv (fun s => e (s, q.2)) q.1) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      _root_.Set.EqOn (fun q => X (q.1, e q)) (fun q => deriv (fun s => e (s, q.2)) q.1) K ∧
      X =ᶠ[𝓝ˢ C] W := by
  have hgraph := isSmoothEmbedding_parametric_graph he hf
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgraph
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞
      (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1) :=
    fun p => DifferentialGeometry.timeDeriv_smoothAt (he p) (by simp)
  exact hgraph.exists_contDiff_compact_extension_eq_nhds hv hK hO hKO hU hC hCU hW hWe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_velocity_extension_eq_nhds then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_velocity_extension_eq_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_velocity_extension_eq_nhds ``Submission.Manifold.exists_contDiff_compact_velocity_extension_eq_nhds

open _root_.Manifold in
theorem exists_contDiff_compact_velocity_extension_Icc_eq_nhds
    (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {O U C : Set (ℝ × V)} (hO : IsOpen O)
    (hKO : (fun q : ℝ × M => (q.1, e q)) ''
      ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
        tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O)
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U ∩ O)
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ t ∈ _root_.Set.Icc a b, ∀ x, (t, e (t, x)) ∈ U →
      W (t, e (t, x)) = deriv (fun s => e (s, x)) t) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, X (t, e (t, x)) = deriv (fun s => e (s, x)) t) ∧
      X =ᶠ[𝓝ˢ C] W := by
  obtain ⟨X, hX, hXc, hXO, hXe, hXW⟩ :=
    exists_contDiff_compact_velocity_extension_eq_nhds he hf
      (isCompact_Icc.prod isCompact_univ) hO hKO hU hC hCU hW
      (fun q hq => hWe q.1 hq.1 q.2)
  exact ⟨X, hX, hXc, hXO, fun t ht x => hXe (x := (t, x)) ⟨ht, _root_.Set.mem_univ x⟩, hXW⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_velocity_extension_Icc_eq_nhds then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_velocity_extension_Icc_eq_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_velocity_extension_Icc_eq_nhds ``Submission.Manifold.exists_contDiff_compact_velocity_extension_Icc_eq_nhds

end

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
  [CompactSpace M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {e : ℝ × M → V}

open _root_.Manifold in
theorem exists_contDiff_compact_velocity_extension_halfspace_eq_nhds
    (he : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {K : Set (ℝ × M)} (hK : IsCompact K)
    {O U C : Set (ℝ × V)} (hO : IsOpen O)
    (hKO : (fun q : ℝ × M => (q.1, e q)) ''
      (K ∩ tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O)
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U ∩ O)
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ q ∈ K, (q.1, e q) ∈ U → W (q.1, e q) = deriv (fun s => e (s, q.2)) q.1) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      _root_.Set.EqOn (fun q => X (q.1, e q)) (fun q => deriv (fun s => e (s, q.2)) q.1) K ∧
      X =ᶠ[𝓝ˢ C] W := by
  have hgraph := isSmoothEmbedding_parametric_graph_halfspace he hf
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgraph
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞
      (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1) :=
    fun p => DifferentialGeometry.timeDeriv_smoothAt (he p) (by simp)
  exact hgraph.exists_contDiff_compact_extension_prod_halfspace_eq_nhds
    hv hK hO hKO hU hC hCU hW hWe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_velocity_extension_halfspace_eq_nhds then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_velocity_extension_halfspace_eq_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_velocity_extension_halfspace_eq_nhds ``Submission.Manifold.exists_contDiff_compact_velocity_extension_halfspace_eq_nhds

open _root_.Manifold in
theorem exists_contDiff_compact_velocity_extension_halfspace_Icc_eq_nhds
    (he : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {O U C : Set (ℝ × V)} (hO : IsOpen O)
    (hKO : (fun q : ℝ × M => (q.1, e q)) ''
      ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
        tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O)
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U ∩ O)
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ t ∈ _root_.Set.Icc a b, ∀ x, (t, e (t, x)) ∈ U →
      W (t, e (t, x)) = deriv (fun s => e (s, x)) t) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, X (t, e (t, x)) = deriv (fun s => e (s, x)) t) ∧
      X =ᶠ[𝓝ˢ C] W := by
  obtain ⟨X, hX, hXc, hXO, hXe, hXW⟩ :=
    exists_contDiff_compact_velocity_extension_halfspace_eq_nhds he hf
      (isCompact_Icc.prod isCompact_univ) hO hKO hU hC hCU hW
      (fun q hq => hWe q.1 hq.1 q.2)
  exact ⟨X, hX, hXc, hXO, fun t ht x => hXe (x := (t, x)) ⟨ht, _root_.Set.mem_univ x⟩, hXW⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_velocity_extension_halfspace_Icc_eq_nhds then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_velocity_extension_halfspace_Icc_eq_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_velocity_extension_halfspace_Icc_eq_nhds ``Submission.Manifold.exists_contDiff_compact_velocity_extension_halfspace_Icc_eq_nhds

end Manifold
