import Submission.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Submission.DifferentialGeometry.Topology.Embedding.SmoothParametricGraph
import Submission.DifferentialGeometry.Topology.Embedding.Extension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace Manifold
open _root_.Manifold

open _root_.Set _root_.Submission.Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {e : ℝ × M → V}

open _root_.Manifold in
theorem exists_contDiff_compact_velocity_extension_of_tsupport_image_subset
    (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {K : Set (ℝ × M)} (hK : IsCompact K)
    {O : Set (ℝ × V)} (hO : IsOpen O) (hKO : (fun q : ℝ × M => (q.1, e q)) ''
      (K ∩ tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      EqOn (fun q => X (q.1, e q)) (fun q => deriv (fun s => e (s, q.2)) q.1) K := by
  have hgraph := isSmoothEmbedding_parametric_graph he hf
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgraph
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞
      (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1) :=
    (fun p => DifferentialGeometry.timeDeriv_smoothAt (he p) (by simp))
  exact hgraph.exists_contDiff_compact_extension_of_tsupport_image_subset hv hK hO hKO

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_velocity_extension_of_tsupport_image_subset then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_velocity_extension_of_tsupport_image_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_velocity_extension_of_tsupport_image_subset ``Submission.Manifold.exists_contDiff_compact_velocity_extension_of_tsupport_image_subset

open _root_.Manifold in
theorem exists_contDiff_compact_velocity_extension
    (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {K : Set (ℝ × M)} (hK : IsCompact K)
    {O : Set (ℝ × V)} (hO : IsOpen O) (hKO : (fun q => (q.1, e q)) '' K ⊆ O) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      EqOn (fun q => X (q.1, e q)) (fun q => deriv (fun s => e (s, q.2)) q.1) K :=
  exists_contDiff_compact_velocity_extension_of_tsupport_image_subset he hf hK hO
    ((_root_.Set.image_mono _root_.Set.inter_subset_left).trans hKO)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_velocity_extension then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_velocity_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_velocity_extension ``Submission.Manifold.exists_contDiff_compact_velocity_extension

open _root_.Manifold in
theorem exists_contDiff_compact_velocity_extension_Icc_of_tsupport_image_subset
    (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {O : Set (ℝ × V)} (hO : IsOpen O)
    (hOe : (fun q : ℝ × M => (q.1, e q)) ''
      ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
        tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      ∀ t ∈ _root_.Set.Icc a b, ∀ x, X (t, e (t, x)) = deriv (fun s => e (s, x)) t := by
  obtain ⟨X, hX, hXc, hXO, hXe⟩ :=
    exists_contDiff_compact_velocity_extension_of_tsupport_image_subset he hf
      (isCompact_Icc.prod isCompact_univ) hO hOe
  exact ⟨X, hX, hXc, hXO, fun t ht x => hXe (x := (t, x)) ⟨ht, _root_.Set.mem_univ x⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_velocity_extension_Icc_of_tsupport_image_subset then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_velocity_extension_Icc_of_tsupport_image_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_velocity_extension_Icc_of_tsupport_image_subset ``Submission.Manifold.exists_contDiff_compact_velocity_extension_Icc_of_tsupport_image_subset

open _root_.Manifold in
theorem exists_contDiff_compact_velocity_extension_Icc
    (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {O : Set (ℝ × V)} (hO : IsOpen O)
    (hOe : (fun q => (q.1, e q)) '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ⊆ O) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      ∀ t ∈ _root_.Set.Icc a b, ∀ x, X (t, e (t, x)) = deriv (fun s => e (s, x)) t :=
  exists_contDiff_compact_velocity_extension_Icc_of_tsupport_image_subset he hf hO
    ((_root_.Set.image_mono _root_.Set.inter_subset_left).trans hOe)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_velocity_extension_Icc then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_velocity_extension_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_velocity_extension_Icc ``Submission.Manifold.exists_contDiff_compact_velocity_extension_Icc

end Manifold

section
namespace Manifold
open _root_.Manifold

open _root_.Set _root_.Submission.Set

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
  [CompactSpace M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {e : ℝ × M → V}

open _root_.Manifold in
theorem exists_contDiff_compact_velocity_extension_halfspace_of_tsupport_image_subset
    (he : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {K : Set (ℝ × M)} (hK : IsCompact K)
    {O : Set (ℝ × V)} (hO : IsOpen O) (hKO : (fun q : ℝ × M => (q.1, e q)) ''
      (K ∩ tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      EqOn (fun q => X (q.1, e q)) (fun q => deriv (fun s => e (s, q.2)) q.1) K := by
  have hgraph := isSmoothEmbedding_parametric_graph_halfspace he hf
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgraph
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞
      (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1) := (fun p => DifferentialGeometry.timeDeriv_smoothAt (he p) (by simp))
  exact hgraph.exists_contDiff_compact_extension_prod_halfspace_of_tsupport_image_subset hv hK hO hKO

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_velocity_extension_halfspace_of_tsupport_image_subset then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_velocity_extension_halfspace_of_tsupport_image_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_velocity_extension_halfspace_of_tsupport_image_subset ``Submission.Manifold.exists_contDiff_compact_velocity_extension_halfspace_of_tsupport_image_subset

open _root_.Manifold in
theorem exists_contDiff_compact_velocity_extension_halfspace_Icc_of_tsupport_image_subset
    (he : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {O : Set (ℝ × V)} (hO : IsOpen O)
    (hOe : (fun q : ℝ × M => (q.1, e q)) ''
      ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
        tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      ∀ t ∈ _root_.Set.Icc a b, ∀ x, X (t, e (t, x)) = deriv (fun s => e (s, x)) t := by
  obtain ⟨X, hX, hXc, hXO, hXe⟩ :=
    exists_contDiff_compact_velocity_extension_halfspace_of_tsupport_image_subset he hf
      (isCompact_Icc.prod isCompact_univ) hO hOe
  exact ⟨X, hX, hXc, hXO, fun t ht x => hXe (x := (t, x)) ⟨ht, _root_.Set.mem_univ x⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_velocity_extension_halfspace_Icc_of_tsupport_image_subset then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_velocity_extension_halfspace_Icc_of_tsupport_image_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_velocity_extension_halfspace_Icc_of_tsupport_image_subset ``Submission.Manifold.exists_contDiff_compact_velocity_extension_halfspace_Icc_of_tsupport_image_subset

open _root_.Manifold in
theorem exists_contDiff_compact_velocity_extension_halfspace_Icc
    (he : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {O : Set (ℝ × V)} (hO : IsOpen O)
    (hOe : (fun q => (q.1, e q)) '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ⊆ O) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      ∀ t ∈ _root_.Set.Icc a b, ∀ x, X (t, e (t, x)) = deriv (fun s => e (s, x)) t :=
  exists_contDiff_compact_velocity_extension_halfspace_Icc_of_tsupport_image_subset he hf hO
    ((_root_.Set.image_mono _root_.Set.inter_subset_left).trans hOe)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_velocity_extension_halfspace_Icc then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_velocity_extension_halfspace_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_velocity_extension_halfspace_Icc ``Submission.Manifold.exists_contDiff_compact_velocity_extension_halfspace_Icc

end Manifold

end
