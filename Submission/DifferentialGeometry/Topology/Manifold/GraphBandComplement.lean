import Submission.DifferentialGeometry.Topology.GraphBandComplement
import Submission.DifferentialGeometry.Topology.Manifold.GraphBand

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

variable {E F H G X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G}
  [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X] [PreconnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace G Y] [T2Space Y]
  {n : ℕ∞ω}

theorem exists_graphBand_partialDiffeomorph_inter_closed_of_frontier_eq
    (T : PartialDiffeomorph (I.prod 𝓘(ℝ)) J (X × ℝ) Y n)
    (a b : X → ℝ) (ha : ContMDiff I 𝓘(ℝ) n a) (hb : ContMDiff I 𝓘(ℝ) n b)
    (hab : ∀ q, a q < b q)
    (hsource : {z : X × ℝ | a z.1 ≤ z.2 ∧ z.2 ≤ b z.1} ⊆ T.source)
    {W : Set Y} (hW : IsClosed W)
    (hfront : frontier W =
      _root_.Set.range (fun q => T (q, a q)) ∪ _root_.Set.range (fun q => T (q, b q)))
    (hout : (T '' {z : X × ℝ | a z.1 < z.2 ∧ z.2 < b z.1} \ W).Nonempty) :
    ∃ A : PartialDiffeomorph (I.prod 𝓘(ℝ)) J (X × ℝ) Y n,
      (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ A.source) ∧
      (∀ z, A z = T (z.1, a z.1 + (b z.1 - a z.1) * z.2)) ∧
      (∀ q, A (q, 0) = T (q, a q)) ∧
      (∀ q, A (q, 1) = T (q, b q)) ∧
      IsCompact (A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
      frontier (A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) = frontier W ∧
      (A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∩ W = frontier W := by
  have hband : {z : X × ℝ | z.2 ∈ _root_.Set.uIcc (a z.1) (b z.1)} ⊆ T.source := by
    intro z hz
    change z.2 ∈ _root_.Set.uIcc (a z.1) (b z.1) at hz
    rw [_root_.Set.uIcc_of_le (hab z.1).le] at hz
    exact hsource hz
  obtain ⟨A, hA, hformula, hrange, hcompact, hfrontA⟩ :=
    exists_graphBand_partialDiffeomorph T a b ha hb (fun q => (hab q).ne) hband
  have hset : {z : X × ℝ | z.2 ∈ _root_.Set.uIcc (a z.1) (b z.1)} =
      {z : X × ℝ | a z.1 ≤ z.2 ∧ z.2 ≤ b z.1} := by
    ext z
    rw [_root_.Set.mem_ofPred_eq, _root_.Set.mem_ofPred_eq, _root_.Set.uIcc_of_le (hab z.1).le, _root_.Set.mem_Icc]
  have hinter := (graphBand_image_inter_closed_of_frontier_eq T.toOpenPartialHomeomorph
    a b ha.continuous hb.continuous hab hsource hW hfront hout).2
  refine ⟨A, hA, hformula, ?_, ?_, hcompact, hfrontA.trans hfront.symm, ?_⟩
  · intro q
    rw [hformula]
    simp
  · intro q
    rw [hformula]
    simp
  · rw [hrange, hset]
    exact hinter.trans hfront.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph_inter_closed_of_frontier_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph_inter_closed_of_frontier_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph_inter_closed_of_frontier_eq ``Submission.DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph_inter_closed_of_frontier_eq

theorem exists_graphBand_partialDiffeomorph_cover_of_frontier_eq
    [PreconnectedSpace Y]
    (T : PartialDiffeomorph (I.prod 𝓘(ℝ)) J (X × ℝ) Y n)
    (a b : X → ℝ) (ha : ContMDiff I 𝓘(ℝ) n a) (hb : ContMDiff I 𝓘(ℝ) n b)
    (hab : ∀ q, a q < b q)
    (hsource : {z : X × ℝ | a z.1 ≤ z.2 ∧ z.2 ≤ b z.1} ⊆ T.source)
    {W : Set Y} (hregular : closure (interior W) = W)
    (hfront : frontier W =
      _root_.Set.range (fun q => T (q, a q)) ∪ _root_.Set.range (fun q => T (q, b q)))
    (hout : (T '' {z : X × ℝ | a z.1 < z.2 ∧ z.2 < b z.1} \ W).Nonempty) :
    ∃ A : PartialDiffeomorph (I.prod 𝓘(ℝ)) J (X × ℝ) Y n,
      (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ A.source) ∧
      (∀ z, A z = T (z.1, a z.1 + (b z.1 - a z.1) * z.2)) ∧
      (∀ q, A (q, 0) = T (q, a q)) ∧
      (∀ q, A (q, 1) = T (q, b q)) ∧
      IsCompact (A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
      frontier (A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) = frontier W ∧
      (A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∩ W = frontier W ∧
      W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = univ := by
  have hW : IsClosed W := hregular ▸ isClosed_closure
  obtain ⟨A, hA, hformula, hzero, hone, hcompact, hfrontA, hinter⟩ :=
    exists_graphBand_partialDiffeomorph_inter_closed_of_frontier_eq
      T a b ha hb hab hsource hW hfront hout
  have hface : frontier W = _root_.Set.range (fun q => A (q, 0)) ∪ _root_.Set.range (fun q => A (q, 1)) := by
    simp only [hzero, hone, hfront]
  have hne : (W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)).Nonempty := by
    obtain ⟨y, ⟨⟨q, t⟩, ht, _⟩, _⟩ := hout
    exact ⟨A (q, 0), Or.inr ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩⟩
  exact ⟨A, hA, hformula, hzero, hone, hcompact, hfrontA, hinter,
    union_cylinder_image_eq_univ_of_frontier_eq A.toOpenPartialHomeomorph hA
      hregular hface hinter hne⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph_cover_of_frontier_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph_cover_of_frontier_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph_cover_of_frontier_eq ``Submission.DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph_cover_of_frontier_eq

end DifferentialGeometry.Topology
