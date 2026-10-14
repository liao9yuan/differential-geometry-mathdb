import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34ReturningArcDisk
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PrismDisk
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallStarring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem IsPLHomeomorphOn.capped_prism_boundary
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) K.space)
    {a b : ℝ} (hab : a < b) {q : (Fin 3 → ℝ) → E × ℝ}
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3))
      (K.space ×ˢ {a} ∪ (r '' stdSimplexBoundary 2) ×ˢ _root_.Set.Icc a b)) :
    q '' stdSimplexBoundary 2 = (r '' stdSimplexBoundary 2) ×ˢ {b} := by
  classical
  let J := r '' stdSimplexBoundary 2
  let S := K.space ×ˢ {a, b} ∪ J ×ˢ _root_.Set.Icc a b
  let A := K.space ×ˢ {a} ∪ J ×ˢ _root_.Set.Icc a b
  have hprod : IsPLBall 3 (K.space ×ˢ _root_.Set.Icc a b) :=
    isPLBall_three_prod hK (isPLBall_Icc hab)
  obtain ⟨T, hTfin, hTspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite T.faces := hTfin.to_subtype
  have hT : IsPLBall 3 T.space := hTspace.symm ▸ hprod
  have hboundary := boundaryComplex_space_prism K hK hab T hTspace
  have hJ : J = (boundaryComplex 2 K).space :=
    hr.image_stdSimplexBoundary_eq_boundaryComplex K rfl
  rw [← hJ] at hboundary
  have hS : IsPLSphere 2 S := by
    change IsPLSphere 2 (K.space ×ˢ {a, b} ∪ J ×ˢ _root_.Set.Icc a b)
    rw [← hboundary]
    exact isPLSphere_boundaryComplex_space_of_isPLBall T hT
  have hJK : J ⊆ K.space := (_root_.Set.image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hAS : A ⊆ S := _root_.Set.union_subset
    (fun _ hx => Or.inl ⟨hx.1, Or.inl hx.2⟩) _root_.Set.subset_union_right
  have hdiff : S \ A = (K.space \ J) ×ˢ {b} := by
    ext z
    constructor
    · rintro ⟨⟨hzK, hza | hzb⟩ | hzside, hzA⟩
      · exact (hzA (Or.inl ⟨hzK, hza⟩)).elim
      · refine ⟨⟨hzK, fun hzJ => hzA (Or.inr ⟨hzJ, ?_⟩)⟩, hzb⟩
        rw [show z.2 = b from hzb]
        exact ⟨hab.le, le_rfl⟩
      · exact (hzA (Or.inr hzside)).elim
    · rintro ⟨⟨hzK, hzJ⟩, hzb⟩
      refine ⟨Or.inl ⟨hzK, Or.inr hzb⟩, ?_⟩
      rintro (⟨_, hza⟩ | ⟨hzJ', _⟩)
      · exact hab.ne (hza.symm.trans hzb)
      · exact hzJ hzJ'
  have hcl : closure (S \ A) = K.space ×ˢ {b} := by
    rw [hdiff, closure_prod_eq, hr.closure_sdiff_image_stdSimplexBoundary,
      isClosed_singleton.closure_eq]
  have hmeet : A ∩ (K.space ×ˢ {b}) = J ×ˢ {b} := by
    ext z
    constructor
    · rintro ⟨hzbase | hzside, hz⟩
      · exact (hab.ne (hzbase.2.symm.trans hz.2)).elim
      · exact ⟨hzside.1, hz.2⟩
    · rintro ⟨hzJ, hzb⟩
      refine ⟨Or.inr ⟨hzJ, ?_⟩, hJK hzJ, hzb⟩
      rw [show z.2 = b from hzb]
      exact ⟨hab.le, le_rfl⟩
  have h := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hAS
  rw [hcl, hmeet] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.capped_prism_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.capped_prism_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.capped_prism_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.capped_prism_boundary

theorem exists_disk_of_lateral_returning_arc
    {P : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P) {a b : ℝ} (hab : a < b)
    {A : Set (E × ℝ)} {γ : ℝ → E × ℝ} (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) A)
    (hAside : A ⊆ (r '' stdSimplexBoundary 2) ×ˢ _root_.Set.Icc a b)
    (hends : A ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = {γ 0, γ 1})
    (hbase : Disjoint A (P ×ˢ ({a} : Set ℝ))) :
    ∃ (F B : Set (E × ℝ)) (q : (Fin 3 → ℝ) → E × ℝ),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) F ∧ IsPLBall 1 B ∧
      F ⊆ (r '' stdSimplexBoundary 2) ×ˢ _root_.Set.Ioc a b ∧
      q '' stdSimplexBoundary 2 = A ∪ B ∧
      F ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = B := by
  classical
  have hP : IsPLBall 2 P := ⟨r, hr⟩
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 2 K.space := hKP.symm ▸ hP
  have hrK : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) K.space := hKP.symm ▸ hr
  have hJ : (boundaryComplex 2 K).space = r '' stdSimplexBoundary 2 :=
    (hr.image_stdSimplexBoundary_eq_boundaryComplex K hKP).symm
  have hD := isPLBall_prism_bottom_union_side K hK hab
  rw [hKP, hJ] at hD
  obtain ⟨d, hd⟩ := hD
  have hrim : d '' stdSimplexBoundary 2 = (r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ) := by
    apply IsPLHomeomorphOn.capped_prism_boundary K hK hrK hab
    rwa [hKP]
  have hAD : A ⊆ P ×ˢ ({a} : Set ℝ) ∪ (r '' stdSimplexBoundary 2) ×ˢ _root_.Set.Icc a b :=
    hAside.trans _root_.Set.subset_union_right
  have hC : IsPLBall 2 (P ×ˢ ({a} : Set ℝ)) :=
    hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const a)
  obtain ⟨F, B, q, hq, hB, hFD, hFC, hqbd, hFB⟩ :=
    hd.exists_returning_crosscut_disk_avoiding_hole hC _root_.Set.subset_union_left hγ hAD
      (hrim.symm ▸ hends) hbase.symm
  refine ⟨F, B, q, hq, hB, ?_, hqbd, hrim ▸ hFB⟩
  intro z hz
  have hzC := disjoint_left.mp hFC hz
  have hzside := (hFD hz).resolve_left hzC
  refine ⟨hzside.1, lt_of_le_of_ne hzside.2.1 ?_, hzside.2.2⟩
  intro heq
  exact hzC ⟨(_root_.Set.image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset hzside.1, heq.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_disk_of_lateral_returning_arc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_disk_of_lateral_returning_arc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_disk_of_lateral_returning_arc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_disk_of_lateral_returning_arc

end DifferentialGeometry.Topology.PiecewiseLinear
