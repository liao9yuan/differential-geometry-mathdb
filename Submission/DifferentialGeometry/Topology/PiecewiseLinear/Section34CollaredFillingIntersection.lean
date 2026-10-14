import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredCylinderFrontier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem Section34SeamMarkedBandFilling.exists_enlargement_with_exact_sheet_intersection
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp Cq As Bs S T D F J₀ J₁ : Set M}
    (h : Section34SeamMarkedBandFilling Cc Cp Cq As Bs S T D F J₀ J₁) :
    ∃ (P V : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (c : ℝ),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = Cc ∧
      V ⊆ P ∧ u '' V ⊆ interior S ∧ 0 < c ∧
      IsCombinatorialSolidTorus V ∧
      IsCylindricalDiagram H (_root_.Set.Icc (-c) (1 + c) ×ˢ _root_.Set.Icc (-c) (1 + c)) V ∧
      (∀ z ∈ _root_.Set.Icc (-c) (1 + c) ×ˢ _root_.Set.Icc (-c) (1 + c), H (z, 0) = H (z, 1)) ∧
      frontier V = H ''
        (frontier (_root_.Set.Icc (-c) (1 + c) ×ˢ _root_.Set.Icc (-c) (1 + c)) ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      u '' V ∩ (As ∩ Bs) = J₀ ∪ J₁ := by
  have hDF := h.toFaceAlignedBandFilling.face_annuli_and_intersection.2.2
  obtain ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, hP, hu, hcell, hRfin, -, hRP, -, -, -, -, -, -,
    hfirst, hsecond, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    C, f, α, β, -, -, -, c, L, W, ρ, H,
    hbase, hH, hHends, -, -, hsupport, hc, -, -, -, -, -, -, -, -, hWP, -, hρ,
    hzero, -, -, hread, hfull, -⟩ := h
  let _ : Finite R.faces := hRfin.to_subtype
  have hdis : Disjoint ((u ∘ ρ) '' (frontier R.space ×ˢ _root_.Set.Ioc (0 : ℝ) c)) (As ∩ Bs) :=
    section34_positive_collar_disjoint_sheet_intersection α β
      (fun k p hp s hs hL t ht hB =>
        (hread k p hp s hs hL t ⟨ht.1.le, ht.2⟩).2.2.mp hB)
      (fun x hx t ht hA => (hfull x hx t ht).1.mp hA)
  have hinter := collar_union_preserves_sheet_intersection
    (isPolyhedron_space R).isClosed.frontier_subset hρ.image_eq hzero hdis
  refine ⟨P, R.space ∪ W, u, H, c, hP, hu, hcell,
    _root_.Set.union_subset hRP (hWP.trans interior_subset), hsupport, hc,
    hH.isCombinatorialSolidTorus hbase (by simp), hH, hHends,
    hH.frontier_eq_image_base_frontier hbase (by simp) (by simp), ?_⟩
  rw [hinter]
  calc
    u '' R.space ∩ (As ∩ Bs) = (Bs ∩ u '' R.space) ∩ (As ∩ u '' R.space) := by
      ext x
      simp only [_root_.Set.mem_inter_iff]
      tauto
    _ = D ∩ F := by rw [hfirst, hsecond]
    _ = J₀ ∪ J₁ := hDF

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling.exists_enlargement_with_exact_sheet_intersection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling.exists_enlargement_with_exact_sheet_intersection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling.exists_enlargement_with_exact_sheet_intersection ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling.exists_enlargement_with_exact_sheet_intersection

end DifferentialGeometry.Topology.PiecewiseLinear
