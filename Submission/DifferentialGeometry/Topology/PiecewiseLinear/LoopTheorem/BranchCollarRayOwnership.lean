/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Covering.SheetTrace
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedIntervalLink
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarSides

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem exists_derived_collar_ray_in_source_sheet (hD : NormalSingularCellData D BdM B)
    {ι : M → E} (hι : Function.Injective ι) (hPL : IsPiecewiseAffineOn (ι ∘ D) D.domain)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J)
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (haR : {ι (D a)} ∈ R.faces) (positive : Bool)
    (harm : (PiecewiseLinear.restrict R
      ((fun t : ℝ => ι (D (ρ (a, t)))) ''
        (if positive then _root_.Set.Icc (0 : ℝ) 1 else _root_.Set.Icc (-1 : ℝ) 0))).space =
      (fun t : ℝ => ι (D (ρ (a, t)))) ''
        (if positive then _root_.Set.Icc (0 : ℝ) 1 else _root_.Set.Icc (-1 : ℝ) 0))
    {A B : Set (EuclideanSpace ℝ (Fin 2))} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) (haA : a ∈ A)
    (hpre : ∀ x ∈ D.domain, ι (D x) ∈ (derivedNeighborhoodCell R {ι (D a)}).space → x ∈ A ∪ B) :
    ∃ v ∈ _root_.Set.Icc (-1 : ℝ) 1, (if positive then 0 < v else v < 0) ∧
      ρ (a, v) ∈ A ∩ collarHalf J ρ positive ∧
      (derivedNeighborhoodCellBase R {ι (D a)}).space ∩
        ((fun t : ℝ => ι (D (ρ (a, t)))) ''
          (if positive then _root_.Set.Icc (0 : ℝ) 1 else _root_.Set.Icc (-1 : ℝ) 0)) = {ι (D (ρ (a, v)))} := by
  let F : ℝ → E := fun t => ι (D (ρ (a, t)))
  let l : ℝ := if positive then 0 else -1
  let u : ℝ := if positive then 1 else 0
  have hlu : l < u := by cases positive <;> norm_num [l, u]
  have hI : _root_.Set.Icc l u = (if positive then _root_.Set.Icc (0 : ℝ) 1 else _root_.Set.Icc (-1 : ℝ) 0) := by
    cases positive <;> rfl
  have hIsub : _root_.Set.Icc l u ⊆ _root_.Set.Icc (-1 : ℝ) 1 := by
    cases positive <;> intro t ht <;> constructor <;> dsimp [l, u] at ht ⊢ <;>
      linarith [ht.1, ht.2]
  have h0 : (0 : ℝ) ∈ _root_.Set.Icc l u := by cases positive <;> constructor <;> norm_num [l, u]
  have hFfull := hD.isPLHomeomorphOn_collarFiber hι hPL hρ ha
  have hF := hFfull.restrict (isHPolytope_Icc (a := l) (b := u)).isPolyhedron hIsub
  have hF0 : F 0 = ι (D a) := congrArg (ι ∘ D) (hρ.2.2.2.2.2.2.1 a ha)
  let K := PiecewiseLinear.restrict R (F '' _root_.Set.Icc l u)
  let _ : Finite K.faces := (restrict_faces_finite R _).to_subtype
  have hKspace : K.space = F '' _root_.Set.Icc l u := by simpa only [K, hI, F] using harm
  have hFK : IsPLHomeomorphOn F (_root_.Set.Icc l u) K.space := hKspace.symm ▸ hF
  have hpEnd : ι (D a) = F l ∨ ι (D a) = F u := by
    cases positive
    · exact Or.inr hF0.symm
    · exact Or.inl hF0.symm
  obtain ⟨v, hv, hne, hbase⟩ := exists_derived_interval_link_parameter R K
    (restrict_faces_subset R _) hlu hFK haR hpEnd
  have hcenterK : ι (D a) ∈ K.space := hF0 ▸ hFK.bijOn.mapsTo h0
  have hpK : {ι (D a)} ∈ K.faces := mem_faces_of_mem_openSimplex_of_mem_space
    (restrict_faces_subset R _) haR
    (by simpa only [Finset.centroid_singleton, id_eq] using
      centroid_mem_openSimplex (Finset.singleton_nonempty (ι (D a))))
    hcenterK
  have hsegment : (derivedNeighborhoodCell R {ι (D a)}).space ∩ K.space =
      segment ℝ (ι (D a)) (F v) := by
    simpa only [Finset.centroid_singleton, id_eq] using
      derivedNeighborhoodCell_inter_eq_segment_of_base_inter_singleton R K
        (restrict_faces_subset R _) hpK hbase
  have hρc : ContinuousOn (fun t : ℝ => ρ (a, t)) (_root_.Set.Icc l u) :=
    hρ.2.2.2.2.2.1.isPiecewiseAffineOn.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨ha, hIsub ht⟩)
  have hTsub : segment ℝ (ι (D a)) (F v) ⊆ F '' _root_.Set.Icc l u := by
    rw [← hKspace, ← hsegment]
    exact _root_.Set.inter_subset_right
  have hTcell : segment ℝ (ι (D a)) (F v) ⊆
      (derivedNeighborhoodCell R {ι (D a)}).space := by
    rw [← hsegment]
    exact _root_.Set.inter_subset_left
  have hvA : ρ (a, v) ∈ A := Covering.source_label_of_preconnected_image _root_.CompactIccSpace.isCompact_Icc
    hF.isPiecewiseAffineOn.continuousOn hF.bijOn.injOn hρc hA hB hAB
    (convex_segment _ _).isPreconnected hTsub
    (fun t ht hFt => hpre _ (interior_subset (hρ.2.2.1
      (hρ.2.2.2.2.2.1.bijOn.mapsTo ⟨ha, hIsub ht⟩))) (hTcell hFt)) h0
    (by rwa [hρ.2.2.2.2.2.2.1 a ha])
    (hF0.symm ▸ left_mem_segment ℝ (ι (D a)) (F v)) v hv (right_mem_segment ℝ _ _)
  have hv0 : v ≠ 0 := fun h => hne ((congrArg F h).trans hF0)
  have hvsign : if positive then 0 < v else v < 0 := by
    cases positive
    · exact lt_of_le_of_ne hv.2 hv0
    · exact lt_of_le_of_ne hv.1 hv0.symm
  refine ⟨v, hIsub hv, hvsign, ⟨hvA, ?_⟩, ?_⟩
  · exact (hD.mem_collarHalf_iff hρ ha (hIsub hv) positive).mpr
      (by cases positive <;> exact hvsign.le)
  · rwa [hKspace, hI] at hbase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_derived_collar_ray_in_source_sheet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_derived_collar_ray_in_source_sheet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_derived_collar_ray_in_source_sheet ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_derived_collar_ray_in_source_sheet

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData
