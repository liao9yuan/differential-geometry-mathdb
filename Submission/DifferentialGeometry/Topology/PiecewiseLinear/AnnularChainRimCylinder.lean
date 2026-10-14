/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimIncidence
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainOpenCellCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Circle" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

variable {φ : E3 → E3} {Pt : ℤ → E3}
  {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

private theorem tower_annuli_locallyFinite
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') :
    LocallyFinite (fun i => (Subtype.val : (⋃ j, φ '' A j) → E3) ⁻¹' (φ '' A i)) := by
  intro x
  obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
  have hxI := htw.subsetInterior i (htw.annulus_image_subset i hi)
  have hxD : (x : E3) ∈ Dimg \ (Dbdimg ∪ {P'}) := by
    rw [← htw.annuliEq, _root_.Set.image_iUnion]
    exact x.property
  have hxP : (x : E3) ≠ P' := fun h => hxD.2 (Or.inr h)
  obtain ⟨U, hU, hfinite⟩ := htw.locallyFinite x hxI hxP
  refine ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt.preimage_mem_nhds hU,
    hfinite.subset ?_⟩
  rintro j ⟨y, hyA, hyU⟩
  exact ⟨y, htw.annulus_image_subset j hyA, hyU⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tower_annuli_locallyFinite
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.tower_annuli_locallyFinite target :: scope.openDecls } }

theorem IsCanonicalTower.exists_annuli_cylinder_homeomorph
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') :
    ∃ c : (Circle × ℝ) ≃ₜ ↥(Dimg \ (Dbdimg ∪ {P'})),
      ∀ i : ℤ, _root_.Set.range (fun x => (c (x, (i : ℝ)) : E3)) = φ '' J i := by
  classical
  choose e he₀ he₁ using htw.exists_annulus_homeomorph
  obtain ⟨e', hseam, hlevels⟩ := exists_compatible_annulus_homeomorphs e
    (fun i => (he₁ i).trans (he₀ (i + 1)).symm)
  have hinter (i : ℤ) : (φ '' A i) ∩ (φ '' A (i + 1)) =
      range (fun x => (e' i (x, 1) : E3)) := by
    rw [hlevels, he₁, htw.annulus_image_inter_next]
  obtain ⟨c, hc⟩ := exists_annulus_chain_cylinder_homeomorph e' hseam hinter
    (fun _ _ hij => htw.annulus_image_disjoint hij) (tower_annuli_locallyFinite htw)
  have hcover : (⋃ i, φ '' A i) = Dimg \ (Dbdimg ∪ {P'}) := by
    rw [← _root_.Set.image_iUnion, htw.annuliEq]
  refine ⟨c.trans (Homeomorph.setCongr hcover), fun i => ?_⟩
  have hval (x : Circle) :
      ((c.trans (Homeomorph.setCongr hcover)) (x, (i : ℝ)) : E3) = e' i (x, 0) := by
    change (c (x, (i : ℝ)) : E3) = e' i (x, 0)
    simpa using hc i x 0
  simp_rw [hval]
  rw [hlevels, he₀]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.exists_annuli_cylinder_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.exists_annuli_cylinder_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.exists_annuli_cylinder_homeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.exists_annuli_cylinder_homeomorph

end DifferentialGeometry.Topology.PiecewiseLinear
