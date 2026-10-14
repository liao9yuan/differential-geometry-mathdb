/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInwardPush
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DoubleCoverProjection
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryLocalEmbedding
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem NonsingularCell.exists_isPLHomeomorphOn_eqOn_boundary
    {S : NormalSystem E} (D : NonsingularCell S) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → E,
      IsPLHomeomorphOn f D.sourceComplex.space (f '' D.sourceComplex.space) ∧
      _root_.Set.MapsTo f D.sourceComplex.space S.manifoldComplex.space ∧
      _root_.Set.EqOn f (simplicialMap D.sourceComplex D.vertexMap) (frontier D.sourceComplex.space) ∧
      D.sourceComplex.space ∩ f ⁻¹' S.boundaryComplex.space = frontier D.sourceComplex.space ∧
      f '' D.sourceComplex.space ∩ S.boundaryComplex.space = f '' frontier D.sourceComplex.space ∧
      range (fun θ => (D.boundaryLoop θ : E)) = f '' frontier D.sourceComplex.space := by
  let _ : Finite D.sourceComplex.faces := D.finite_source.to_subtype
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  have hfront : frontier D.sourceComplex.space ⊆ D.sourceComplex.space :=
    frontier_subset_closure.trans (isPolyhedron_space D.sourceComplex).isClosed.closure_eq.subset
  have hmap := simplicialMap_mapsTo D.sourceComplex S.manifoldComplex D.vertexMap D.source_faces_map
  have hb : _root_.Set.MapsTo (simplicialMap D.sourceComplex D.vertexMap) (frontier D.sourceComplex.space)
      (PiecewiseLinear.boundaryComplex 3 S.manifoldComplex).space := by
    intro x hx
    have hrange : simplicialMap D.sourceComplex D.vertexMap x ∈
        range (fun θ => (D.boundaryLoop θ : E)) := D.boundary_range.symm ▸ ⟨x, hx, rfl⟩
    obtain ⟨θ, hθ⟩ := hrange
    rw [← hθ]
    exact derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex (D.boundaryLoop θ).2
  obtain ⟨f, hf, hfmap, hfix, hpre, hinter⟩ :=
    S.isManifold.exists_isPLHomeomorphOn_eqOn_preimage_boundary S.manifoldComplex
      (isPolyhedron_space D.sourceComplex) D.source_isPLBall.isPLSphere_frontier.isPolyhedron
      hfront (isPiecewiseAffineOn_simplicialMap D.sourceComplex D.vertexMap) D.nonsingular hmap hb
  have himage := hfix.image_eq
  exact ⟨f, hf, hfmap, hfix, hpre, hinter.trans himage.symm,
    D.boundary_range.trans himage.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.exists_isPLHomeomorphOn_eqOn_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.exists_isPLHomeomorphOn_eqOn_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.exists_isPLHomeomorphOn_eqOn_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.exists_isPLHomeomorphOn_eqOn_boundary

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open _root_.Classical in
theorem DoubleCoverDiagram.preimage_boundaryComplex_subset
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T) :
    T.manifoldComplex.space ∩ R.projection ⁻¹' S.boundaryComplex.space ⊆
      T.boundaryComplex.space := by
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ : Finite T.manifoldComplex.faces := T.manifoldComplex_faces_finite.to_subtype
  have hpl := R.isPiecewiseAffineOn_projection.mono_of_isPolyhedron
    (isPolyhedron_space T.manifoldComplex) T.manifoldComplex_space_subset_ambient
  obtain ⟨hloc, -⟩ := Covering.locally_injective_fiber_le_of_isCoveringMap_restrict
    R.isCoveringMap (fun _ => rfl) (continuous_id.continuousOn (s := T.manifoldComplex.space))
    (Function.injective_id.injOn) T.manifoldComplex_space_subset_ambient
    (fun y => (R.fiber_card y).le)
  exact hpl.preimage_boundaryComplex_subset_of_isLocallyInjective T.manifoldComplex
    S.manifoldComplex T.isManifold S.isManifold
    (R.projection_mapsTo.mono_left T.manifoldComplex_space_subset_ambient)
    (Covering.isLocallyInjective_domRestrict_iff.mpr hloc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.DoubleCoverDiagram.preimage_boundaryComplex_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.DoubleCoverDiagram.preimage_boundaryComplex_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.DoubleCoverDiagram.preimage_boundaryComplex_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.DoubleCoverDiagram.preimage_boundaryComplex_subset

open _root_.Classical in
theorem DoubleCoverDiagram.exists_projected_disk_with_boundary
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (D : NonsingularCell T) :
    ∃ (g : EuclideanSpace ℝ (Fin 2) → F) (f : EuclideanSpace ℝ (Fin 2) → E)
      (γ : freeLoop S.boundaryNeighborhoodSpace) (q : Path S.basepoint (γ 0)),
      IsPLHomeomorphOn g D.sourceComplex.space (g '' D.sourceComplex.space) ∧
      _root_.Set.MapsTo g D.sourceComplex.space T.manifoldComplex.space ∧
      _root_.Set.EqOn g (simplicialMap D.sourceComplex D.vertexMap) (frontier D.sourceComplex.space) ∧
      f = R.projection ∘ g ∧ IsPiecewiseAffineOn f D.sourceComplex.space ∧
      _root_.Set.MapsTo f D.sourceComplex.space S.manifoldComplex.space ∧
      (∀ x ∈ D.sourceComplex.space, ∃ U ∈ 𝓝[D.sourceComplex.space] x, _root_.Set.InjOn f U) ∧
      (∀ y, (D.sourceComplex.space ∩ f ⁻¹' {y}).encard ≤ 2) ∧
      D.sourceComplex.space ∩ f ⁻¹' S.boundaryComplex.space = frontier D.sourceComplex.space ∧
      f '' D.sourceComplex.space ∩ S.boundaryComplex.space = f '' frontier D.sourceComplex.space ∧
      _root_.Set.range (fun θ => (γ θ : E)) = f '' frontier D.sourceComplex.space ∧
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint γ q) S.normalSubgroup := by
  obtain ⟨g, hg, hgmap, hgfix, hgpre, -, -⟩ := D.exists_isPLHomeomorphOn_eqOn_boundary
  obtain ⟨f, γ, q, hfg, hf, hfmap, hloc, htwo, hboundary, havoid⟩ :=
    R.exists_projected_disk_of_embedding D hg.isPiecewiseAffineOn hg.bijOn.injOn hgmap hgfix
  have hfront : frontier D.sourceComplex.space ⊆ D.sourceComplex.space :=
    frontier_subset_closure.trans D.source_isPLBall.isPolyhedron.isClosed.closure_eq.subset
  have hfb : _root_.Set.MapsTo f (frontier D.sourceComplex.space) S.boundaryComplex.space := by
    intro x hx
    obtain ⟨θ, hθ⟩ := hboundary.symm.subset ⟨x, hx, rfl⟩
    rw [← hθ]
    exact derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex (γ θ).2
  have hpre : D.sourceComplex.space ∩ f ⁻¹' S.boundaryComplex.space =
      frontier D.sourceComplex.space := by
    apply Subset.antisymm
    · rintro x ⟨hx, hfx⟩
      have hgx : g x ∈ T.boundaryComplex.space :=
        R.preimage_boundaryComplex_subset ⟨hgmap hx, by
          simpa only [_root_.Set.mem_preimage, hfg, Function.comp_apply] using hfx⟩
      exact hgpre.subset ⟨hx, hgx⟩
    · exact fun x hx => ⟨hfront hx, hfb hx⟩
  refine ⟨g, f, γ, q, hg, hgmap, hgfix, hfg, hf, hfmap, hloc, htwo, hpre, ?_, hboundary, havoid⟩
  apply Subset.antisymm
  · rintro y ⟨⟨x, hx, rfl⟩, hfx⟩
    exact ⟨x, hpre.subset ⟨hx, hfx⟩, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, hfront hx, rfl⟩, hfb hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.DoubleCoverDiagram.exists_projected_disk_with_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.DoubleCoverDiagram.exists_projected_disk_with_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.DoubleCoverDiagram.exists_projected_disk_with_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.DoubleCoverDiagram.exists_projected_disk_with_boundary
end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
