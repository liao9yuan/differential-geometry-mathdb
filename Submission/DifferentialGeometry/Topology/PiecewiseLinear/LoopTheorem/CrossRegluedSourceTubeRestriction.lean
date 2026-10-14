/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PieceParametrization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem CrossSeamTubeCore.precomp
    {M : Type u} [TopologicalSpace M] {chart : (ℝ × ℝ) × ℝ → M}
    {D S Γ U : Set M} (T : CrossSeamTubeCore chart D S Γ U)
    {f : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ}
    (hf : ContinuousOn f spliceCylinder) (hinj : _root_.Set.InjOn f spliceCylinder)
    (hcyl : _root_.Set.MapsTo f spliceCylinder spliceCylinder)
    (hcore : f '' spliceCore = spliceCore)
    (hfig : f '' crossingFigure = crossingFigure ∩ f '' spliceCylinder) :
    CrossSeamTubeCore (chart ∘ f) D S Γ U := by
  have hsub : (chart ∘ f) '' spliceCylinder ⊆ chart '' spliceCylinder := by
    rw [_root_.Set.image_comp]
    exact _root_.Set.image_mono hcyl.image_subset
  refine ⟨T.isOpen_tube, T.continuousOn_chart.comp hf hcyl, T.injOn_chart.comp hinj hcyl,
    hsub.trans T.image_subset_tube, ?_, ?_, T.double_inter_tube⟩
  · rw [_root_.Set.image_comp, hcore, T.image_spliceCore]
  · rw [_root_.Set.image_comp, hfig]
    have hcross : crossingFigure ⊆ spliceCylinder := by
      intro p hp
      exact ⟨hp.1.elim And.left And.left, hp.2⟩
    rw [T.injOn_chart.image_inter hcross hcyl.image_subset]
    rw [T.image_crossingFigure, _root_.Set.image_comp]
    exact _root_.Set.inter_assoc D (chart '' spliceCylinder) (chart '' (f '' spliceCylinder)) |>.trans
      (congrArg (D ∩ ·) (inter_eq_right.mpr (_root_.Set.image_mono hcyl.image_subset)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeCore.precomp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeCore.precomp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeCore.precomp ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeCore.precomp

theorem PLSeamTubeChart.nonempty_precomp
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {chart : (ℝ × ℝ) × ℝ → M} (C : PLSeamTubeChart M chart)
    {f : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ}
    (hf : IsPLHomeomorphOn f spliceCylinder (f '' spliceCylinder))
    (hcyl : _root_.Set.MapsTo f spliceCylinder spliceCylinder) :
    Nonempty (PLSeamTubeChart M (chart ∘ f)) := by
  have hpoly := isHPolytope_spliceCylinder.isPolyhedron.image_of_isPiecewiseAffineOn
    hf.isPiecewiseAffineOn hf.bijOn.injOn
  have hsub : f '' spliceCylinder ⊆ C.piece.complex.space := by
    rw [C.space_eq]
    exact hcyl.image_subset
  obtain ⟨P, hPspace, hPmap⟩ := C.piece.exists_restrict_of_isPolyhedron hpoly hsub
  have hparam : IsPLHomeomorphOn f C.piece.complex.space P.complex.space := by
    rw [C.space_eq, hPspace]
    exact hf
  let S := P.precomp C.piece.complex C.piece.finite_faces hparam
  have hmap : S.map = chart ∘ f := by
    change P.map ∘ f = chart ∘ f
    rw [hPmap, C.map_eq]
  have himage : C.piece.map '' (f '' spliceCylinder) = (chart ∘ f) '' spliceCylinder := by
    rw [C.map_eq, _root_.Set.image_comp]
  have hbij : _root_.Set.BijOn (chart ∘ f) C.piece.complex.space ((chart ∘ f) '' spliceCylinder) := by
    rw [← himage, ← hmap]
    exact S.bijOn
  refine ⟨⟨⟨C.piece.complex, C.piece.finite_faces, chart ∘ f, hbij, ?_, ?_, ?_⟩,
    C.space_eq, rfl⟩⟩
  · rw [← hmap]
    exact S.continuousOn
  · intro e he
    have h := S.isPiecewiseAffineOn_chart e he
    change IsPiecewiseAffineOn (e ∘ S.map)
      (C.piece.complex.space ∩ S.map ⁻¹' e.source) at h
    rwa [hmap] at h
  · intro e he
    have h := S.isPiecewiseAffineOn_chart_symm e he
    change IsPiecewiseAffineOn (Function.invFunOn S.map C.piece.complex.space ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' (C.piece.map '' (f '' spliceCylinder))) at h
    rwa [hmap, himage] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLSeamTubeChart.nonempty_precomp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLSeamTubeChart.nonempty_precomp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLSeamTubeChart.nonempty_precomp ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLSeamTubeChart.nonempty_precomp

end DifferentialGeometry.Topology.PiecewiseLinear
