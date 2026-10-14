/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homology.PathConcatenation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set
open scoped _root_.Simplicial

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {a b : X} {p q : Path a b}

def pathHomotopyDiagonal (F : Path.Homotopy p q) : Path a b where
  toFun t := F (t, t)
  continuous_toFun := F.continuous.comp (continuous_id.prodMk continuous_id)
  source' := F.source 0
  target' := F.target 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathHomotopyDiagonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathHomotopyDiagonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathHomotopyDiagonal ``Submission.DifferentialGeometry.Topology.pathHomotopyDiagonal

noncomputable def pathHomotopyLowerSimplex (F : Path.Homotopy p q) :
    integralSingularSimplex 2 X :=
  (integralSingularSimplexEquiv 2 X).symm
    ⟨fun t => F (_root_.Set.projIcc 0 1 zero_le_one (t.val 2),
        _root_.Set.projIcc 0 1 zero_le_one (t.val 1 + t.val 2)),
      F.continuous.comp
        ((continuous_projIcc.comp ((continuous_apply 2).comp continuous_subtype_val)).prodMk
          (continuous_projIcc.comp (((continuous_apply 1).comp continuous_subtype_val).add
            ((continuous_apply 2).comp continuous_subtype_val))))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathHomotopyLowerSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathHomotopyLowerSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathHomotopyLowerSimplex ``Submission.DifferentialGeometry.Topology.pathHomotopyLowerSimplex

noncomputable def pathHomotopyUpperSimplex (F : Path.Homotopy p q) :
    integralSingularSimplex 2 X :=
  (integralSingularSimplexEquiv 2 X).symm
    ⟨fun t => F (_root_.Set.projIcc 0 1 zero_le_one (t.val 1 + t.val 2),
        _root_.Set.projIcc 0 1 zero_le_one (t.val 2)),
      F.continuous.comp
        ((continuous_projIcc.comp (((continuous_apply 1).comp continuous_subtype_val).add
          ((continuous_apply 2).comp continuous_subtype_val))).prodMk
          (continuous_projIcc.comp ((continuous_apply 2).comp continuous_subtype_val)))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathHomotopyUpperSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathHomotopyUpperSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathHomotopyUpperSimplex ``Submission.DifferentialGeometry.Topology.pathHomotopyUpperSimplex

theorem pathHomotopyLowerSimplex_faces (F : Path.Homotopy p q) (i : Fin 3) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (pathHomotopyLowerSimplex F) =
      ![integralPathSimplex (Path.refl b), integralPathSimplex (pathHomotopyDiagonal F),
        integralPathSimplex p] i := by
  apply (integralSingularSimplexEquiv 1 X).injective
  apply ContinuousMap.ext
  intro t
  have ht : t.val 0 + t.val 1 = 1 := by simpa [Fin.sum_univ_two] using t.property.2
  have hp : _root_.Set.projIcc (0 : ℝ) 1 zero_le_one (t.val 1) = stdSimplexHomeomorphUnitInterval t :=
    _root_.Set.projIcc_val _ (stdSimplexHomeomorphUnitInterval t)
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ i (pathHomotopyLowerSimplex F)) t = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 2 X ((integralSingularSimplexEquiv 2 X).symm _)
    (stdSimplex.map i.succAbove t) = _
  rw [Equiv.apply_symm_apply]
  change F (_root_.Set.projIcc 0 1 zero_le_one
      ((FunOnFinite.linearMap ℝ ℝ i.succAbove t.val) 2),
    _root_.Set.projIcc 0 1 zero_le_one ((FunOnFinite.linearMap ℝ ℝ i.succAbove t.val) 1 +
      (FunOnFinite.linearMap ℝ ℝ i.succAbove t.val) 2)) = _
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, Fin.sum_univ_two]
  fin_cases i <;> norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.ext_iff,
    ht, hp, integralPathSimplex_apply, pathHomotopyDiagonal]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathHomotopyLowerSimplex_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathHomotopyLowerSimplex_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathHomotopyLowerSimplex_faces ``Submission.DifferentialGeometry.Topology.pathHomotopyLowerSimplex_faces

theorem pathHomotopyUpperSimplex_faces (F : Path.Homotopy p q) (i : Fin 3) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (pathHomotopyUpperSimplex F) =
      ![integralPathSimplex q, integralPathSimplex (pathHomotopyDiagonal F),
        integralPathSimplex (Path.refl a)] i := by
  apply (integralSingularSimplexEquiv 1 X).injective
  apply ContinuousMap.ext
  intro t
  have ht : t.val 0 + t.val 1 = 1 := by simpa [Fin.sum_univ_two] using t.property.2
  have hp : _root_.Set.projIcc (0 : ℝ) 1 zero_le_one (t.val 1) = stdSimplexHomeomorphUnitInterval t :=
    _root_.Set.projIcc_val _ (stdSimplexHomeomorphUnitInterval t)
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ i (pathHomotopyUpperSimplex F)) t = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 2 X ((integralSingularSimplexEquiv 2 X).symm _)
    (stdSimplex.map i.succAbove t) = _
  rw [Equiv.apply_symm_apply]
  change F (_root_.Set.projIcc 0 1 zero_le_one
      ((FunOnFinite.linearMap ℝ ℝ i.succAbove t.val) 1 +
        (FunOnFinite.linearMap ℝ ℝ i.succAbove t.val) 2),
    _root_.Set.projIcc 0 1 zero_le_one ((FunOnFinite.linearMap ℝ ℝ i.succAbove t.val) 2)) = _
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, Fin.sum_univ_two]
  fin_cases i <;> norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.ext_iff,
    ht, hp, integralPathSimplex_apply, pathHomotopyDiagonal]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathHomotopyUpperSimplex_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathHomotopyUpperSimplex_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathHomotopyUpperSimplex_faces ``Submission.DifferentialGeometry.Topology.pathHomotopyUpperSimplex_faces

theorem integralPathChain_sub_mem_range_of_homotopic (h : Path.Homotopic p q) :
    integralPathChain p - integralPathChain q ∈
      LinearMap.range ((integralSingularChains X).d 2 1).hom := by
  obtain ⟨F⟩ := h
  refine ⟨integralSimplexChain 2 (pathHomotopyLowerSimplex F) -
    integralSimplexChain 2 (pathHomotopyUpperSimplex F) -
    integralSimplexChain 2 (pathConcatenationSimplex (Path.refl b) (Path.refl b)) +
    integralSimplexChain 2 (pathConcatenationSimplex (Path.refl a) (Path.refl a)), ?_⟩
  simp only [map_add, map_sub, integralSimplexChain_boundary_two,
    pathHomotopyLowerSimplex_faces, pathHomotopyUpperSimplex_faces,
    pathConcatenationSimplex_faces, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Path.refl_trans_refl]
  change integralPathChain (Path.refl b) - integralPathChain (pathHomotopyDiagonal F) +
      integralPathChain p -
      (integralPathChain q - integralPathChain (pathHomotopyDiagonal F) +
        integralPathChain (Path.refl a)) -
      (integralPathChain (Path.refl b) - integralPathChain (Path.refl b) +
        integralPathChain (Path.refl b)) +
      (integralPathChain (Path.refl a) - integralPathChain (Path.refl a) +
        integralPathChain (Path.refl a)) = _
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathChain_sub_mem_range_of_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathChain_sub_mem_range_of_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathChain_sub_mem_range_of_homotopic ``Submission.DifferentialGeometry.Topology.integralPathChain_sub_mem_range_of_homotopic

end DifferentialGeometry.Topology
