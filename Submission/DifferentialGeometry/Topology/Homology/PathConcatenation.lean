/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathEvaluation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.AlgebraicTopology _root_.ContinuousMap
open scoped _root_.Simplicial

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {a b c : X}

noncomputable def pathConcatenationSimplex (p : Path a b) (q : Path b c) :
    integralSingularSimplex 2 X :=
  (integralSingularSimplexEquiv 2 X).symm
    ⟨fun t => (p.trans q).extend (t.val 1 / 2 + t.val 2),
      (p.trans q).continuous_extend.comp
        ((((continuous_apply 1).comp continuous_subtype_val).div_const 2).add
          ((continuous_apply 2).comp continuous_subtype_val))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatenationSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatenationSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatenationSimplex ``Submission.DifferentialGeometry.Topology.pathConcatenationSimplex

theorem pathConcatenationSimplex_faces (p : Path a b) (q : Path b c) (i : Fin 3) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (pathConcatenationSimplex p q) =
      ![integralPathSimplex q, integralPathSimplex (p.trans q), integralPathSimplex p] i := by
  apply (integralSingularSimplexEquiv 1 X).injective
  apply ContinuousMap.ext
  intro t
  have ht : t.val 0 + t.val 1 = 1 := by simpa [Fin.sum_univ_two] using t.property.2
  have ht₀ := t.property.1 0
  have ht₁ := t.property.1 1
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ i (pathConcatenationSimplex p q)) t = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv 2 X ((integralSingularSimplexEquiv 2 X).symm _)
    (stdSimplex.map i.succAbove t) = _
  rw [Equiv.apply_symm_apply]
  change (p.trans q).extend
    ((FunOnFinite.linearMap ℝ ℝ i.succAbove t.val) 1 / 2 +
      (FunOnFinite.linearMap ℝ ℝ i.succAbove t.val) 2) = _
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, Fin.sum_univ_two]
  fin_cases i
  · norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.ext_iff]
    change (p.trans q).extend (t.val 0 / 2 + t.val 1) =
      integralSingularSimplexEquiv 1 X (integralPathSimplex q) t
    rw [integralPathSimplex_apply, Path.extend_trans_of_half_le p q (by linarith)]
    convert q.extend_apply (stdSimplexHomeomorphUnitInterval t).property using 1
    congr 1
    change 2 * (t.val 0 / 2 + t.val 1) - 1 = t.val 1
    linarith
  · norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.ext_iff]
    change (p.trans q).extend (t.val 1) =
      integralSingularSimplexEquiv 1 X (integralPathSimplex (p.trans q)) t
    rw [integralPathSimplex_apply]
    exact (p.trans q).extend_apply (stdSimplexHomeomorphUnitInterval t).property
  · norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.ext_iff]
    change (p.trans q).extend (t.val 1 / 2) =
      integralSingularSimplexEquiv 1 X (integralPathSimplex p) t
    rw [integralPathSimplex_apply, Path.extend_trans_of_le_half p q (by linarith)]
    convert p.extend_apply (stdSimplexHomeomorphUnitInterval t).property using 1
    congr 1
    change 2 * (t.val 1 / 2) = t.val 1
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatenationSimplex_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatenationSimplex_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatenationSimplex_faces ``Submission.DifferentialGeometry.Topology.pathConcatenationSimplex_faces

theorem pathConcatenationSimplex_boundary (p : Path a b) (q : Path b c) :
    (integralSingularChains X).d 2 1 (integralSimplexChain 2 (pathConcatenationSimplex p q)) =
      integralPathChain q - integralPathChain (p.trans q) + integralPathChain p := by
  rw [integralSimplexChain_boundary_two, pathConcatenationSimplex_faces p q 0,
    pathConcatenationSimplex_faces p q 1, pathConcatenationSimplex_faces p q 2]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatenationSimplex_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatenationSimplex_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatenationSimplex_boundary ``Submission.DifferentialGeometry.Topology.pathConcatenationSimplex_boundary

end DifferentialGeometry.Topology
