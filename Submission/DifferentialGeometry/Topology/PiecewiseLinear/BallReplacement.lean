/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLHomeomorphOn.isPLSphere_image_stdSimplexBoundary {n : ℕ} {P : Set E}
    {f : (Fin (n + 2) → ℝ) → E}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P) :
    IsPLSphere n (f '' stdSimplexBoundary (n + 1)) := by
  classical
  let B := simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)
  let _ : Finite B.faces := (simplexBoundary_faces_finite _ _).to_subtype
  have h := (isPLSphere_simplexBoundary_std n).of_isPLHomeomorphOn
    (hf.restrict (isPolyhedron_space B) (simplexBoundary_stdVertices_space_subset n))
  rwa [simplexBoundary_stdVertices_space] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPLSphere_image_stdSimplexBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPLSphere_image_stdSimplexBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPLSphere_image_stdSimplexBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPLSphere_image_stdSimplexBoundary

theorem exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary {n : ℕ} {P : Set E} {Q : Set F}
    {f : (Fin (n + 2) → ℝ) → E} {g : (Fin (n + 2) → ℝ) → F}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P)
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin (n + 2))) Q) {b : E → F}
    (hb : IsPLHomeomorphOn b (f '' stdSimplexBoundary (n + 1)) (g '' stdSimplexBoundary (n + 1))) :
    ∃ H : E → F, IsPLHomeomorphOn H P Q ∧ _root_.Set.EqOn H b (f '' stdSimplexBoundary (n + 1)) := by
  classical
  have hP : IsPLBall (n + 1) P := ⟨f, hf⟩
  have hQ : IsPLBall (n + 1) Q := ⟨g, hg⟩
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLQ⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hfK : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) K.space := hKP.symm ▸ hf
  have hgL : IsPLHomeomorphOn g (stdSimplex ℝ (Fin (n + 2))) L.space := hLQ.symm ▸ hg
  have hKboundary := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hfK
  have hLboundary := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L hgL
  rw [simplexBoundary_stdVertices_space] at hKboundary hLboundary
  have hbKL : IsPLHomeomorphOn b (boundaryComplex (n + 1) K).space (boundaryComplex (n + 1) L).space
      := by
    rwa [hKboundary, hLboundary]
  obtain ⟨H, hH, hHb⟩ := exists_isPLHomeomorphOn_of_boundaryComplex K L
    (⟨f, hfK⟩ : IsPLBall (n + 1) K.space) (⟨g, hgL⟩ : IsPLBall (n + 1) L.space) hbKL
  rw [hKP, hLQ] at hH
  rw [hKboundary] at hHb
  exact ⟨H, hH, hHb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary

theorem exists_isPLHomeomorphOn_replace_ball {n : ℕ} {P Q R J : Set E}
    (hP : IsPolyhedron P) {f g : (Fin (n + 2) → ℝ) → E}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) Q)
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin (n + 2))) R)
    (hfJ : f '' stdSimplexBoundary (n + 1) = J) (hgJ : g '' stdSimplexBoundary (n + 1) = J)
    (hPQ : P ∩ Q = J) (hPR : P ∩ R = J) :
    ∃ H : E → E, IsPLHomeomorphOn H (P ∪ Q) (P ∪ R) ∧ _root_.Set.EqOn H id P := by
  have hQ : IsPLBall (n + 1) Q := ⟨f, hf⟩
  have hJ : IsPolyhedron J := hPQ ▸ hP.inter hQ.isPolyhedron
  have hJid : IsPLHomeomorphOn (id : E → E)
      (f '' stdSimplexBoundary (n + 1)) (g '' stdSimplexBoundary (n + 1)) := by
    rw [hfJ, hgJ]
    exact hJ.isPLHomeomorphOn_id
  obtain ⟨G, hG, hGJ⟩ := exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary hf hg hJid
  rw [hfJ] at hGJ
  have hfg : _root_.Set.EqOn id G (P ∩ Q) := by
    rw [hPQ]
    exact hGJ.symm
  have hinter : _root_.Set.SurjOn (id : E → E) (P ∩ Q) (P ∩ R) := by
    rw [hPQ, hPR]
    exact _root_.Set.surjOn_id J
  obtain ⟨H, hH, hHP, -⟩ := exists_isPLHomeomorphOn_union hP hQ.isPolyhedron
    hP.isPLHomeomorphOn_id hG hfg hinter
  exact ⟨H, hH, hHP⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_replace_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_replace_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_replace_ball ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_replace_ball

end DifferentialGeometry.Topology.PiecewiseLinear
