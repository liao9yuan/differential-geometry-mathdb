/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
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
theorem IsConeBase.boundaryComplex_space_of_isPLSphere {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {p : E}
    (hp : IsConeBase p K) (hK : IsPLSphere n K.space) :
    (boundaryComplex (n + 1) (coneComplex hp)).space = K.space := by
  let _ : Finite (coneComplex hp).faces :=
    (coneComplex_faces_finite hp (Set.toFinite K.faces)).to_subtype
  obtain ⟨f, hf⟩ := hK
  let S := simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)
  let _ : Finite S.faces := (simplexBoundary_faces_finite _ _).to_subtype
  have hfS : IsPLHomeomorphOn f S.space K.space := by
    change IsPLHomeomorphOn f
      (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space K.space
    rwa [simplexBoundary_stdVertices_space]
  obtain ⟨g, hg, hgf, -, -⟩ := exists_isPLHomeomorphOn_coneComplex (isConeBase_std n) hp hfS
  rw [coneComplex_std_space] at hg
  have himg : g '' stdSimplexBoundary (n + 1) = K.space := by
    rw [← simplexBoundary_stdVertices_space]
    exact hgf.image_eq.trans hfS.image_eq
  exact (hg.image_stdSimplexBoundary_eq_boundaryComplex (coneComplex hp) rfl).symm.trans himg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.boundaryComplex_space_of_isPLSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.boundaryComplex_space_of_isPLSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.boundaryComplex_space_of_isPLSphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.boundaryComplex_space_of_isPLSphere

end DifferentialGeometry.Topology.PiecewiseLinear
