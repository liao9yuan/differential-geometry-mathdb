/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskPair
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open _root_.Classical in
theorem exists_isPLHomeomorphOn_prism_map_ends
    {P : Set E} (hP : IsPLBall 2 P) {a b : ℝ} (hab : a < b)
    (K : Geometry.SimplicialComplex ℝ F) [Finite K.faces] (hK : IsPLBall 3 K.space)
    {D₀ D₁ : Set F} (hD₀K : D₀ ⊆ (boundaryComplex 3 K).space)
    (hD₁ : IsPLBall 2 D₁) (hD₁K : D₁ ⊆ (boundaryComplex 3 K).space)
    (hdis : Disjoint D₀ D₁) {g : E → F} (hg : IsPLHomeomorphOn g P D₀) :
    ∃ G : E × ℝ → F, IsPLHomeomorphOn G (P ×ˢ _root_.Set.Icc a b) K.space ∧
      (∀ x ∈ P, G (x, a) = g x) ∧ G '' (P ×ˢ {b}) = D₁ := by
  let _ : DecidableEq F := Classical.decEq _
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  obtain ⟨L, hLfin, hLspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall 2 L.space := hLspace.symm ▸ hP
  have hprod := isPLBall_three_prod hP (isPLBall_Icc hab)
  obtain ⟨R, hRfin, hRspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hR : IsPLBall 3 R.space := hRspace.symm ▸ hprod
  have hboundary := boundaryComplex_space_prism L hL hab R (hLspace.symm ▸ hRspace)
  rw [hLspace] at hboundary
  have hleft : P ×ˢ {a} ⊆ (boundaryComplex 3 R).space := by
    rw [hboundary]
    rintro x ⟨hx, hxa⟩
    exact Or.inl ⟨hx, Or.inl hxa⟩
  have hright : P ×ˢ {b} ⊆ (boundaryComplex 3 R).space := by
    rw [hboundary]
    rintro x ⟨hx, hxb⟩
    exact Or.inl ⟨hx, Or.inr hxb⟩
  have hends : Disjoint (P ×ˢ {a}) (P ×ˢ {b}) :=
    disjoint_left.mpr fun _ hx hy => hab.ne (hx.2.symm.trans hy.2)
  have hg' := (hP.isPolyhedron.isPLHomeomorphOn_fst_prod_const a).trans hg
  obtain ⟨G, hG, hGg, hGb⟩ := exists_isPLHomeomorphOn_map_disk_pair_of_boundaryComplex R K hR hK
    (hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const a)) hleft
    (hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const b)) hright
    hends hD₁ hD₁K hdis hg' hD₀K
  rw [hRspace] at hG
  exact ⟨G, hG, fun x hx => hGg ⟨hx, rfl⟩, hGb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_map_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_map_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_map_ends ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_map_ends

end DifferentialGeometry.Topology.PiecewiseLinear
