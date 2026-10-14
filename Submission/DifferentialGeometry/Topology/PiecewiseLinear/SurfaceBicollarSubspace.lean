/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BicollarEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCombinatorialManifold.isBicollared_preimage_open
    (L : Geometry.SimplicialComplex ℝ E3) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hconn : IsConnected L.space)
    {U : Set E3} (hU : IsOpen U) (hLU : L.space ⊆ U) :
    IsBicollared (((↑) : U → E3) ⁻¹' L.space) := by
  classical
  have hpoly : IsPolyhedralManifold (n := 3) 2 L.space := by
    have hLt : L.space ⊆ (chartAt E3 (0 : E3)).target := by
      rw [chartAt_self_eq]
      exact _root_.Set.subset_univ _
    have h : IsPolyhedralManifold (n := 3) 2 ((chartAt E3 (0 : E3)).symm '' L.space) :=
      ⟨⟨3, chartPieceOfComplex _ (chart_mem_atlas _ _) L hLt⟩, hL⟩
    simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, _root_.Set.image_id] using h
  obtain ⟨a, ha⟩ := hconn.nonempty
  let f : E3 → U := fun x => if hx : x ∈ U then ⟨x, hx⟩ else ⟨a, hLU ha⟩
  have hfix (x : U) : f x = x := by
    dsimp only [f]
    rw [dif_pos x.property]
  have hf : _root_.Topology.IsOpenEmbedding (fun x : U => f x) := by
    have heq : (fun x : U => f x) = id := funext hfix
    rw [heq]
    exact IsOpenEmbedding.id
  have hnear : U ∈ 𝓝ˢ L.space :=
    subset_interior_iff_mem_nhdsSet.mp (hU.interior_eq.symm ▸ hLU)
  have hbi := hpoly.isBicollared_image (hpoly.isTwoSided hconn) hnear hf
  have himage : f '' L.space = ((↑) : U → E3) ⁻¹' L.space := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (f y : E3) ∈ L.space
      simpa only [f, dif_pos (hLU hy)] using hy
    · intro hx
      exact ⟨(x : E3), hx, hfix x⟩
  exact himage ▸ hbi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isBicollared_preimage_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isBicollared_preimage_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isBicollared_preimage_open ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isBicollared_preimage_open

end DifferentialGeometry.Topology.PiecewiseLinear
