/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homeomorph.Conjugate
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphOpen
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Manifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isPiecewiseAffineOn_conjugateMap [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph E F) (he : IsPiecewiseAffineOn e e.source)
    (hei : IsPiecewiseAffineOn e.symm e.target) {h : F → F}
    (hh : IsPiecewiseAffineOn h e.target) (hmap : _root_.Set.MapsTo h e.target e.target)
    {C : Set F} (hC : IsCompact C) (hCt : C ⊆ e.target) (hfix : _root_.Set.EqOn h id Cᶜ) :
    IsPiecewiseAffineOn (e.conjugateMap h) univ := by
  have hhe : IsPiecewiseAffineOn (h ∘ e) e.source := by
    have hc := hh.comp he
    have hdom : e.source ∩ e ⁻¹' e.target = e.source :=
      inter_eq_left.mpr (fun x hx => e.map_source hx)
    rwa [hdom] at hc
  have heh : IsPiecewiseAffineOn (e.symm ∘ h ∘ e) e.source := by
    have hc := hei.comp hhe
    have hdom : e.source ∩ (h ∘ e) ⁻¹' e.target = e.source :=
      inter_eq_left.mpr (fun x hx => hmap (e.map_source hx))
    rw [hdom] at hc
    exact hc
  have hclosed : IsClosed (e.symm '' C) :=
    (hC.image_of_continuousOn (e.continuousOn_symm.mono hCt)).isClosed
  apply isPiecewiseAffineOn_of_locally
  intro x _
  by_cases hx : x ∈ e.source
  · refine ⟨e.source, e.open_source, hx, ?_⟩
    rw [_root_.Set.univ_inter]
    exact heh.congr (fun z hz => e.conjugateMap_of_mem h hz)
  · have hxC : x ∉ e.symm '' C := by
      rintro ⟨y, hy, rfl⟩
      exact hx (e.map_target (hCt hy))
    refine ⟨(e.symm '' C)ᶜ, hclosed.isOpen_compl, hxC, ?_⟩
    rw [_root_.Set.univ_inter]
    exact (isPiecewiseAffineOn_id hclosed.isOpen_compl).congr (e.conjugateMap_eqOn_compl hfix)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_conjugateMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_conjugateMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_conjugateMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_conjugateMap

theorem isPLHomeomorphOn_conjugateHomeomorph [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph E E) (he : IsPiecewiseAffineOn e e.source)
    (h : E ≃ₜ E) (hh : IsPiecewiseAffineOn h _root_.Set.univ)
    {C : Set E} (hC : IsCompact C) (hCt : C ⊆ e.target) (hfix : _root_.Set.EqOn h id Cᶜ) :
    IsPLHomeomorphOn (e.conjugateHomeomorph h hC hCt hfix) _root_.Set.univ univ := by
  have hmap : _root_.Set.MapsTo h e.target e.target := by
    intro y hy
    by_contra hnot
    have hyC : h y ∉ C := fun hhy => hnot (hCt hhy)
    have heq : h y = y := h.injective (hfix hyC)
    exact hnot (by rwa [heq])
  have hpl : IsPiecewiseAffineOn (e.conjugateMap h) univ :=
    isPiecewiseAffineOn_conjugateMap e he he.symm
      (hh.mono e.open_target (_root_.Set.subset_univ _)) hmap hC hCt hfix
  exact isPLHomeomorphOn_openPartialHomeomorph
    (e.conjugateHomeomorph h hC hCt hfix).toOpenPartialHomeomorph hpl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_conjugateHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_conjugateHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_conjugateHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_conjugateHomeomorph

theorem isPL_conjugateHomeomorph {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ (plGroupoid n).maximalAtlas X)
    (h : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    (hh : IsPiecewiseAffineOn h _root_.Set.univ) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsCompact C) (hCt : C ⊆ e.target) (hfix : _root_.Set.EqOn h id Cᶜ) :
    IsPL n n (e.conjugateHomeomorph h hC hCt hfix) := by
  let g := e.conjugateHomeomorph h hC hCt hfix
  have hmap : _root_.Set.MapsTo h e.target e.target := by
    intro y hy
    by_contra hnot
    have hyC : h y ∉ C := fun hhy => hnot (hCt hhy)
    have heq : h y = y := h.injective (hfix hyC)
    exact hnot (by rwa [heq])
  have hgsource : _root_.Set.MapsTo g e.source e.source := by
    intro x hx
    rw [show g x = e.conjugateMap h x from rfl, e.conjugateMap_of_mem h hx]
    exact e.map_target (hmap (e.map_source hx))
  have hcoord : _root_.Set.EqOn (e ∘ g ∘ e.symm) h e.target := by
    intro z hz
    change e (g (e.symm z)) = h z
    rw [show g (e.symm z) = e.conjugateMap h (e.symm z) from rfl,
      e.conjugateMap_of_mem h (e.map_target hz), e.right_inv hz, e.right_inv (hmap hz)]
  have hclosed : IsClosed (e.symm '' C) :=
    (hC.image_of_continuousOn (e.continuousOn_symm.mono hCt)).isClosed
  intro x
  by_cases hx : x ∈ e.source
  · apply (isPLAt_iff_of_mem_maximalAtlas he hx he (hgsource hx)).mpr
    refine ⟨g.continuous.continuousAt, ?_⟩
    have hneigh : e.target ∈ 𝓝 (e x) := e.open_target.mem_nhds (e.map_source hx)
    have hlocal := (hh (e x) (_root_.Set.mem_univ _)).inter_of_mem_nhds hneigh
    exact (hlocal.congr (fun z hz => hcoord hz.2)).of_inter_of_mem_nhds hneigh
  · have hxC : x ∉ e.symm '' C := by
      rintro ⟨y, hy, rfl⟩
      exact hx (e.map_target (hCt hy))
    apply piecewiseAffineProperty_localInvariantProp.liftPropAt_congr_of_eventuallyEq
      (isPL_id (M := X) x)
    filter_upwards [hclosed.isOpen_compl.mem_nhds hxC] with z hz
    exact e.conjugateMap_eqOn_compl hfix hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPL_conjugateHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPL_conjugateHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPL_conjugateHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPL_conjugateHomeomorph

end DifferentialGeometry.Topology.PiecewiseLinear
