/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPiece

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_union
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P Q : Set E} {P' Q' : Set F} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) {f g : E → F}
    (hf : IsPLHomeomorphOn f P P') (hg : IsPLHomeomorphOn g Q Q')
    (hfg : _root_.Set.EqOn f g (P ∩ Q)) (hinter : _root_.Set.SurjOn f (P ∩ Q) (P' ∩ Q')) :
    ∃ h : E → F, IsPLHomeomorphOn h (P ∪ Q) (P' ∪ Q') ∧ _root_.Set.EqOn h f P ∧ _root_.Set.EqOn h g Q := by
  classical
  let h := P.piecewise f g
  have hPf : _root_.Set.EqOn h f P := fun _ hx => _root_.Set.piecewise_eq_of_mem P f g hx
  have hQg : _root_.Set.EqOn h g Q := by
    intro x hxQ
    by_cases hxP : x ∈ P
    · exact (hPf hxP).trans (hfg ⟨hxP, hxQ⟩)
    · exact _root_.Set.piecewise_eq_of_notMem P f g hxP
  have hcross {x y : E} (hx : x ∈ P) (hy : y ∈ Q) (hxy : f x = g y) : x = y := by
    obtain ⟨z, hz, hzx⟩ := hinter ⟨hf.bijOn.mapsTo hx, hxy.symm ▸ hg.bijOn.mapsTo hy⟩
    have hzx' : z = x := hf.bijOn.injOn hz.1 hx hzx
    have hzy : g z = g y := (hfg hz).symm.trans (hzx.trans hxy)
    exact hzx'.symm.trans (hg.bijOn.injOn hz.2 hy hzy)
  have hinj : _root_.Set.InjOn h (P ∪ Q) := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hPf hx, hPf hy] at hxy
      exact hf.bijOn.injOn hx hy hxy
    · rw [hPf hx, hQg hy] at hxy
      exact hcross hx hy hxy
    · rw [hQg hx, hPf hy] at hxy
      exact (hcross hy hx hxy.symm).symm
    · rw [hQg hx, hQg hy] at hxy
      exact hg.bijOn.injOn hx hy hxy
  have hbij : _root_.Set.BijOn h (P ∪ Q) (P' ∪ Q') := by
    refine ⟨?_, hinj, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · rw [hPf hx]
        exact Or.inl (hf.bijOn.mapsTo hx)
      · rw [hQg hx]
        exact Or.inr (hg.bijOn.mapsTo hx)
    · intro y hy
      rcases hy with hy | hy
      · obtain ⟨x, hx, hxy⟩ := hf.bijOn.surjOn hy
        exact ⟨x, Or.inl hx, (hPf hx).trans hxy⟩
      · obtain ⟨x, hx, hxy⟩ := hg.bijOn.surjOn hy
        exact ⟨x, Or.inr hx, (hQg hx).trans hxy⟩
  have hpl : IsPiecewiseAffineOn h (P ∪ Q) :=
    (hf.isPiecewiseAffineOn.congr hPf).union_of_isClosed (hg.isPiecewiseAffineOn.congr hQg)
      hP.isCompact.isClosed hQ.isCompact.isClosed
  obtain ⟨K, hfinite, hspace⟩ := (hP.union hQ).exists_simplicialComplex
  let _ : Finite K.faces := hfinite.to_subtype
  have hplK : IsPiecewiseAffineOn h K.space := by rwa [hspace]
  have hinjK : _root_.Set.InjOn h K.space := by rwa [hspace]
  obtain ⟨L, _, hL, hh⟩ := exists_isPLHomeomorphOn_image K hplK hinjK
  rw [hspace] at hh hL
  rw [hL, hbij.image_eq] at hh
  exact ⟨h, hh, hPf, hQg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_union

theorem exists_isPLHomeomorphOn_union_of_eqOn_inter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P Q : Set E} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) {f g : E → E}
    (hf : IsPLHomeomorphOn f P P) (hg : IsPLHomeomorphOn g Q Q)
    (hfg : _root_.Set.EqOn f g (P ∩ Q)) (hinter : _root_.Set.SurjOn f (P ∩ Q) (P ∩ Q)) :
    ∃ h : E → E, IsPLHomeomorphOn h (P ∪ Q) (P ∪ Q) ∧ _root_.Set.EqOn h f P ∧ _root_.Set.EqOn h g Q :=
  exists_isPLHomeomorphOn_union hP hQ hf hg hfg hinter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_union_of_eqOn_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_union_of_eqOn_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_union_of_eqOn_inter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_union_of_eqOn_inter

end DifferentialGeometry.Topology.PiecewiseLinear
