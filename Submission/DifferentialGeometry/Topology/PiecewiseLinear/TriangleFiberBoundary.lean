/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TriangleFiber

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem snd_eq_endpoint_of_mem_triangle_fiber_boundary
    {b : ℝ × ℝ → ℝ} {r t : ℝ}
    (hh : ∀ y ∈ _root_.Set.Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (_root_.Set.Icc 0 (1 - y)))
    (hl : StrictMonoOn (fun y => b (0, y)) (_root_.Set.Icc (0 : ℝ) 1))
    (hr : StrictAntiOn (fun y => b (1 - y, y)) (_root_.Set.Icc (0 : ℝ) 1))
    (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1)
    (hbij : _root_.Set.BijOn Prod.snd
      {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r} (_root_.Set.Icc 0 t))
    {z : ℝ × ℝ} (hz : (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r)
    (hbd : z.1 = 0 ∨ z.2 = 0 ∨ z.1 + z.2 = 1) : z.2 = 0 ∨ z.2 = t := by
  obtain ⟨w, hw, hwt⟩ := hbij.surjOn (show t ∈ _root_.Set.Icc 0 t from ⟨ht.1, le_rfl⟩)
  have hy : z.2 ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨hz.1.2.1, by linarith [hz.1.1, hz.1.2.2]⟩
  have hyt : z.2 ≤ t := (hbij.mapsTo hz).2
  have hw₁ : w.1 ∈ _root_.Set.Icc 0 (1 - t) := by
    change w.2 = t at hwt
    exact ⟨hw.1.1, by linarith [hw.1.2.2]⟩
  have hbw : b (w.1, t) = r := by
    change w.2 = t at hwt
    simpa only [← hwt] using hw.2
  have hlo : b (0, t) ≤ r :=
    ((hh t ht).monotoneOn ⟨le_rfl, by linarith [ht.2]⟩ hw₁ hw₁.1).trans_eq hbw
  have hhi : r ≤ b (1 - t, t) :=
    hbw.symm.trans_le ((hh t ht).monotoneOn hw₁ ⟨by linarith [ht.2], le_rfl⟩ hw₁.2)
  rcases hbd with hx | hy0 | hxy
  · right
    apply le_antisymm hyt
    apply le_of_not_gt
    intro hlt
    have h := hl hy ht hlt
    have heq : b (0, z.2) = r := by simpa only [← hx] using hz.2
    linarith
  · exact Or.inl hy0
  · right
    apply le_antisymm hyt
    apply le_of_not_gt
    intro hlt
    have h := hr hy ht hlt
    have hx : 1 - z.2 = z.1 := by linarith
    have heq : b (1 - z.2, z.2) = r := by simpa only [hx] using hz.2
    linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.snd_eq_endpoint_of_mem_triangle_fiber_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.snd_eq_endpoint_of_mem_triangle_fiber_boundary target :: scope.openDecls } }

theorem exists_isPLHomeomorphOn_snd_triangle_fiber_with_boundary
    {b : ℝ × ℝ → ℝ} {r : ℝ}
    (hb : IsPiecewiseAffineOn b {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (hh : ∀ y ∈ _root_.Set.Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (_root_.Set.Icc 0 (1 - y)))
    (hl : StrictMonoOn (fun y => b (0, y)) (_root_.Set.Icc (0 : ℝ) 1))
    (hr : StrictAntiOn (fun y => b (1 - y, y)) (_root_.Set.Icc (0 : ℝ) 1))
    (h₀ : b (0, 0) < r) (h₁ : r < b (1, 0)) :
    ∃ t ∈ _root_.Set.Ioc (0 : ℝ) 1, IsPLHomeomorphOn Prod.snd
      {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r} (_root_.Set.Icc 0 t) ∧
      ∀ z, (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) → b z = r →
        (z.1 = 0 ∨ z.2 = 0 ∨ z.1 + z.2 = 1 ↔ z.2 = 0 ∨ z.2 = t) := by
  obtain ⟨t, ht, hPL⟩ := exists_isPLHomeomorphOn_snd_triangle_fiber hb hh hl hr h₀ h₁
  have hforward : ∀ {z : ℝ × ℝ},
      ((0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r) →
      (z.1 = 0 ∨ z.2 = 0 ∨ z.1 + z.2 = 1) → z.2 = 0 ∨ z.2 = t :=
    snd_eq_endpoint_of_mem_triangle_fiber_boundary hh hl hr
    ⟨ht.1.le, ht.2⟩ hPL.bijOn
  have hend : ∃ z : ℝ × ℝ, (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r ∧
      z.2 = t ∧ (z.1 = 0 ∨ z.1 + z.2 = 1) := by
    by_cases hmid : r ≤ b (0, 1)
    · obtain ⟨u, hu, hbu, -⟩ := exists_bijOn_snd_triangle_fiber_of_monotone
        hb.continuousOn hh hl hr.antitoneOn h₀ hmid
      have hz : 0 ≤ (0 : ℝ) ∧ 0 ≤ u ∧ 0 + u ≤ 1 := ⟨le_rfl, hu.1.le, by simpa using hu.2⟩
      have hut : u = t := (hforward ⟨hz, hbu⟩ (Or.inl rfl)).resolve_left hu.1.ne'
      exact ⟨(0, u), hz, hbu, hut, Or.inl rfl⟩
    · have hcont : ContinuousOn (fun y => b (1 - y, y)) (_root_.Set.Icc (0 : ℝ) 1) := by
        apply hb.continuousOn.comp (by fun_prop : Continuous (fun y : ℝ => (1 - y, y))).continuousOn
        intro y hy
        change 0 ≤ 1 - y ∧ 0 ≤ y ∧ 1 - y + y ≤ 1
        exact ⟨by linarith [hy.2], hy.1, by linarith⟩
      obtain ⟨u, hu, hbu⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont
        (show r ∈ _root_.Set.Icc (b (1 - 1, 1)) (b (1 - 0, 0)) from by
          simpa using And.intro (le_of_not_ge hmid) h₁.le)
      have hupos : 0 < u := lt_of_le_of_ne hu.1 fun hu0 => by
        subst u
        simp only [sub_zero] at hbu
        exact h₁.ne hbu.symm
      have hz : 0 ≤ 1 - u ∧ 0 ≤ u ∧ 1 - u + u ≤ 1 :=
        ⟨by linarith [hu.2], hu.1, by linarith⟩
      have hut : u = t := (hforward ⟨hz, hbu⟩ (Or.inr (Or.inr (by ring)))).resolve_left hupos.ne'
      exact ⟨(1 - u, u), hz, hbu, hut, Or.inr (by ring)⟩
  obtain ⟨w, hw, hbw, hwt, hwbd⟩ := hend
  refine ⟨t, ht, hPL, fun z hz hbz => ⟨hforward ⟨hz, hbz⟩, ?_⟩⟩
  rintro (hz0 | hzt)
  · exact Or.inr (Or.inl hz0)
  · have hzw : z = w := hPL.bijOn.injOn ⟨hz, hbz⟩ ⟨hw, hbw⟩ (hzt.trans hwt.symm)
    rw [hzw]
    exact hwbd.imp_right Or.inr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_snd_triangle_fiber_with_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_snd_triangle_fiber_with_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_snd_triangle_fiber_with_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_snd_triangle_fiber_with_boundary

theorem triangle_fiber_bounds_of_monotone {b : ℝ × ℝ → ℝ}
    (hh : ∀ y ∈ _root_.Set.Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (_root_.Set.Icc 0 (1 - y)))
    (hl : StrictMonoOn (fun y => b (0, y)) (_root_.Set.Icc (0 : ℝ) 1))
    (hr : StrictAntiOn (fun y => b (1 - y, y)) (_root_.Set.Icc (0 : ℝ) 1))
    {z : ℝ × ℝ} (hz : 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) :
    b (0, 0) ≤ b z ∧ b z ≤ b (1, 0) ∧
      (b z = b (0, 0) ↔ z = (0, 0)) ∧ (b z = b (1, 0) ↔ z = (1, 0)) := by
  have hy : z.2 ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨hz.2.1, by linarith [hz.1, hz.2.2]⟩
  have hx : z.1 ∈ _root_.Set.Icc 0 (1 - z.2) := ⟨hz.1, by linarith [hz.2.2]⟩
  have hz₀ : (0 : ℝ) ∈ _root_.Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hleft := hl.monotoneOn hz₀ hy hy.1
  have hleft' := (hh z.2 hy).monotoneOn ⟨le_rfl, by linarith [hy.2]⟩ hx hx.1
  have hright := hr.antitoneOn hz₀ hy hy.1
  have hright' := (hh z.2 hy).monotoneOn hx ⟨by linarith [hy.2], le_rfl⟩ hx.2
  simp only [sub_zero] at hright
  refine ⟨hleft.trans hleft', hright'.trans hright, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hbz
    change b (z.1, z.2) = _ at hbz
    have hy0 : z.2 = 0 := hl.injOn hy hz₀ (le_antisymm (hleft'.trans_eq hbz) hleft)
    have hx0 : z.1 = 0 := (hh z.2 hy).injOn hx ⟨le_rfl, by linarith [hy.2]⟩ (by
      simpa only [hy0] using hbz)
    exact Prod.ext hx0 hy0
  · rintro rfl
    rfl
  · intro hbz
    change b (z.1, z.2) = _ at hbz
    have hy0 : z.2 = 0 := hr.injOn hy hz₀ (by
      simpa only [sub_zero] using le_antisymm hright (hbz.symm.trans_le hright'))
    have hx1 : z.1 = 1 := by
      apply (hh 0 hz₀).injOn
        (show z.1 ∈ _root_.Set.Icc 0 (1 - 0) from by simpa only [hy0] using hx)
        (show (1 : ℝ) ∈ _root_.Set.Icc 0 (1 - 0) from by norm_num)
      simpa only [hy0] using hbz
    exact Prod.ext hx1 hy0
  · rintro rfl
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_bounds_of_monotone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_bounds_of_monotone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_bounds_of_monotone ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_bounds_of_monotone

theorem exists_isPLHomeomorphOn_snd_triangle_fiber_preserving_edges
    {b : ℝ × ℝ → ℝ} {r : ℝ}
    (hb : IsPiecewiseAffineOn b {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (hh : ∀ y ∈ _root_.Set.Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (_root_.Set.Icc 0 (1 - y)))
    (hl : StrictMonoOn (fun y => b (0, y)) (_root_.Set.Icc (0 : ℝ) 1))
    (hr : StrictAntiOn (fun y => b (1 - y, y)) (_root_.Set.Icc (0 : ℝ) 1))
    (h₀ : b (0, 0) < r) (h₁ : r < b (1, 0)) :
    ∃ t ∈ _root_.Set.Ioc (0 : ℝ) 1, IsPLHomeomorphOn Prod.snd
      {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r} (_root_.Set.Icc 0 t) ∧
      ∀ z, (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) → b z = r →
        (z.1 = 0 ↔ z.2 = t ∧ r ≤ b (0, 1)) ∧
        (z.1 + z.2 = 1 ↔ z.2 = t ∧ b (0, 1) ≤ r) := by
  obtain ⟨t, ht, hPL, hbd⟩ := exists_isPLHomeomorphOn_snd_triangle_fiber_with_boundary
    hb hh hl hr h₀ h₁
  refine ⟨t, ht, hPL, fun z hz hbz => ?_⟩
  have hy : z.2 ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨hz.2.1, by linarith [hz.1, hz.2.2]⟩
  have hone : (1 : ℝ) ∈ _root_.Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hlo : b (0, z.2) ≤ b (0, 1) := hl.monotoneOn hy hone hy.2
  have hhi : b (0, 1) ≤ b (1 - z.2, z.2) := by
    simpa only [sub_self] using hr.antitoneOn hy hone hy.2
  have hleft : z.1 = 0 → z.2 = t ∧ r ≤ b (0, 1) := by
    intro hx
    have hbzy : b (0, z.2) = r := by simpa only [← hx] using hbz
    refine ⟨?_, hbzy.symm.trans_le hlo⟩
    refine ((hbd z hz hbz).mp (Or.inl hx)).resolve_left fun hy0 => ?_
    rw [hy0] at hbzy
    exact h₀.ne hbzy
  have hright : z.1 + z.2 = 1 → z.2 = t ∧ b (0, 1) ≤ r := by
    intro hxy
    have hx : 1 - z.2 = z.1 := by linarith
    have hbzy : b (1 - z.2, z.2) = r := by simpa only [hx] using hbz
    refine ⟨?_, hhi.trans_eq hbzy⟩
    refine ((hbd z hz hbz).mp (Or.inr (Or.inr hxy))).resolve_left fun hy0 => ?_
    rw [hy0, sub_zero] at hbzy
    exact h₁.ne hbzy.symm
  refine ⟨⟨hleft, ?_⟩, ⟨hright, ?_⟩⟩
  · rintro ⟨hyt, hrle⟩
    rcases (hbd z hz hbz).mpr (Or.inr hyt) with hx | hy0 | hxy
    · exact hx
    · exact False.elim (ht.1.ne (hy0.symm.trans hyt))
    · have hx : 1 - z.2 = z.1 := by linarith
      have hbzy : b (1 - z.2, z.2) = r := by simpa only [hx] using hbz
      have hy1 : z.2 = 1 := hr.injOn hy hone (by
        simpa only [sub_self] using le_antisymm (hbzy.trans_le hrle) hhi)
      linarith
  · rintro ⟨hyt, hrle⟩
    rcases (hbd z hz hbz).mpr (Or.inr hyt) with hx | hy0 | hxy
    · have hbzy : b (0, z.2) = r := by simpa only [← hx] using hbz
      have hy1 : z.2 = 1 := hl.injOn hy hone (le_antisymm hlo (hrle.trans_eq hbzy.symm))
      linarith
    · exact False.elim (ht.1.ne (hy0.symm.trans hyt))
    · exact hxy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_snd_triangle_fiber_preserving_edges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_snd_triangle_fiber_preserving_edges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_snd_triangle_fiber_preserving_edges ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_snd_triangle_fiber_preserving_edges

theorem triangle_fiber_min_eq_singleton_of_monotone {b : ℝ × ℝ → ℝ}
    (hh : ∀ y ∈ _root_.Set.Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (_root_.Set.Icc 0 (1 - y)))
    (hl : StrictMonoOn (fun y => b (0, y)) (_root_.Set.Icc (0 : ℝ) 1))
    (hr : StrictAntiOn (fun y => b (1 - y, y)) (_root_.Set.Icc (0 : ℝ) 1)) :
    {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = b (0, 0)} = {(0, 0)} := by
  ext z
  constructor
  · rintro ⟨hz, hbz⟩
    exact (triangle_fiber_bounds_of_monotone hh hl hr hz).2.2.1.mp hbz
  · rintro rfl
    norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_min_eq_singleton_of_monotone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_min_eq_singleton_of_monotone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_min_eq_singleton_of_monotone ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_min_eq_singleton_of_monotone

theorem triangle_fiber_max_eq_singleton_of_monotone {b : ℝ × ℝ → ℝ}
    (hh : ∀ y ∈ _root_.Set.Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (_root_.Set.Icc 0 (1 - y)))
    (hl : StrictMonoOn (fun y => b (0, y)) (_root_.Set.Icc (0 : ℝ) 1))
    (hr : StrictAntiOn (fun y => b (1 - y, y)) (_root_.Set.Icc (0 : ℝ) 1)) :
    {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = b (1, 0)} = {(1, 0)} := by
  ext z
  constructor
  · rintro ⟨hz, hbz⟩
    exact (triangle_fiber_bounds_of_monotone hh hl hr hz).2.2.2.mp hbz
  · rintro rfl
    norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_max_eq_singleton_of_monotone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_max_eq_singleton_of_monotone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_max_eq_singleton_of_monotone ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_max_eq_singleton_of_monotone

theorem triangle_fiber_eq_empty_of_notMem_Icc {b : ℝ × ℝ → ℝ} {r : ℝ}
    (hh : ∀ y ∈ _root_.Set.Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (_root_.Set.Icc 0 (1 - y)))
    (hl : StrictMonoOn (fun y => b (0, y)) (_root_.Set.Icc (0 : ℝ) 1))
    (hr : StrictAntiOn (fun y => b (1 - y, y)) (_root_.Set.Icc (0 : ℝ) 1))
    (hrange : r ∉ _root_.Set.Icc (b (0, 0)) (b (1, 0))) :
    {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro z ⟨hz, hbz⟩
  have hbound := triangle_fiber_bounds_of_monotone hh hl hr hz
  exact hrange ⟨hbound.1.trans_eq hbz, hbz.symm.trans_le hbound.2.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_eq_empty_of_notMem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_eq_empty_of_notMem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_eq_empty_of_notMem_Icc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangle_fiber_eq_empty_of_notMem_Icc

end DifferentialGeometry.Topology.PiecewiseLinear
