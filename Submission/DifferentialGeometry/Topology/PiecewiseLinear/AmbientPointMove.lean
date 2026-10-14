/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.AmbientExtension
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplexComplex
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Connected.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_small_point_move {U : Set E} (hU : IsOpen U)
    {p : E} (hp : p ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : E, _root_.Dist.dist q p < δ →
      ∃ h : E ≃ₜ E, IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ ∧ _root_.Set.EqOn h id Uᶜ ∧ h p = q := by
  classical
  let T : Finset E := {p}
  have hT : AffineIndependent ℝ ((↑) : T → E) := affineIndependent_of_subsingleton ℝ _
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hK : K.space = {p} := by
    rw [simplexComplex_space T hT (Finset.singleton_nonempty p)]
    simp [T]
  have hpK : {p} ∈ K.faces := ⟨Finset.singleton_nonempty p, subset_rfl⟩
  obtain ⟨N, hN, hpN, hNU⟩ := exists_isPolyhedron_neighborhood isCompact_singleton hU
    (singleton_subset_iff.mpr hp)
  have hstar : openStar K p ⊆ interior N := by
    rw [← hK] at hpN
    exact (openStar_subset_space K p).trans hpN
  obtain ⟨δ, hδ, hmove⟩ := exists_isPLHomeomorphOn_of_small_vertex_move K p hN hstar
  refine ⟨δ, hδ, fun q hq => ?_⟩
  obtain ⟨h, hh, hfix, hmap⟩ := hmove q hq
  refine ⟨h, hh, hfix.mono (compl_subset_compl.mpr hNU), ?_⟩
  rw [hmap (hK.symm ▸ _root_.Set.mem_singleton p), simplicialMap_vertex K _ hpK, Function.update_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_small_point_move then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_small_point_move"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_small_point_move ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_small_point_move

theorem exists_isPLHomeomorphOn_map_point_eqOn_compl {U : Set E}
    (hU : IsOpen U) (hc : IsPreconnected U) {p q : E} (hp : p ∈ U) (hq : q ∈ U) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ ∧ _root_.Set.EqOn h id Uᶜ ∧ h p = q := by
  classical
  let A : Set E := {x | x ∈ U ∧ ∃ h : E ≃ₜ E,
    IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ ∧ _root_.Set.EqOn h id Uᶜ ∧ h p = x}
  have hsymm {h : E ≃ₜ E} (hh : IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ) :
      IsPLHomeomorphOn h.symm _root_.Set.univ univ := by
    apply hh.symm.congr
    intro x hx
    exact h.injective ((h.apply_symm_apply x).trans (hh.bijOn.invOn_invFunOn.2 hx).symm)
  have hfixsymm {h : E ≃ₜ E} (hh : _root_.Set.EqOn h id Uᶜ) : _root_.Set.EqOn h.symm id Uᶜ := by
    intro x hx
    exact h.symm_apply_eq.mpr (hh hx).symm
  have hlocal (x : E) (hx : x ∈ U) :
      ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∀ y ∈ V, ∃ h : E ≃ₜ E,
          IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ ∧ _root_.Set.EqOn h id Uᶜ ∧ h x = y := by
    obtain ⟨δ, hδ, hmove⟩ := exists_isPLHomeomorphOn_small_point_move hU hx
    exact ⟨Metric.ball x δ ∩ U, Metric.isOpen_ball.inter hU,
      ⟨Metric.mem_ball_self hδ, hx⟩, _root_.Set.inter_subset_right, fun y hy => hmove y hy.1⟩
  have hA : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨hxU, h, hh, hfix, hpx⟩
    obtain ⟨V, hV, hxV, hVU, hmove⟩ := hlocal x hxU
    apply Filter.mem_of_superset (hV.mem_nhds hxV)
    intro y hy
    obtain ⟨g, hg, hgfix, hxy⟩ := hmove y hy
    refine ⟨hVU hy, h.trans g, hh.trans hg, ?_, ?_⟩
    · intro z hz
      change g (h z) = z
      exact (congrArg g (hfix hz)).trans (hgfix hz)
    · change g (h p) = y
      rw [hpx, hxy]
  have hB : IsOpen (U \ A) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨hxU, hxA⟩
    obtain ⟨V, hV, hxV, hVU, hmove⟩ := hlocal x hxU
    apply Filter.mem_of_superset (hV.mem_nhds hxV)
    intro y hy
    refine ⟨hVU hy, ?_⟩
    rintro ⟨_, h, hh, hfix, hpy⟩
    obtain ⟨g, hg, hgfix, hxy⟩ := hmove y hy
    apply hxA
    refine ⟨hxU, h.trans g.symm, hh.trans (hsymm hg), ?_, ?_⟩
    · intro z hz
      change g.symm (h z) = z
      exact (congrArg g.symm (hfix hz)).trans (hfixsymm hgfix hz)
    · change g.symm (h p) = x
      rw [hpy, ← hxy, g.symm_apply_apply]
  have hpA : p ∈ A := by
    refine ⟨hp, Homeomorph.refl E, ?_, fun _ _ => rfl, rfl⟩
    exact ⟨bijOn_id _root_.Set.univ, isPiecewiseAffineOn_id isOpen_univ,
      (isPiecewiseAffineOn_id isOpen_univ).congr
        (fun _ hx => (_root_.Set.bijOn_id _root_.Set.univ).invOn_invFunOn.1 hx)⟩
  have hUA : U ⊆ A := hc.subset_left_of_subset_union hA hB _root_.Set.disjoint_sdiff_right
    (fun x hx => by
      by_cases h : x ∈ A
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩)
    ⟨p, hp, hpA⟩
  exact (hUA hq).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_map_point_eqOn_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_map_point_eqOn_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_map_point_eqOn_compl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_map_point_eqOn_compl

open _root_.Classical in
theorem exists_isPLHomeomorphOn_moves_point_dist_lt [Nontrivial E]
    {p : E} {ε : ℝ} (hε : 0 < ε) :
    ∃ h : E ≃ₜ E,
      IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ ∧ h p ≠ p ∧
      EqOn h id (Metric.ball p (ε / 4))ᶜ ∧ ∀ x, _root_.Dist.dist (h x) x < ε := by
  let r := ε / 4
  have hr : 0 < r := by positivity
  obtain ⟨η, hη, hmove⟩ :=
    exists_isPLHomeomorphOn_small_point_move
      (U := Metric.ball p r) (p := p) Metric.isOpen_ball
      (Metric.mem_ball_self hr)
  let s := _root_.Min.min η r / 2
  have hs : 0 < s := div_pos (lt_min hη hr) (by norm_num)
  have hsη : s < η :=
    (half_lt_self (lt_min hη hr)).trans_le (min_le_left η r)
  obtain ⟨q, hq⟩ :=
    (NormedSpace.sphere_nonempty (E := E) (x := p) (r := s)).mpr hs.le
  have hqdist : _root_.Dist.dist q p = s := Metric.mem_sphere.mp hq
  have hqp : q ≠ p := by
    intro h
    subst q
    have : (0 : ℝ) = s := by simpa using hqdist
    linarith
  obtain ⟨h, hh, hfix, hpq⟩ := hmove q (by simpa [hqdist] using hsη)
  have hmaps : _root_.Set.MapsTo h (Metric.ball p r) (Metric.ball p r) := by
    intro x hx
    by_contra hnot
    have hfixed : h (h x) = h x := hfix hnot
    have heq : h x = x := h.injective hfixed
    exact hnot (heq.symm ▸ hx)
  refine ⟨h, hh, ?_, ?_, ?_⟩
  · exact hpq.symm ▸ hqp
  · simpa [r] using hfix
  · intro x
    by_cases hx : x ∈ Metric.ball p r
    · have hhx := hmaps hx
      calc
        dist (h x) x ≤ _root_.Dist.dist (h x) p + _root_.Dist.dist p x := dist_triangle _ _ _
        _ < r + r := add_lt_add hhx
          (by simpa only [Metric.mem_ball, dist_comm] using hx)
        _ = ε / 2 := by simp [r]; ring
        _ < ε := half_lt_self hε
    · simpa [hfix hx] using hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_moves_point_dist_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_moves_point_dist_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_moves_point_dist_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_moves_point_dist_lt

open _root_.Classical in
theorem exists_isPLHomeomorphOn_moves_point_dist_lt_eqOn [Nontrivial E]
    {F U : Set E} (hF : IsClosed F) (hU : IsOpen U) {p : E}
    (hpU : p ∈ U) (hpF : p ∉ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball p r ⊆ U \ F ∧
      ∃ h : E ≃ₜ E,
        IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ ∧ h p ≠ p ∧
        _root_.Set.EqOn h id (Metric.ball p r)ᶜ ∧ _root_.Set.EqOn h id F ∧ _root_.Set.EqOn h id Uᶜ ∧
        ∀ x, _root_.Dist.dist (h x) x < ε := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp (hU.sdiff hF) p ⟨hpU, hpF⟩
  let η := _root_.Min.min ε R
  have hη : 0 < η := lt_min hε hR
  obtain ⟨h, hh, hmove, hfix, hclose⟩ :=
    exists_isPLHomeomorphOn_moves_point_dist_lt (p := p) hη
  have hr : 0 < η / 4 := by positivity
  have hrR : η / 4 < R := by
    calc
      η / 4 < η := by linarith
      _ ≤ R := min_le_right ε R
  have hball : Metric.ball p (η / 4) ⊆ U \ F := by
    intro x hx
    exact hRU (Metric.mem_ball.mpr ((Metric.mem_ball.mp hx).trans hrR))
  refine ⟨η / 4, hr, hball, h, hh, hmove, hfix, ?_, ?_, ?_⟩
  · intro x hxF
    apply hfix
    intro hx
    exact (hball hx).2 hxF
  · intro x hxU
    apply hfix
    intro hx
    exact hxU (hball hx).1
  · intro x
    exact (hclose x).trans_le (min_le_left ε R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_moves_point_dist_lt_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_moves_point_dist_lt_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_moves_point_dist_lt_eqOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_moves_point_dist_lt_eqOn

end DifferentialGeometry.Topology.PiecewiseLinear
