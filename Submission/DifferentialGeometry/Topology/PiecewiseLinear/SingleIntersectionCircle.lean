/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleMap
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenPLPath
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.Classical in
theorem exists_piecewiseAffineOn_circle_single_intersection
    {S : Set E} (hS : IsPLSphere 1 S) {p q : E} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    {T : Set F} (hT : IsClosed T) (hconn : IsPreconnected Tᶜ)
    {x v : F} {r : ℝ} (hr : 0 < r)
    (hline : ∀ t ∈ _root_.Set.Icc (-r) r, x + t • v ∈ T ↔ t = 0) :
    ∃ (A B : Set E) (γ δ : ℝ → E) (H : E → F),
      IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) A ∧ IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) B ∧
        A ∪ B = S ∧ A ∩ B = {γ 0, γ 1} ∧ IsPiecewiseAffineOn H _root_.Set.univ ∧
          (∀ t ∈ _root_.Set.Icc 0 1, H (γ t) = x + (r * t - r / 2) • v) ∧
            MapsTo H B Tᶜ ∧ S ∩ H ⁻¹' T = {γ (1 / 2)} := by
  let a := x + (-r / 2) • v
  let b := x + (r / 2) • v
  have ha : a ∈ Tᶜ := by
    intro h
    have := (hline (-r / 2) ⟨by linarith, by linarith⟩).mp h
    linarith
  have hb : b ∈ Tᶜ := by
    intro h
    have := (hline (r / 2) ⟨by linarith, by linarith⟩).mp h
    linarith
  obtain ⟨g, hg, hg0, hg1, hgT⟩ := exists_piecewiseAffine_path_of_isOpen
    hT.isOpen_compl hconn ha hb
  let f := AffineMap.lineMap (k := ℝ) a b
  have hf : IsPiecewiseAffineOn f (_root_.Set.Icc 0 1) :=
    isPiecewiseAffineOn_of_affine_of_isHPolytope f isHPolytope_Icc
  have hfval : ∀ t, f t = x + (r * t - r / 2) • v := by
    intro t
    change AffineMap.lineMap (k := ℝ) (x + (-r / 2) • v) (x + (r / 2) • v) t = _
    rw [AffineMap.lineMap_apply_module, smul_add, smul_add, smul_smul, smul_smul,
      add_add_add_comm, ← add_smul, sub_add_cancel, one_smul, ← add_smul]
    congr 2
    ring
  obtain ⟨A, B, γ, δ, H, hγ, hδ, hγ0, hγ1, _, _, hunion, hinter, hH, hHγ, hHδ⟩ :=
    exists_piecewiseAffineOn_circle_of_paths hS hp hq hpq hf hg
      (by simpa only [f, AffineMap.lineMap_apply_zero] using hg0.symm)
      (by simpa only [f, AffineMap.lineMap_apply_one] using hg1.symm)
  obtain ⟨G, _, hG, _, hfix, _, _⟩ :=
    hH.exists_lipschitz_extension hS.isPolyhedron isOpen_univ (_root_.Set.subset_univ S)
  have hGA : ∀ t ∈ _root_.Set.Icc 0 1, G (γ t) = x + (r * t - r / 2) • v := by
    intro t ht
    rw [hfix (hunion.subset (Or.inl (hγ.bijOn.mapsTo ht))), hHγ t ht, hfval]
  have hGB : _root_.Set.MapsTo G B Tᶜ := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hδ.bijOn.surjOn hz
    rw [hfix (hunion.subset (Or.inr (hδ.bijOn.mapsTo ht))), hHδ t ht]
    exact hgT ht
  refine ⟨A, B, γ, δ, G, hγ, hδ, hunion, by simpa only [hγ0, hγ1] using hinter,
    hG, hGA, hGB, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hzT⟩
    rcases hunion.symm.subset hz with hzA | hzB
    · obtain ⟨t, ht, rfl⟩ := hγ.bijOn.surjOn hzA
      rw [_root_.Set.mem_preimage, hGA t ht] at hzT
      have htr : r * t - r / 2 ∈ _root_.Set.Icc (-r) r := by
        constructor <;> nlinarith [ht.1, ht.2]
      have ht0 := (hline _ htr).mp hzT
      have htval : t = 1 / 2 := by nlinarith
      simp only [htval, _root_.Set.mem_singleton_iff]
    · exact (hGB hzB hzT).elim
  · rintro rfl
    refine ⟨hunion.subset (Or.inl (hγ.bijOn.mapsTo (by norm_num))), ?_⟩
    rw [_root_.Set.mem_preimage, hGA _ (by norm_num)]
    have heq : r * (1 / 2) - r / 2 = 0 := by ring
    rw [heq]
    exact (hline 0 ⟨by linarith, hr.le⟩).mpr rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_circle_single_intersection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_circle_single_intersection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_circle_single_intersection ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_circle_single_intersection

open _root_.Classical in
omit [FiniteDimensional ℝ E] in
theorem exists_translate_circle_single_intersection_avoiding_finite
    {A B S Z : Set E} {γ : ℝ → E} {H : E → F}
    (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) A) (hB : IsCompact B) (hunion : A ∪ B = S)
    (hH : Continuous H) {T : Set F} (hT : IsClosed T) (hHB : _root_.Set.MapsTo H B Tᶜ)
    {x v : F} {r : ℝ} (hr : 0 < r)
    (hA : ∀ t ∈ _root_.Set.Icc 0 1, H (γ t) = x + (r * t - r / 2) • v)
    (hline : ∀ t ∈ _root_.Set.Icc (-r) r, x + t • v ∈ T ↔ t = 0) (hZ : Z.Finite) :
    ∃ a t : ℝ, t ∈ _root_.Set.Ioo 0 1 ∧ γ t ∉ Z ∧ a = r / 2 - r * t ∧
      _root_.Set.MapsTo (fun z => H z + a • v) B Tᶜ ∧
        S ∩ (fun z => H z + a • v) ⁻¹' T = {γ t} := by
  have hevent : ∀ᶠ t : ℝ in nhds (1 / 2), ∀ z ∈ B, H z + (r / 2 - r * t) • v ∈ Tᶜ := by
    apply hB.eventually_forall_of_forall_eventually
    intro z hz
    have hc : Continuous (fun w : ℝ × E => H w.2 + (r / 2 - r * w.1) • v) := by fun_prop
    have heq : r / 2 - r * (1 / 2) = 0 := by ring
    exact
      (hc.tendsto (1 / 2, z)).eventually (hT.isOpen_compl.mem_nhds (by
        simpa only [heq, zero_smul, add_zero] using hHB hz))
  have hnhds : {t : ℝ | (∀ z ∈ B, H z + (r / 2 - r * t) • v ∈ Tᶜ) ∧ t ∈ _root_.Set.Ioo 0 1} ∈
      nhds (1 / 2) := Filter.inter_mem hevent (isOpen_Ioo.mem_nhds (by norm_num))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hbad : (Function.invFunOn γ (_root_.Set.Icc 0 1) '' Z).Finite := hZ.image _
  obtain ⟨t, ht, havoid⟩ := ((Set.Ioo_infinite
    (show (1 / 2 : ℝ) - ε < 1 / 2 + ε by linarith)).sdiff hbad).nonempty
  have htball : t ∈ Metric.ball (1 / 2 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨hBt, ht01⟩ := hball htball
  have htcc : t ∈ _root_.Set.Icc (0 : ℝ) 1 := _root_.Set.Ioo_subset_Icc_self ht01
  have htZ : γ t ∉ Z := by
    intro h
    exact havoid ⟨γ t, h, hγ.bijOn.invOn_invFunOn.1 htcc⟩
  refine ⟨r / 2 - r * t, t, ht01, htZ, rfl, hBt, ?_⟩
  have hvalue : ∀ u ∈ _root_.Set.Icc 0 1,
      H (γ u) + (r / 2 - r * t) • v = x + (r * (u - t)) • v := by
    intro u hu
    rw [hA u hu, add_assoc, ← add_smul]
    congr 2
    ring
  ext z
  constructor
  · rintro ⟨hz, hzT⟩
    rcases hunion.symm.subset hz with hzA | hzB
    · obtain ⟨u, hu, rfl⟩ := hγ.bijOn.surjOn hzA
      rw [_root_.Set.mem_preimage, hvalue u hu] at hzT
      have hrut : r * (u - t) ∈ _root_.Set.Icc (-r) r := by
        constructor <;> nlinarith [hu.1, hu.2, ht01.1, ht01.2]
      have heq := (hline _ hrut).mp hzT
      have hut : u = t := by nlinarith
      simp only [hut, _root_.Set.mem_singleton_iff]
    · exact (hBt z hzB hzT).elim
  · rintro rfl
    refine ⟨hunion.subset (Or.inl (hγ.bijOn.mapsTo htcc)), ?_⟩
    rw [_root_.Set.mem_preimage, hvalue t htcc, sub_self, _root_.MulZeroClass.mul_zero]
    exact (hline 0 ⟨by linarith, hr.le⟩).mpr rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_translate_circle_single_intersection_avoiding_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_translate_circle_single_intersection_avoiding_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_translate_circle_single_intersection_avoiding_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_translate_circle_single_intersection_avoiding_finite

end DifferentialGeometry.Topology.PiecewiseLinear
