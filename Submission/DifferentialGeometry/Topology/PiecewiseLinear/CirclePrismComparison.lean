/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem IsPLCirclePositive.of_leftInverse {S : Set E} {u v : E → E}
    (hpos : IsPLCirclePositive S u) (hu : _root_.Set.BijOn u S S) (hv : _root_.Set.MapsTo v S S)
    (hvu : ∀ x ∈ S, v (u x) = x) : IsPLCirclePositive S v := by
  obtain ⟨g, hgc, hgb, hgu⟩ := hpos
  refine ⟨g, hgc, hgb, hgu.inv (bijective_circleConj hgb hu).2 ?_⟩
  intro θ
  apply hgb.injOn (_root_.Set.mem_univ _) (_root_.Set.mem_univ _)
  rw [circleConj_spec hgb hv, circleConj_spec hgb hu.mapsTo,
    hvu (g θ) (hgb.mapsTo (_root_.Set.mem_univ θ))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCirclePositive.of_leftInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCirclePositive.of_leftInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCirclePositive.of_leftInverse ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCirclePositive.of_leftInverse

theorem isPLCirclePositive_comp_of_not_isPLCirclePositive [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsPLSphere 1 S) {u v : E → E}
    (hu : IsPLHomeomorphOn u S S) (hv : IsPLHomeomorphOn v S S)
    (hnu : ¬ IsPLCirclePositive S u) (hnv : ¬ IsPLCirclePositive S v) :
    IsPLCirclePositive S (u ∘ v) := by
  obtain ⟨g, hgc, hgb⟩ := exists_loopCircle_param_of_isPLSphere_one hS
  let ψ : loopCircle ≃ₜ loopCircle := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (circleConj g u) (bijective_circleConj hgb hu.bijOn))
    (continuous_circleConj hgc hgb hu.isPiecewiseAffineOn.continuousOn hu.bijOn.mapsTo)
  let χ : loopCircle ≃ₜ loopCircle := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (circleConj g v) (bijective_circleConj hgb hv.bijOn))
    (continuous_circleConj hgc hgb hv.isPiecewiseAffineOn.continuousOn hv.bijOn.mapsTo)
  have hψ : ¬ HasIncreasingCircleLift ψ := fun h => hnu ⟨g, hgc, hgb, h⟩
  have hχ : ¬ HasIncreasingCircleLift χ := fun h => hnv ⟨g, hgc, hgb, h⟩
  refine ⟨g, hgc, hgb,
    (hasIncreasingCircleLift_comp_of_not_hasIncreasingCircleLift ψ χ hψ hχ).congr ?_⟩
  intro θ
  exact circleConj_comp hgb hv.bijOn.mapsTo θ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_comp_of_not_isPLCirclePositive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_comp_of_not_isPLCirclePositive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_comp_of_not_isPLCirclePositive ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_comp_of_not_isPLCirclePositive

theorem exists_isPLHomeomorphOn_circle_prod_of_isPLCirclePositive_iff
    [FiniteDimensional ℝ E] {S : Set E} (hS : IsPLSphere 1 S) {u v : E → E}
    (hu : IsPLHomeomorphOn u S S) (hv : IsPLHomeomorphOn v S S)
    (horient : IsPLCirclePositive S u ↔ IsPLCirclePositive S v) :
    ∃ Φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Φ (S ×ˢ _root_.Set.Icc 0 1) (S ×ˢ _root_.Set.Icc 0 1) ∧
        (∀ x ∈ S, Φ (x, 0) = (u x, 0)) ∧ ∀ x ∈ S, Φ (x, 1) = (v x, 1) := by
  let w := v ∘ Function.invFunOn u S
  have hw : IsPLHomeomorphOn w S S := hu.symm.trans hv
  have hwpos : IsPLCirclePositive S w := by
    by_cases hupos : IsPLCirclePositive S u
    · exact (horient.mp hupos).comp
        (hupos.of_leftInverse hu.bijOn hu.symm.bijOn.mapsTo
          fun x hx => hu.bijOn.invOn_invFunOn.1 hx) hu.symm.bijOn.mapsTo
    · have hvneg : ¬ IsPLCirclePositive S v := fun h => hupos (horient.mpr h)
      have huneg : ¬ IsPLCirclePositive S (Function.invFunOn u S) := by
        intro hinv
        exact hupos (hinv.of_leftInverse hu.symm.bijOn hu.bijOn.mapsTo
          fun x hx => hu.bijOn.invOn_invFunOn.2 hx)
      exact isPLCirclePositive_comp_of_not_isPLCirclePositive hS hv hu.symm hvneg huneg
  obtain ⟨Ξ, hΞ, hΞ0, hΞ1⟩ := isPLPseudoIsotopicToId_of_isPLCirclePositive hS hw hwpos
  have hprod : IsPLHomeomorphOn (Prod.map u (id : ℝ → ℝ))
      (S ×ˢ _root_.Set.Icc 0 1) (S ×ˢ _root_.Set.Icc 0 1) :=
    hu.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  refine ⟨Ξ ∘ Prod.map u id, hprod.trans hΞ, fun x hx => ?_, fun x hx => ?_⟩
  · exact hΞ0 (u x) (hu.bijOn.mapsTo hx)
  · change Ξ (u x, 1) = (v x, 1)
    rw [hΞ1 (u x) (hu.bijOn.mapsTo hx)]
    change (v (Function.invFunOn u S (u x)), (1 : ℝ)) = (v x, 1)
    rw [hu.bijOn.invOn_invFunOn.1 hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_circle_prod_of_isPLCirclePositive_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_circle_prod_of_isPLCirclePositive_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_circle_prod_of_isPLCirclePositive_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_circle_prod_of_isPLCirclePositive_iff

theorem exists_isPLHomeomorphOn_arc_prod_of_isPLCirclePositive_iff
    [FiniteDimensional ℝ E] {S A : Set E} (hS : IsPLSphere 1 S)
    {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) A) (hAS : A ⊆ S)
    {u v : E → E} (hu : IsPLHomeomorphOn u S S) (hv : IsPLHomeomorphOn v S S)
    (horient : IsPLCirclePositive S u ↔ IsPLCirclePositive S v) :
    ∃ (T : Set (E × ℝ)) (β : ℝ × ℝ → E × ℝ),
      IsPLHomeomorphOn β (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) T ∧
        T ⊆ S ×ˢ _root_.Set.Icc 0 1 ∧
        (∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, β (s, 0) = (u (γ s), 0)) ∧
        (∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, β (s, 1) = (v (γ s), 1)) ∧
        (∀ z ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1, (β z).2 = 0 ↔ z.2 = 0) ∧
        ∀ z ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1, (β z).2 = 1 ↔ z.2 = 1 := by
  obtain ⟨Φ, hΦ, hΦ0, hΦ1⟩ :=
    exists_isPLHomeomorphOn_circle_prod_of_isPLCirclePositive_iff hS hu hv horient
  have hA : IsPolyhedron A := ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ).isPolyhedron
  have hprod : IsPLHomeomorphOn (Prod.map γ (id : ℝ → ℝ))
      (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) (A ×ˢ _root_.Set.Icc 0 1) :=
    hγ.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  have hsub : A ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ S ×ˢ _root_.Set.Icc 0 1 := fun z hz => ⟨hAS hz.1, hz.2⟩
  have hrestrict := hΦ.restrict (hA.prod isHPolytope_Icc.isPolyhedron) hsub
  refine ⟨Φ '' (A ×ˢ _root_.Set.Icc (0 : ℝ) 1), Φ ∘ Prod.map γ id, hprod.trans hrestrict, ?_,
    fun s hs => ?_, fun s hs => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hΦ.bijOn.mapsTo (hsub hz)
  · exact hΦ0 (γ s) (hAS (hγ.bijOn.mapsTo hs))
  · exact hΦ1 (γ s) (hAS (hγ.bijOn.mapsTo hs))
  · have hmem : (γ z.1, z.2) ∈ S ×ˢ _root_.Set.Icc (0 : ℝ) 1 :=
      ⟨hAS (hγ.bijOn.mapsTo hz.1), hz.2⟩
    constructor
    · intro hzero
      exact snd_eq_of_map_level hΦ hu (by norm_num) hΦ0 hmem hzero
    · intro hzero
      change (Φ (γ z.1, z.2)).2 = 0
      rw [hzero, hΦ0 (γ z.1) (hAS (hγ.bijOn.mapsTo hz.1))]
  · have hmem : (γ z.1, z.2) ∈ S ×ˢ _root_.Set.Icc (0 : ℝ) 1 :=
      ⟨hAS (hγ.bijOn.mapsTo hz.1), hz.2⟩
    constructor
    · intro hone
      exact snd_eq_of_map_level hΦ hv (by norm_num) hΦ1 hmem hone
    · intro hone
      change (Φ (γ z.1, z.2)).2 = 1
      rw [hone, hΦ1 (γ z.1) (hAS (hγ.bijOn.mapsTo hz.1))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_arc_prod_of_isPLCirclePositive_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_arc_prod_of_isPLCirclePositive_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_arc_prod_of_isPLCirclePositive_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_arc_prod_of_isPLCirclePositive_iff

end DifferentialGeometry.Topology.PiecewiseLinear
