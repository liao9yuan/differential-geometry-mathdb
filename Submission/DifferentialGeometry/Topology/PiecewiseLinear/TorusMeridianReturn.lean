/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import Submission.DifferentialGeometry.Topology.Connected.MarkedExcursion
import Submission.DifferentialGeometry.Topology.LoopSpace.PrimitiveCircleLift
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleLiftArc
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleParametrization
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingLiftExtrema
import Mathlib.Topology.DiscreteSubset

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem finite_circle_lift_inter_compact
    {K : Set loopCircle} (hK : K.Finite) {C : Set ℝ} (hC : IsCompact C) :
    (((↑) : ℝ → loopCircle) ⁻¹' K ∩ C).Finite := by
  have hd : IsDiscrete (((↑) : ℝ → loopCircle) ⁻¹' K) :=
    hK.isDiscrete.preimage' (AddCircle.continuous_mk' 1).continuousOn fun z =>
      ⟨(AddCircle.isCoveringMap_coe (1 : ℝ) z).discreteTopology_fiber⟩
  exact (hC.inter_left (hK.isClosed.preimage (AddCircle.continuous_mk' 1))).finite
    (hd.mono _root_.Set.inter_subset_left)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_circle_lift_inter_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.finite_circle_lift_inter_compact target :: scope.openDecls } }

private theorem surjective_fundamentalGroup_map_homeomorph
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] (e : Y ≃ₜ Z) (y : Y) :
    Function.Surjective (FundamentalGroup.map (e : C(Y, Z)) y) := by
  have h := (fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv
    e.toHomotopyEquiv y (e y) rfl).2
  change Function.Surjective (FundamentalGroup.mapOfEq (e : C(Y, Z))
    (rfl : e y = e y)) at h
  have heq : FundamentalGroup.mapOfEq (e : C(Y, Z)) (rfl : e y = e y) =
      FundamentalGroup.map (e : C(Y, Z)) y := by
    ext u
    rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
    rfl
  rwa [heq] at h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.surjective_fundamentalGroup_map_homeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.surjective_fundamentalGroup_map_homeomorph target :: scope.openDecls } }

private theorem product_fiber_mem_iff
    {E : Type*} [TopologicalSpace E] {M Q X : Set E}
    (φ : (M × Q) ≃ₜ X) (q : Q) (x : X) :
    (x : E) ∈ _root_.Set.range (fun m : M => (φ (m, q) : E)) ↔ (φ.symm x).2 = q := by
  constructor
  · rintro ⟨m, hm⟩
    have hmx : φ (m, q) = x := Subtype.ext hm
    rw [← hmx, φ.symm_apply_apply]
  · intro hx
    refine ⟨(φ.symm x).1, ?_⟩
    have heq : ((φ.symm x).1, q) = φ.symm x := Prod.ext rfl hx.symm
    change (φ ((φ.symm x).1, q) : E) = (x : E)
    rw [heq, φ.apply_symm_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.product_fiber_mem_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.product_fiber_mem_iff target :: scope.openDecls } }

private theorem surjective_fundamentalGroup_circle_conjugate
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (eY : loopCircle ≃ₜ Y) (eZ : loopCircle ≃ₜ Z) (f : C(Y, Z))
    (hf : ∀ y, Function.Surjective (FundamentalGroup.map f y)) :
    Function.Surjective (FundamentalGroup.map
      ((eZ.symm : C(Z, loopCircle)).comp (f.comp (eY : C(loopCircle, Y)))) 0) := by
  intro u
  obtain ⟨v, hv⟩ := surjective_fundamentalGroup_map_homeomorph eZ.symm (f (eY 0)) u
  obtain ⟨w, hw⟩ := hf (eY 0) v
  obtain ⟨z, hz⟩ := surjective_fundamentalGroup_map_homeomorph eY 0 w
  refine ⟨z, ?_⟩
  change (Path.Homotopic.Quotient.map z
    ((eZ.symm : C(Z, loopCircle)).comp (f.comp (eY : C(loopCircle, Y))))) = u
  rw [Path.Homotopic.Quotient.map_comp, Path.Homotopic.Quotient.map_comp]
  change FundamentalGroup.map (eZ.symm : C(Z, loopCircle)) (f (eY 0))
    (FundamentalGroup.map f (eY 0) (FundamentalGroup.map (eY : C(loopCircle, Y)) 0 z)) = u
  rw [hz, hw, hv]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.surjective_fundamentalGroup_circle_conjugate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.surjective_fundamentalGroup_circle_conjugate target :: scope.openDecls } }

private theorem exists_ordered_lifts_of_same_mark
    (ρ : C(loopCircle, loopCircle)) {K : Set loopCircle}
    (hmore : ∃ x y : loopCircle, x ≠ y ∧ ρ x = ρ y ∧ ρ x ∈ K) :
    ∃ a b : ℝ, a < b ∧ b < a + 1 ∧ ρ (a : loopCircle) = ρ (b : loopCircle) ∧
      ρ (a : loopCircle) ∈ K := by
  obtain ⟨x, y, hxy, hρ, hxK⟩ := hmore
  obtain ⟨a, ha, hax⟩ := exists_lift_mem_Ico x
  obtain ⟨b, hb, hby⟩ := exists_lift_mem_Ico y
  have hab : a ≠ b := fun h =>
    hxy (hax.symm.trans ((congrArg (fun t : ℝ => (t : loopCircle)) h).trans hby))
  rcases lt_or_gt_of_ne hab with hab | hba
  · refine ⟨a, b, hab, by linarith [ha.1, hb.2], ?_, ?_⟩
    · simpa only [hax, hby] using hρ
    · simpa only [hax] using hxK
  · refine ⟨b, a, hba, by linarith [hb.1, ha.2], ?_, ?_⟩
    · simpa only [hax, hby] using hρ.symm
    · simpa only [hby, ← hρ] using hxK

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_ordered_lifts_of_same_mark
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.exists_ordered_lifts_of_same_mark target :: scope.openDecls } }

private theorem exists_returning_arc_of_circle_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} {J M Q X : Set E} (hJ : IsPLSphere 1 J)
    (e : loopCircle ≃ₜ J) (φ : (M × Q) ≃ₜ X) (hJX : J ⊆ X) (q : ι → Q)
    {a b : ℝ} (hab : a < b) (hba : b < a + 1) (i : ι)
    (ha : (φ.symm ⟨e (a : loopCircle), hJX (e (a : loopCircle)).property⟩).2 = q i)
    (hb : (φ.symm ⟨e (b : loopCircle), hJX (e (b : loopCircle)).property⟩).2 = q i)
    (havoid : ∀ t ∈ _root_.Set.Ioo a b, ∀ k,
      (φ.symm ⟨e (t : loopCircle), hJX (e (t : loopCircle)).property⟩).2 ≠ q k) :
    ∃ (B : Set E) (γ : ℝ → E), IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) B ∧ B ⊆ J ∧
      ({γ 0, γ 1} : Set E) ⊆ _root_.Set.range (fun m : M => (φ (m, q i) : E)) ∧
      B ∩ (⋃ k, _root_.Set.range (fun m : M => (φ (m, q k) : E))) = {γ 0, γ 1} := by
  let g : ℝ → E := fun t => e (t : loopCircle)
  obtain ⟨γ, hγ, hγ0, hγ1⟩ :=
    hJ.exists_isPLHomeomorphOn_Icc_image_circleInterval e hab hba
  have hga : g a ∈ _root_.Set.range (fun m : M => (φ (m, q i) : E)) :=
    (product_fiber_mem_iff φ (q i) _).mpr ha
  have hgb : g b ∈ _root_.Set.range (fun m : M => (φ (m, q i) : E)) :=
    (product_fiber_mem_iff φ (q i) _).mpr hb
  refine ⟨g '' _root_.Set.Icc a b, γ, hγ, ?_, ?_, ?_⟩
  · rintro _ ⟨t, -, rfl⟩
    exact (e _).property
  · intro y hy
    simp only [hγ0, hγ1, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hga
    · exact hgb
  · rw [hγ0, hγ1]
    apply Subset.antisymm
    · rintro _ ⟨⟨t, ht, rfl⟩, htf⟩
      by_cases hta : t = a
      · rw [hta]
        exact _root_.Set.mem_insert _ _
      by_cases htb : t = b
      · rw [htb]
        exact _root_.Set.mem_insert_of_mem _ rfl
      obtain ⟨k, hk⟩ := mem_iUnion.mp htf
      exact (havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩ k
        ((product_fiber_mem_iff φ (q k) _).mp hk)).elim
    · intro y hy
      rcases mem_insert_iff.mp hy with hy | hy
      · subst y
        exact ⟨⟨a, ⟨le_rfl, hab.le⟩, rfl⟩, mem_iUnion.mpr ⟨i, hga⟩⟩
      · have hy' := mem_singleton_iff.mp hy
        subst y
        exact ⟨⟨b, ⟨hab.le, le_rfl⟩, rfl⟩, mem_iUnion.mpr ⟨i, hgb⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_returning_arc_of_circle_interval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.exists_returning_arc_of_circle_interval target :: scope.openDecls } }

theorem exists_returning_arc_of_primitive_longitude
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] {J M Q X : Set E}
    (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    (φ : (M × Q) ≃ₜ X) (hJX : J ⊆ X) (q : ι → Q)
    (hcross : ∀ i x, x ∈ J ∩ _root_.Set.range (fun m : M => (φ (m, q i) : E)) →
      HasPLCurveCrossingOnAt X J (_root_.Set.range (fun m : M => (φ (m, q i) : E))) x)
    (honto : ∀ x : J, Function.Surjective (FundamentalGroup.map
      (ContinuousMap.snd.comp ((φ.symm : C(X, M × Q)).comp
        (⟨inclusion hJX, continuous_inclusion hJX⟩ : C(J, X)))) x))
    (hmore : ∃ i, (J ∩ _root_.Set.range (fun m : M => (φ (m, q i) : E))).Nontrivial) :
    ∃ (i : ι) (B : Set E) (γ : ℝ → E), IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) B ∧ B ⊆ J ∧
      ({γ 0, γ 1} : Set E) ⊆ _root_.Set.range (fun m : M => (φ (m, q i) : E)) ∧
      B ∩ (⋃ k, _root_.Set.range (fun m : M => (φ (m, q k) : E))) = {γ 0, γ 1} := by
  classical
  obtain ⟨eJ⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hJ
  obtain ⟨eQ⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hQ
  let π : C(J, Q) := ContinuousMap.snd.comp ((φ.symm : C(X, M × Q)).comp
    ⟨inclusion hJX, continuous_inclusion hJX⟩)
  let ρ : C(loopCircle, loopCircle) :=
    (eQ.symm : C(Q, loopCircle)).comp (π.comp (eJ : C(loopCircle, J)))
  have hρonto : Function.Surjective (FundamentalGroup.map ρ 0) :=
    surjective_fundamentalGroup_circle_conjugate eJ eQ π honto
  obtain ⟨F, hlift, hperiod⟩ := exists_primitive_real_lift ρ hρonto
  let K : Set loopCircle := eQ ⁻¹' _root_.Set.range q
  let P : Set ℝ := ((↑) : ℝ → loopCircle) ⁻¹' K
  have hK : K.Finite := (_root_.Set.finite_range q).preimage eQ.injective.injOn
  have hP : ∀ y : ℝ, y + 1 ∈ P ↔ y ∈ P := by
    intro y
    change eQ ((y + 1 : ℝ) : loopCircle) ∈ _root_.Set.range q ↔ eQ (y : loopCircle) ∈ _root_.Set.range q
    rw [AddCircle.coe_add_period]
  have hfinite : ∀ a b : ℝ, (P ∩ F '' _root_.Set.Icc a b).Finite := fun a b =>
    finite_circle_lift_inter_compact hK (isCompact_Icc.image F.continuous)
  have hFproj (t : ℝ) : eQ (F t : loopCircle) = π (eJ (t : loopCircle)) := by
    rw [hlift]
    exact eQ.apply_symm_apply _
  have hno : ∀ t : ℝ, F t ∈ P → ¬ IsLocalMax F t ∧ ¬ IsLocalMin F t := by
    intro t ht
    change eQ (F t : loopCircle) ∈ _root_.Set.range q at ht
    obtain ⟨i, hi⟩ := ht
    have hcoord : π (eJ (t : loopCircle)) = q i := (hFproj t).symm.trans hi.symm
    have hfiber : (eJ (t : loopCircle) : E) ∈
        range (fun m : M => (φ (m, q i) : E)) :=
      (product_fiber_mem_iff φ (q i) _).mpr hcoord
    have hc := hcross i _ ⟨(eJ (t : loopCircle)).property, hfiber⟩
    have hn := HasPLCurveCrossingOnAt.not_isLocalExtr_longitude_lift φ hJX eJ eQ
      F F.continuous hFproj hi.symm hc
    exact ⟨fun h => hn (Or.inr h), fun h => hn (Or.inl h)⟩
  have hmoreρ : ∃ x y : loopCircle, x ≠ y ∧ ρ x = ρ y ∧ ρ x ∈ K := by
    obtain ⟨i, p, hp, s, hs, hps⟩ := hmore
    let u : J := ⟨p, hp.1⟩
    let v : J := ⟨s, hs.1⟩
    have hu : π u = q i := (product_fiber_mem_iff φ (q i) _).mp hp.2
    have hv : π v = q i := (product_fiber_mem_iff φ (q i) _).mp hs.2
    refine ⟨eJ.symm u, eJ.symm v, ?_, ?_, ?_⟩
    · intro huv
      exact hps (congrArg Subtype.val (eJ.symm.injective huv))
    · change eQ.symm (π (eJ (eJ.symm u))) = eQ.symm (π (eJ (eJ.symm v)))
      rw [eJ.apply_symm_apply, eJ.apply_symm_apply, hu, hv]
    · change eQ (eQ.symm (π (eJ (eJ.symm u)))) ∈ _root_.Set.range q
      rw [eJ.apply_symm_apply, eQ.apply_symm_apply, hu]
      exact _root_.Set.mem_range_self i
  obtain ⟨a, b, hab, hba, habρ, haK⟩ := exists_ordered_lifts_of_same_mark ρ hmoreρ
  have haP : F a ∈ P := by
    change (F a : loopCircle) ∈ K
    rwa [hlift]
  have hmod : ∃ k : ℤ, F b - F a = (k : ℝ) :=
    (loopCircle_coe_eq_coe_iff _ _).mp (by rw [hlift, hlift, habρ])
  obtain ⟨c, d, hcd, hdc, heq, hcP, havoid⟩ :=
    exists_periodic_marked_excursion F.continuous hperiod hP hfinite hno hab hba haP hmod
  change eQ (F c : loopCircle) ∈ _root_.Set.range q at hcP
  obtain ⟨i, hi⟩ := hcP
  have hc : π (eJ (c : loopCircle)) = q i := (hFproj c).symm.trans hi.symm
  have hd : π (eJ (d : loopCircle)) = q i := by
    rw [← hFproj d, ← heq]
    exact hi.symm
  have hav : ∀ t ∈ _root_.Set.Ioo c d, ∀ k, π (eJ (t : loopCircle)) ≠ q k := by
    intro t ht k he
    apply havoid t ht
    change eQ (F t : loopCircle) ∈ _root_.Set.range q
    exact ⟨k, ((hFproj t).trans he).symm⟩
  obtain ⟨B, γ, hγ, hBJ, hend, hinter⟩ :=
    exists_returning_arc_of_circle_interval hJ eJ φ hJX q hcd hdc i hc hd hav
  exact ⟨i, B, γ, hγ, hBJ, hend, hinter⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_returning_arc_of_primitive_longitude then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_returning_arc_of_primitive_longitude"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_returning_arc_of_primitive_longitude ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_returning_arc_of_primitive_longitude

end DifferentialGeometry.Topology.PiecewiseLinear
