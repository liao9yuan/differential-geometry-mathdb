/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLMap
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem mapsTo_of_eqOn_compl {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    {S : Set X} (hfix : _root_.Set.EqOn f id Sᶜ) : _root_.Set.MapsTo f S S := by
  intro x hx
  by_contra hnot
  have heq : f x = x := f.injective (hfix hnot)
  exact hnot (heq.symm ▸ hx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_of_eqOn_compl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_of_eqOn_compl target :: scope.openDecls } }

private theorem image_eq_of_eqOn_compl {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    {S : Set X} (hfix : _root_.Set.EqOn f id Sᶜ) : f '' S = S := by
  refine Subset.antisymm (mapsTo_of_eqOn_compl f hfix).image_subset ?_
  intro y hy
  obtain ⟨x, rfl⟩ := f.surjective y
  refine ⟨x, ?_, rfl⟩
  by_contra hx
  exact hx (by simpa only [hfix hx, id_eq] using hy)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_eq_of_eqOn_compl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.image_eq_of_eqOn_compl target :: scope.openDecls } }

theorem exists_isPL_homeomorph_of_finite_disjoint_support {ι M : Type*}
    [TopologicalSpace M] {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (s : Finset ι) (Ω : ι → Set M) (φ : ι → M ≃ₜ M)
    (hdis : Pairwise (Disjoint on Ω)) (hPL : ∀ i ∈ s, IsPL n n (φ i))
    (hPLinv : ∀ i ∈ s, IsPL n n (φ i).symm)
    (hfix : ∀ i ∈ s, _root_.Set.EqOn (φ i) id (Ω i)ᶜ) :
    ∃ Φ : M ≃ₜ M, IsPL n n Φ ∧ IsPL n n Φ.symm ∧
      (∀ i ∈ s, _root_.Set.EqOn Φ (φ i) (Ω i)) ∧ _root_.Set.EqOn Φ id (⋃ i ∈ s, Ω i)ᶜ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Homeomorph.refl M, isPL_id, isPL_id, ?_, fun _ _ => rfl⟩
    simp
  | @insert i s hi ih =>
    obtain ⟨Φ, hΦ, hΦinv, hΦeq, hΦfix⟩ := ih
      (fun j hj => hPL j (Finset.mem_insert_of_mem hj))
      (fun j hj => hPLinv j (Finset.mem_insert_of_mem hj))
      (fun j hj => hfix j (Finset.mem_insert_of_mem hj))
    refine ⟨Φ.trans (φ i), (hPL i (Finset.mem_insert_self _ _)).comp hΦ,
      hΦinv.comp (hPLinv i (Finset.mem_insert_self _ _)), ?_, ?_⟩
    · intro j hj x hx
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        have hxout : x ∉ ⋃ j ∈ s, Ω j := by
          intro hxU
          obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxU
          exact Set.disjoint_left.mp (hdis (show i ≠ j from fun heq => hi (heq.symm ▸ hj))) hx hxj
        change φ i (Φ x) = φ i x
        rw [hΦfix hxout, id_eq]
      · have hji : j ≠ i := fun heq => hi (heq ▸ hj)
        have hy : φ j x ∈ Ω j := mapsTo_of_eqOn_compl (φ j)
          (hfix j (Finset.mem_insert_of_mem hj)) hx
        change φ i (Φ x) = φ j x
        rw [hΦeq j hj hx]
        exact hfix i (Finset.mem_insert_self _ _) (Set.disjoint_left.mp (hdis hji) hy)
    · intro x hx
      have hxi : x ∉ Ω i := fun hxi => hx (mem_iUnion₂.mpr
        ⟨i, Finset.mem_insert_self _ _, hxi⟩)
      have hxs : x ∉ ⋃ j ∈ s, Ω j := by
        intro hxU
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxU
        exact hx (mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hj, hxj⟩)
      change φ i (Φ x) = x
      rw [hΦfix hxs, id_eq, hfix i (Finset.mem_insert_self _ _) hxi, id_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPL_homeomorph_of_finite_disjoint_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPL_homeomorph_of_finite_disjoint_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPL_homeomorph_of_finite_disjoint_support ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPL_homeomorph_of_finite_disjoint_support

theorem homeomorph_eqOn_of_disjoint_support {ι M : Type*} [TopologicalSpace M]
    {s : Finset ι} {Ω : ι → Set M} {Φ : M ≃ₜ M}
    (hdis : Pairwise (Disjoint on Ω)) (hfix : _root_.Set.EqOn Φ id (⋃ i ∈ s, Ω i)ᶜ)
    {j : ι} (hj : j ∉ s) : _root_.Set.EqOn Φ id (Ω j) := by
  intro x hx
  apply hfix
  intro hxU
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
  exact Set.disjoint_left.mp (hdis (show j ≠ i from fun heq => hj (heq.symm ▸ hi))) hx hxi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.homeomorph_eqOn_of_disjoint_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.homeomorph_eqOn_of_disjoint_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.homeomorph_eqOn_of_disjoint_support ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.homeomorph_eqOn_of_disjoint_support

theorem homeomorph_image_eq_of_disjoint_support {ι M : Type*} [TopologicalSpace M]
    {s : Finset ι} {Ω : ι → Set M} {φ : ι → M ≃ₜ M} {Φ : M ≃ₜ M}
    (hdis : Pairwise (Disjoint on Ω)) (hφfix : ∀ i ∈ s, _root_.Set.EqOn (φ i) id (Ω i)ᶜ)
    (heq : ∀ i ∈ s, _root_.Set.EqOn Φ (φ i) (Ω i)) (hfix : _root_.Set.EqOn Φ id (⋃ i ∈ s, Ω i)ᶜ) :
    ∀ i, Φ '' Ω i = Ω i := by
  classical
  intro i
  by_cases hi : i ∈ s
  · rw [_root_.Set.image_congr (heq i hi)]
    exact image_eq_of_eqOn_compl (φ i) (hφfix i hi)
  · rw [_root_.Set.image_congr (homeomorph_eqOn_of_disjoint_support hdis hfix hi), _root_.Set.image_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.homeomorph_image_eq_of_disjoint_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.homeomorph_image_eq_of_disjoint_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.homeomorph_image_eq_of_disjoint_support ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.homeomorph_image_eq_of_disjoint_support

theorem dist_lt_of_disjoint_support {ι M : Type*} [PseudoMetricSpace M]
    {s : Finset ι} {Ω : ι → Set M} {φ : ι → M → M} {Φ : M → M} {ε : M → ℝ}
    (hε : ∀ x, 0 < ε x) (heq : ∀ i ∈ s, _root_.Set.EqOn Φ (φ i) (Ω i))
    (hfix : _root_.Set.EqOn Φ id (⋃ i ∈ s, Ω i)ᶜ)
    (hdist : ∀ i ∈ s, ∀ x ∈ Ω i, _root_.Dist.dist (φ i x) x < ε x) :
    ∀ x, _root_.Dist.dist (Φ x) x < ε x := by
  intro x
  by_cases hx : x ∈ ⋃ i ∈ s, Ω i
  · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    rw [heq i hi hxi]
    exact hdist i hi x hxi
  · rw [hfix hx, id_eq, dist_self]
    exact hε x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.dist_lt_of_disjoint_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.dist_lt_of_disjoint_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.dist_lt_of_disjoint_support ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.dist_lt_of_disjoint_support

end DifferentialGeometry.Topology.PiecewiseLinear
