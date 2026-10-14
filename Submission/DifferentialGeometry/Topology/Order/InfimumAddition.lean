import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Bounds.Lattice
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.WithTop

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace WithTop
open _root_.WithTop

open _root_.WithTop in
theorem sInf_coe_image_add {R : Type*} [ConditionallyCompleteLattice R]
    [AddCommGroup R] [IsOrderedAddMonoid R] {A B : Set R} (hAbdd : BddBelow A) (hBbdd : BddBelow B) :
    _root_.InfSet.sInf ((fun r : R => (r : WithTop R)) '' A) + _root_.InfSet.sInf ((fun r : R => (r : WithTop R)) '' B) =
      sInf ((fun r : R => (r : WithTop R)) '' Set.image2 (fun a b : R => a + b) A B) := by
  classical
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · have hAB := hA.image2 (f := fun a b : R => a + b) hB
      have hABbdd : BddBelow (Set.image2 (fun a b : R => a + b) A B) := by
        obtain ⟨a, ha⟩ := hAbdd
        obtain ⟨b, hb⟩ := hBbdd
        refine ⟨a + b, ?_⟩
        rintro z ⟨x, hx, y, hy, rfl⟩
        exact add_le_add (ha hx) (hb hy)
      have hInf : _root_.InfSet.sInf (Set.image2 (fun a b : R => a + b) A B) = _root_.InfSet.sInf A + _root_.InfSet.sInf B :=
        csInf_image2_eq_csInf_csInf
          (u := fun p q : R => p + q)
          (l₁ := fun q p : R => p - q) (l₂ := fun p q : R => q - p)
          (fun _ _ _ => sub_le_iff_le_add) (fun _ _ _ => sub_le_iff_le_add')
          hA hAbdd hB hBbdd
      rw [← WithTop.coe_sInf' hA hAbdd, ← WithTop.coe_sInf' hB hBbdd,
        ← WithTop.coe_sInf' hAB hABbdd, hInf, WithTop.coe_add]
    · have hBe : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
      rw [hBe, Set.image_empty, WithTop.sInf_empty, Set.image2_empty_right,
        Set.image_empty, WithTop.sInf_empty, WithTop.add_top]
  · have hAe : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    rw [hAe, Set.image_empty, WithTop.sInf_empty, Set.image2_empty_left,
      Set.image_empty, WithTop.sInf_empty, WithTop.top_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `WithTop.sInf_coe_image_add then
    throwError "Refusing to shadow existing declaration WithTop.sInf_coe_image_add"
  Lean.modifyEnv fun env => Lean.addAlias env `WithTop.sInf_coe_image_add ``Submission.WithTop.sInf_coe_image_add

end WithTop

namespace WithTop
open _root_.WithTop

open _root_.Set

section

variable {R : Type*} [ConditionallyCompleteLattice R] [Nonempty R]

open _root_.WithTop in
private theorem bddBelow_coe_preimage {A : Set (WithTop R)} (hA : BddBelow A) :
    BddBelow ((fun r : R => (r : WithTop R)) ⁻¹' A) := by
  obtain ⟨a, ha⟩ := hA
  cases a using WithTop.recTopCoe with
  | top =>
    refine ⟨Classical.arbitrary R, ?_⟩
    intro r hr
    exact (WithTop.not_top_le_coe r (ha hr)).elim
  | coe a =>
    exact ⟨a, fun r hr => WithTop.coe_le_coe.mp (ha hr)⟩

run_cmd do
  let target := ``Submission.WithTop.bddBelow_coe_preimage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `WithTop.bddBelow_coe_preimage target :: scope.openDecls } }

open _root_.WithTop in
private theorem sInf_eq_sInf_coe_preimage {A : Set (WithTop R)} (hA : BddBelow A) :
    _root_.InfSet.sInf A = _root_.InfSet.sInf ((fun r : R => (r : WithTop R)) ''
      ((fun r : R => (r : WithTop R)) ⁻¹' A)) := by
  have hB := Monotone.map_bddBelow WithTop.coe_mono (bddBelow_coe_preimage hA)
  have hlower : lowerBounds A = lowerBounds ((fun r : R => (r : WithTop R)) ''
      ((fun r : R => (r : WithTop R)) ⁻¹' A)) := by
    ext x
    constructor
    · intro hx y hy
      obtain ⟨r, hr, rfl⟩ := hy
      exact hx hr
    · intro hx y hy
      cases y using WithTop.recTopCoe with
      | top => exact le_top
      | coe r => exact hx ⟨r, hy, rfl⟩
  apply (WithTop.isGLB_sInf' hA).unique
  change IsGreatest (lowerBounds A) _
  rw [hlower]
  exact WithTop.isGLB_sInf' hB

run_cmd do
  let target := ``Submission.WithTop.sInf_eq_sInf_coe_preimage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `WithTop.sInf_eq_sInf_coe_preimage target :: scope.openDecls } }

end

open _root_.WithTop in
theorem sInf_add {R : Type*} [ConditionallyCompleteLattice R] [AddCommGroup R]
    [IsOrderedAddMonoid R] {A B : Set (WithTop R)} (hA : BddBelow A) (hB : BddBelow B) :
    sInf A + _root_.InfSet.sInf B = _root_.InfSet.sInf (Set.image2 (fun a b : WithTop R => a + b) A B) := by
  let A₀ : Set R := (fun r : R => (r : WithTop R)) ⁻¹' A
  let B₀ : Set R := (fun r : R => (r : WithTop R)) ⁻¹' B
  have hAB : BddBelow (Set.image2 (fun a b : WithTop R => a + b) A B) := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    refine ⟨a + b, ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact add_le_add (ha hx) (hb hy)
  have hpre : (fun r : R => (r : WithTop R)) ⁻¹'
      Set.image2 (fun a b : WithTop R => a + b) A B = Set.image2 (fun a b : R => a + b) A₀ B₀ := by
    ext r
    constructor
    · rintro ⟨x, hx, y, hy, hxy⟩
      cases x using WithTop.recTopCoe with
      | top => simp only [WithTop.top_add, WithTop.top_ne_coe] at hxy
      | coe x =>
        cases y using WithTop.recTopCoe with
        | top => simp only [WithTop.add_top, WithTop.top_ne_coe] at hxy
        | coe y => exact ⟨x, hx, y, hy, WithTop.coe_injective hxy⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨(x : WithTop R), hx, (y : WithTop R), hy, rfl⟩
  rw [sInf_eq_sInf_coe_preimage hA, sInf_eq_sInf_coe_preimage hB,
    sInf_eq_sInf_coe_preimage hAB, hpre]
  exact WithTop.sInf_coe_image_add (bddBelow_coe_preimage hA) (bddBelow_coe_preimage hB)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `WithTop.sInf_add then
    throwError "Refusing to shadow existing declaration WithTop.sInf_add"
  Lean.modifyEnv fun env => Lean.addAlias env `WithTop.sInf_add ``Submission.WithTop.sInf_add

end WithTop
