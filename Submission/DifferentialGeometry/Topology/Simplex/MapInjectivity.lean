import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Order.WellFounded

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
namespace stdSimplex
open _root_.stdSimplex

variable {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S]

open _root_.stdSimplex in
lemma map_apply_of_injective {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y} (hf : Function.Injective f)
    (p : stdSimplex S X) (x : X) :
    (stdSimplex.map f p) (f x) = p x := by
  classical
  change FunOnFinite.linearMap S S f p (f x) = p x
  rw [FunOnFinite.linearMap_apply_apply]
  rw [Finset.sum_eq_single x]
  · intro b hb hbx
    exact (hbx (hf (Finset.mem_filter.mp hb).2)).elim
  · simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `stdSimplex.map_apply_of_injective then
    throwError "Refusing to shadow existing declaration stdSimplex.map_apply_of_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `stdSimplex.map_apply_of_injective ``Submission.stdSimplex.map_apply_of_injective

open _root_.stdSimplex in
lemma map_apply_eq_zero_of_not_mem_range {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (p : stdSimplex S X) {y : Y} (hy : y ∉ Set.range f) :
    (stdSimplex.map f p) y = 0 := by
  classical
  change FunOnFinite.linearMap S S f p y = 0
  rw [FunOnFinite.linearMap_apply_apply]
  have h : ∀ x, f x ≠ y := fun x hxy => hy ⟨x, hxy⟩
  simp [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `stdSimplex.map_apply_eq_zero_of_not_mem_range then
    throwError "Refusing to shadow existing declaration stdSimplex.map_apply_eq_zero_of_not_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `stdSimplex.map_apply_eq_zero_of_not_mem_range ``Submission.stdSimplex.map_apply_eq_zero_of_not_mem_range

open _root_.stdSimplex in
lemma range_subset_of_map_eq_of_nonzero {X Y : Type*} [Fintype X] [Fintype Y]
    {f g : X → Y} (hf : Function.Injective f)
    {p q : stdSimplex S X} (hp : ∀ x, p x ≠ 0)
    (h : stdSimplex.map f p = stdSimplex.map g q) : Set.range f ⊆ Set.range g := by
  rintro y ⟨x, rfl⟩
  by_contra hx
  apply hp x
  rw [← map_apply_of_injective hf p x, h]
  exact map_apply_eq_zero_of_not_mem_range g q hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `stdSimplex.range_subset_of_map_eq_of_nonzero then
    throwError "Refusing to shadow existing declaration stdSimplex.range_subset_of_map_eq_of_nonzero"
  Lean.modifyEnv fun env => Lean.addAlias env `stdSimplex.range_subset_of_map_eq_of_nonzero ``Submission.stdSimplex.range_subset_of_map_eq_of_nonzero

open _root_.stdSimplex in
lemma map_injective {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (stdSimplex.map (S := S) f) := by
  intro p q h
  ext x
  have hx := DFunLike.congr_fun h (f x)
  simpa only [map_apply_of_injective hf] using hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `stdSimplex.map_injective then
    throwError "Refusing to shadow existing declaration stdSimplex.map_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `stdSimplex.map_injective ``Submission.stdSimplex.map_injective

open _root_.stdSimplex in
lemma eq_and_eq_of_map_eq_of_strictMono
    {X Y : Type*} [Fintype X] [Fintype Y] [LinearOrder X] [Preorder Y]
    {f g : X → Y}
    (hf : StrictMono f) (hg : StrictMono g)
    {p q : stdSimplex S X} (hp : ∀ x, p x ≠ 0)
    (h : stdSimplex.map f p = stdSimplex.map g q) : f = g ∧ p = q := by
  classical
  have hsub := range_subset_of_map_eq_of_nonzero hf.injective hp h
  have hcardf := Fintype.card_congr (Equiv.ofInjective f hf.injective)
  have hcardg := Fintype.card_congr (Equiv.ofInjective g hg.injective)
  have heq : Set.range f = Set.range g :=
    Set.eq_of_subset_of_card_le hsub (by omega)
  have hfg := hf.range_inj hg |>.mp heq
  refine ⟨hfg, ?_⟩
  subst g
  exact map_injective hf.injective h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `stdSimplex.eq_and_eq_of_map_eq_of_strictMono then
    throwError "Refusing to shadow existing declaration stdSimplex.eq_and_eq_of_map_eq_of_strictMono"
  Lean.modifyEnv fun env => Lean.addAlias env `stdSimplex.eq_and_eq_of_map_eq_of_strictMono ``Submission.stdSimplex.eq_and_eq_of_map_eq_of_strictMono

end stdSimplex
