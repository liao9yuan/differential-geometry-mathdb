import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.MonotoneContinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.TopologicalSpace

universe u v w

namespace DifferentialGeometry.Topology


private def realIooHomeomorph (a b : ℝ) (h : a < b) : ℝ ≃ₜ Set.Ioo a b := by
  let r := (b - a) / 2
  let c := (a + b) / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  exact (orderIsoIooNegOneOne ℝ).toHomeomorph.trans
    ((Homeomorph.image (affineHomeomorph r c hr.ne')
      (Set.Ioo (-1 : ℝ) 1)).trans
      (Homeomorph.setCongr (by
        rw [affineHomeomorph_image_Ioo r c (-1 : ℝ) 1 hr]
        congr 1 <;> dsimp [r, c] <;> ring)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.realIooHomeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.realIooHomeomorph target :: scope.openDecls } }

def piIooHomeomorph {ι : Type*} (a b : ι → ℝ) (h : ∀ i, a i < b i) :
    (ι → ℝ) ≃ₜ Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)) :=
  (Homeomorph.piCongrRight fun i => realIooHomeomorph (a i) (b i) (h i)).trans
    { toEquiv := (Equiv.Set.univPi fun i => Set.Ioo (a i) (b i)).symm
      continuous_toFun := (continuous_pi fun i =>
        continuous_subtype_val.comp (continuous_apply i)).subtype_mk _
      continuous_invFun := continuous_pi fun i =>
        ((continuous_apply i).comp continuous_subtype_val).subtype_mk _ }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.piIooHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.piIooHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.piIooHomeomorph ``Submission.DifferentialGeometry.Topology.piIooHomeomorph


theorem isTopologicalBasis_pi_Ioo {ι : Type u} [Finite ι] {X : ι → Type v}
    [∀ i, LinearOrder (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, OrderTopology (X i)] [∀ i, NoMinOrder (X i)] [∀ i, NoMaxOrder (X i)] :
    _root_.TopologicalSpace.IsTopologicalBasis {s : Set (∀ i, X i) |
      ∃ a b : ∀ i, X i, s = Set.pi Set.univ (fun i => Set.Ioo (a i) (b i))} := by
  refine _root_.TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro s ⟨a, b, rfl⟩
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  · intro x s hxs hs
    obtain ⟨U, hU, hUs⟩ := isOpen_pi_iff'.mp hs x hxs
    have hinterval : ∀ i, ∃ a b : X i, x i ∈ _root_.Set.Ioo a b ∧ _root_.Set.Ioo a b ⊆ U i :=
      fun i => mem_nhds_iff_exists_Ioo_subset.mp ((hU i).1.mem_nhds (hU i).2)
    choose a b hx hab using hinterval
    refine ⟨Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)), ⟨a, b, rfl⟩, ?_, ?_⟩
    · exact fun i _ => hx i
    · exact (Set.pi_mono fun i _ => hab i).trans hUs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isTopologicalBasis_pi_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isTopologicalBasis_pi_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isTopologicalBasis_pi_Ioo ``Submission.DifferentialGeometry.Topology.isTopologicalBasis_pi_Ioo



variable {ι κ : Type*}

private theorem pi_Ioo_inter (a b c d : ι → ℝ) :
    (univ.pi (fun i => _root_.Set.Ioo (a i) (b i))) ∩ (univ.pi (fun i => _root_.Set.Ioo (c i) (d i))) =
      univ.pi (fun i => _root_.Set.Ioo (_root_.Max.max (a i) (c i)) (_root_.Min.min (b i) (d i))) := by
  rw [← _root_.Set.pi_inter_distrib]
  congr 1
  funext i
  exact _root_.Set.Ioo_inter_Ioo

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.pi_Ioo_inter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.pi_Ioo_inter target :: scope.openDecls } }

private theorem exists_pi_Ioo_eq_biInter (s : Finset κ) (hs : s.Nonempty)
    (a b : κ → ι → ℝ) :
    ∃ c d : ι → ℝ, (⋂ j ∈ s, univ.pi (fun i => _root_.Set.Ioo (a j i) (b j i))) =
      univ.pi (fun i => _root_.Set.Ioo (c i) (d i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hs)
  | @insert j s hj ih =>
    by_cases h : s.Nonempty
    · obtain ⟨c, d, hcd⟩ := ih h
      refine ⟨fun i => _root_.Max.max (a j i) (c i), fun i => _root_.Min.min (b j i) (d i), ?_⟩
      rw [Finset.set_biInter_insert, hcd, pi_Ioo_inter]
    · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst s
      exact ⟨a j, b j, by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.exists_pi_Ioo_eq_biInter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.exists_pi_Ioo_eq_biInter target :: scope.openDecls } }


theorem nonempty_homeomorph_biInter_pi_Ioo (s : Finset κ) (a b : κ → ι → ℝ)
    (h : (⋂ j ∈ s, univ.pi (fun i => _root_.Set.Ioo (a j i) (b j i))).Nonempty) :
    Nonempty ((⋂ j ∈ s, univ.pi (fun i => _root_.Set.Ioo (a j i) (b j i))) ≃ₜ (ι → ℝ)) := by
  by_cases hs : s.Nonempty
  · obtain ⟨c, d, hcd⟩ := exists_pi_Ioo_eq_biInter s hs a b
    obtain ⟨x, hx⟩ := h
    rw [hcd] at hx
    have hab (i : ι) : c i < d i := (hx i (_root_.Set.mem_univ i)).1.trans (hx i (_root_.Set.mem_univ i)).2
    exact ⟨(Homeomorph.setCongr hcd).trans (piIooHomeomorph c d hab).symm⟩
  · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    exact ⟨(Homeomorph.setCongr (show (⋂ j ∈ (∅ : Finset κ),
      univ.pi (fun i => _root_.Set.Ioo (a j i) (b j i))) = _root_.Set.univ from by ext; simp)).trans
      (Homeomorph.Set.univ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_homeomorph_biInter_pi_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_homeomorph_biInter_pi_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_homeomorph_biInter_pi_Ioo ``Submission.DifferentialGeometry.Topology.nonempty_homeomorph_biInter_pi_Ioo


theorem exists_isTopologicalBasis_inter_homeomorph_of_homeomorph_pi
    {X : Type u} [TopologicalSpace X] [Finite ι] (e : X ≃ₜ (ι → ℝ)) :
    ∃ B : Set (Set X), _root_.TopologicalSpace.IsTopologicalBasis B ∧
      (∀ S ∈ B, ∀ T ∈ B, S ∩ T ∈ B) ∧
      ∀ S ∈ B, S.Nonempty → Nonempty (S ≃ₜ X) := by
  let A : Set (Set (ι → ℝ)) :=
    {S | ∃ a b : ι → ℝ, S = univ.pi (fun i => _root_.Set.Ioo (a i) (b i))}
  refine ⟨(_root_.Set.preimage e) '' A, isTopologicalBasis_pi_Ioo.isInducing e.isInducing, ?_, ?_⟩
  · rintro S ⟨S', ⟨a, b, rfl⟩, rfl⟩ T ⟨T', ⟨c, d, rfl⟩, rfl⟩
    refine ⟨univ.pi (fun i => _root_.Set.Ioo (_root_.Max.max (a i) (c i)) (_root_.Min.min (b i) (d i))),
      ⟨fun i => _root_.Max.max (a i) (c i), fun i => _root_.Min.min (b i) (d i), rfl⟩, ?_⟩
    rw [← _root_.Set.preimage_inter, pi_Ioo_inter]
  · rintro S ⟨S', ⟨a, b, rfl⟩, rfl⟩ ⟨x, hx⟩
    have hab (i : ι) : a i < b i := (hx i (_root_.Set.mem_univ i)).1.trans (hx i (_root_.Set.mem_univ i)).2
    exact ⟨(e.sets rfl).trans ((piIooHomeomorph a b hab).symm.trans e.symm)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_isTopologicalBasis_inter_homeomorph_of_homeomorph_pi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_isTopologicalBasis_inter_homeomorph_of_homeomorph_pi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_isTopologicalBasis_inter_homeomorph_of_homeomorph_pi ``Submission.DifferentialGeometry.Topology.exists_isTopologicalBasis_inter_homeomorph_of_homeomorph_pi


theorem exists_isTopologicalBasis_inter_homeomorph_of_finiteDimensional
    {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E] :
    ∃ B : Set (Set E), _root_.TopologicalSpace.IsTopologicalBasis B ∧
      (∀ S ∈ B, ∀ T ∈ B, S ∩ T ∈ B) ∧
      ∀ S ∈ B, S.Nonempty → Nonempty (S ≃ₜ E) :=
  exists_isTopologicalBasis_inter_homeomorph_of_homeomorph_pi
    (Module.finBasis ℝ E).equivFunL.toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_isTopologicalBasis_inter_homeomorph_of_finiteDimensional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_isTopologicalBasis_inter_homeomorph_of_finiteDimensional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_isTopologicalBasis_inter_homeomorph_of_finiteDimensional ``Submission.DifferentialGeometry.Topology.exists_isTopologicalBasis_inter_homeomorph_of_finiteDimensional

end DifferentialGeometry.Topology

end
