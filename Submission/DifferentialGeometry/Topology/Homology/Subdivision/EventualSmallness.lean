import Submission.DifferentialGeometry.Topology.Homology.Subdivision.SimplexSmallness
import Mathlib.LinearAlgebra.Quotient.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial

universe u v

namespace DifferentialGeometry.Homology

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)
  (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)

local notation "K" => _root_.SSet.chainComplex (TopCat.toSSet.obj X) R

private def eventuallySmallChainSubmodule (n : ℕ) : Submodule k ((K).X n) where
  carrier := {c | ∃ N : ℕ, ∀ m ≥ N,
    (End.of (singularSubdivision R X) ^ m).f n c ∈
      LinearMap.range ((smallChainMap X U R).f n).hom}
  zero_mem' := ⟨0, fun _ _ ↦ by rw [map_zero]; exact Submodule.zero_mem _⟩
  add_mem' := by
    rintro c d ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨max N M, fun m hm ↦ ?_⟩
    rw [map_add]
    exact Submodule.add_mem _ (hN m ((le_max_left _ _).trans hm))
      (hM m ((le_max_right _ _).trans hm))
  smul_mem' := by
    rintro a c ⟨N, hN⟩
    refine ⟨N, fun m hm ↦ ?_⟩
    rw [map_smul]
    exact Submodule.smul_mem _ a (hN m hm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.eventuallySmallChainSubmodule
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.eventuallySmallChainSubmodule target :: scope.openDecls } }

private theorem singularChain_submodule_eq_top {n : ℕ} (P : Submodule k ((K).X n))
    (hP : ∀ (σ : TopCat.toSSet.obj X _⦋n⦌) (r : R),
      (TopCat.toSSet.obj X).ιChainComplex (R := R) σ r ∈ P) : P = ⊤ := by
  let q : (K).X n ⟶ ModuleCat.of k (((K).X n) ⧸ P) := ModuleCat.ofHom P.mkQ
  have hq : q = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change P.mkQ ((TopCat.toSSet.obj X).ιChainComplex (R := R) σ r) = 0
    exact (Submodule.Quotient.mk_eq_zero P).mpr (hP σ r)
  apply top_unique
  intro c _
  have hc := congrArg (fun f ↦ ModuleCat.Hom.hom f c) hq
  exact (Submodule.Quotient.mk_eq_zero P).mp hc

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.singularChain_submodule_eq_top
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.singularChain_submodule_eq_top target :: scope.openDecls } }

theorem exists_eventually_small_subdivision_power
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (n : ℕ) (c : (K).X n) :
    ∃ N : ℕ, ∀ m ≥ N,
      (End.of (singularSubdivision R X) ^ m).f n c ∈
        LinearMap.range ((smallChainMap X U R).f n).hom := by
  have htop : eventuallySmallChainSubmodule R X U n = ⊤ := by
    apply singularChain_submodule_eq_top
    intro σ r
    obtain ⟨N, hN⟩ := exists_small_subdivision_power_generator R X U hopen hcover σ
    exact ⟨N, fun m hm ↦ hN m hm r⟩
  have hc : c ∈ eventuallySmallChainSubmodule R X U n := by rw [htop]; trivial
  exact hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.exists_eventually_small_subdivision_power then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.exists_eventually_small_subdivision_power"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.exists_eventually_small_subdivision_power ``Submission.DifferentialGeometry.Homology.exists_eventually_small_subdivision_power

theorem exists_small_subdivision_power
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (n : ℕ) (c : (K).X n) :
    ∃ N : ℕ, (End.of (singularSubdivision R X) ^ N).f n c ∈
      LinearMap.range ((smallChainMap X U R).f n).hom := by
  obtain ⟨N, hN⟩ := exists_eventually_small_subdivision_power R X U hopen hcover n c
  exact ⟨N, hN N le_rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.exists_small_subdivision_power then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.exists_small_subdivision_power"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.exists_small_subdivision_power ``Submission.DifferentialGeometry.Homology.exists_small_subdivision_power

end DifferentialGeometry.Homology
