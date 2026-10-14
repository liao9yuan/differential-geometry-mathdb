import Submission.DifferentialGeometry.Topology.Homology.Local.PointRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

section charted

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem relπ_compl_eq_zero_of_forall_ptRes (hn : 1 ≤ n) {A : Set M} (hA : IsCompact A)
    (c : singularHomology R (TopCat.of M) n) (h : ∀ x ∈ A, ptRes R (TopCat.of M) n c x = 0) :
    relπ R (TopCat.of M) Aᶜ n c = 0 :=
  (localGood.of_isCompact R hn hA).2 _ fun x hx => by
    rw [ptRes_res R hx n c]
    exact h x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relπ_compl_eq_zero_of_forall_ptRes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relπ_compl_eq_zero_of_forall_ptRes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relπ_compl_eq_zero_of_forall_ptRes ``Submission.DifferentialGeometry.Topology.SingularPair.relπ_compl_eq_zero_of_forall_ptRes

theorem eq_zero_of_forall_ptRes [CompactSpace M] (hn : 1 ≤ n) (c : singularHomology R (TopCat.of M) n)
    (h : ∀ x, ptRes R (TopCat.of M) n c x = 0) : c = 0 := by
  have h0 := relπ_compl_eq_zero_of_forall_ptRes R hn isCompact_univ c fun x _ => h x
  rw [Set.compl_univ] at h0
  have hmono : _root_.CategoryTheory.Mono (relπ R (TopCat.of M) ∅ n) := by
    have := isIso_relπ_empty R (TopCat.of M) n
    infer_instance
  exact ((ModuleCat.mono_iff_injective (relπ R (TopCat.of M) ∅ n)).1 hmono)
    (h0.trans (map_zero _).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.eq_zero_of_forall_ptRes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.eq_zero_of_forall_ptRes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.eq_zero_of_forall_ptRes ``Submission.DifferentialGeometry.Topology.SingularPair.eq_zero_of_forall_ptRes

theorem mono_relπ_compl_singleton (hn : 1 ≤ n) [CompactSpace M] [ConnectedSpace M] (x : M) :
    Mono (relπ R (TopCat.of M) {x}ᶜ n) := by
  rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro c hc
  exact eq_zero_of_forall_ptRes R hn c (ptRes_eq_zero_of_exists R hn c ⟨x, hc⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mono_relπ_compl_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mono_relπ_compl_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mono_relπ_compl_singleton ``Submission.DifferentialGeometry.Topology.SingularPair.mono_relπ_compl_singleton

theorem ptRes_injective (hn : 1 ≤ n) [CompactSpace M] [ConnectedSpace M] (x : M) :
    Function.Injective fun c : singularHomology R (TopCat.of M) n => ptRes R (TopCat.of M) n c x :=
  (ModuleCat.mono_iff_injective _).1 (mono_relπ_compl_singleton R hn x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ptRes_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ptRes_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ptRes_injective ``Submission.DifferentialGeometry.Topology.SingularPair.ptRes_injective

end charted

end DifferentialGeometry.Topology.SingularPair

end
