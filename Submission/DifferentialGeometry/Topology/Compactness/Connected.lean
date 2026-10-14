import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Set

namespace DifferentialGeometry.Topology

theorem sigmaCompactSpace_of_preconnected (X : Type*) [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [ParacompactSpace X]
    [PreconnectedSpace X] : SigmaCompactSpace X := by
  classical
  cases isEmpty_or_nonempty X with
  | inl h =>
      let _ := h
      exact inferInstance
  | inr h =>
      let _ := h
      choose K hKc hKn using fun x : X => _root_.WeaklyLocallyCompactSpace.exists_compact_mem_nhds x
      obtain ⟨V, hVo, hVcov, hVfin, hVK⟩ := precise_refinement
        (fun x => interior (K x)) (fun _ => isOpen_interior)
        (iUnion_eq_univ_iff.mpr fun x => ⟨x, mem_interior_iff_mem_nhds.mpr (hKn x)⟩)
      have hVK' : ∀ i, V i ⊆ K i := fun i => (hVK i).trans interior_subset
      let N : X → Set X := fun i => {j | (V j ∩ K i).Nonempty}
      have hN : ∀ i, (N i).Finite := fun i =>
        hVfin.finite_nonempty_inter_compact (hKc i)
      obtain ⟨i₀, hi₀⟩ := iUnion_eq_univ_iff.mp hVcov (Classical.arbitrary X)
      let F : ℕ → Set X := fun n => Nat.rec {i₀} (fun _ s => ⋃ i ∈ s, N i) n
      have hF : ∀ n, (F n).Finite := by
        intro n
        induction n with
        | zero => exact _root_.Set.finite_singleton i₀
        | succ n ih => exact ih.biUnion fun i _ => hN i
      let S : Set X := ⋃ n, F n
      have hSc : S.Countable := _root_.Set.countable_iUnion fun n => (hF n).countable
      have hSN : ∀ i ∈ S, N i ⊆ S := by
        intro i hi j hj
        obtain ⟨n, hn⟩ := mem_iUnion.mp hi
        exact mem_iUnion.mpr ⟨n + 1, mem_iUnion₂.mpr ⟨i, hn, hj⟩⟩
      have hi₀S : i₀ ∈ S := mem_iUnion.mpr ⟨0, _root_.Set.mem_singleton i₀⟩
      have hSall : ∀ j, (V j).Nonempty → j ∈ S := by
        intro j hj
        have hpre : IsPreconnected (⋃ i, V i) := by
          rw [hVcov]
          exact _root_.PreconnectedSpace.isPreconnected_univ
        have hpath := hpre.transGen_of_iUnion hVo
          i₀ j ⟨Classical.arbitrary X, hi₀⟩ hj
        induction hpath with
        | single hij =>
            obtain ⟨x, hxi, hxj⟩ := hij
            exact hSN i₀ hi₀S ⟨x, hxj, hVK' i₀ hxi⟩
        | @tail i j _ hij ih =>
            obtain ⟨x, hxi, hxj⟩ := hij
            exact hSN i (ih ⟨x, hxi⟩) ⟨x, hxj, hVK' i hxi⟩
      have hKcov : (⋃ i : S, K i) = univ := by
        apply iUnion_eq_univ_iff.mpr
        intro x
        obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hVcov x
        exact ⟨⟨j, hSall j ⟨x, hj⟩⟩, hVK' j hj⟩
      have : Countable S := hSc.to_subtype
      apply isSigmaCompact_univ_iff.mp
      rw [← hKcov]
      exact isSigmaCompact_iUnion_of_isCompact _ (fun i : S => hKc i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sigmaCompactSpace_of_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sigmaCompactSpace_of_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sigmaCompactSpace_of_preconnected ``Submission.DifferentialGeometry.Topology.sigmaCompactSpace_of_preconnected

end DifferentialGeometry.Topology

end
