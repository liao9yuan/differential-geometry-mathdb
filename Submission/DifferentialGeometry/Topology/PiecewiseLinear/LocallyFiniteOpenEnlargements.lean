/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.LocallyFinite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology

theorem exists_locallyFinite_open_supersets {X ι : Type*} [TopologicalSpace X]
    [ParacompactSpace X] {F : ι → Set X} (hF : LocallyFinite F) :
    ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, F i ⊆ V i) ∧ LocallyFinite V := by
  classical
  choose A hA hfin using hF
  choose O hOA hO hxO using fun x => mem_nhds_iff.mp (hA x)
  obtain ⟨B, hB, hcover, hBloc, hBO⟩ := precise_refinement_set isClosed_univ O hO
    (fun x _ => mem_iUnion.mpr ⟨x, hxO x⟩)
  let V : ι → Set X := fun i => ⋃ x ∈ {x | (F i ∩ B x).Nonempty}, B x
  refine ⟨V, fun _ => isOpen_iUnion fun x => isOpen_iUnion fun _ => hB x, ?_, ?_⟩
  · intro i x hx
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hcover (_root_.Set.mem_univ x))
    exact mem_iUnion₂.mpr ⟨y, ⟨x, hx, hy⟩, hy⟩
  · intro x
    obtain ⟨N, hN, hfinite⟩ := hBloc x
    refine ⟨N, hN, (hfinite.biUnion fun y _ => hfin y).subset ?_⟩
    rintro i ⟨z, hz, hzN⟩
    obtain ⟨y, ⟨v, hvF, hvB⟩, hzB⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨y, ⟨z, hzB, hzN⟩, ⟨v, hvF, hOA y (hBO y hvB)⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_locallyFinite_open_supersets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_locallyFinite_open_supersets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_locallyFinite_open_supersets ``Submission.DifferentialGeometry.Topology.exists_locallyFinite_open_supersets

end DifferentialGeometry.Topology
