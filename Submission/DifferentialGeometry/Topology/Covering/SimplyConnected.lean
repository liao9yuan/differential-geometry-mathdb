import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Function
open scoped _root_.Manifold _root_.ContDiff

noncomputable section

namespace IsLocalHomeomorph
open _root_.IsLocalHomeomorph

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}

open _root_.IsLocalHomeomorph in
theorem surjective_compact
    [CompactSpace E] [Nonempty E] [T2Space X] [ConnectedSpace X]
    (hf : IsLocalHomeomorph f) : Function.Surjective f := by
  have hopen : IsOpen (Set.range f) := by
    rw [← Set.image_univ]
    exact hf.isOpenMap Set.univ isOpen_univ
  have hclosed : IsClosed (Set.range f) :=
    (isCompact_range hf.continuous).isClosed
  have hrange : Set.range f = Set.univ :=
    (show IsClopen (Set.range f) from ⟨hclosed, hopen⟩).eq_univ
      (Set.range_nonempty f)
  intro x
  have hx : x ∈ Set.range f := by
    rw [hrange]
    exact Set.mem_univ x
  exact hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsLocalHomeomorph.surjective_compact then
    throwError "Refusing to shadow existing declaration IsLocalHomeomorph.surjective_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalHomeomorph.surjective_compact ``Submission.IsLocalHomeomorph.surjective_compact

open _root_.IsLocalHomeomorph in
theorem covering_compact
    [CompactSpace E] [T2Space E] [T2Space X]
    (hf : IsLocalHomeomorph f) : IsCoveringMap f := by
  exact isLocalHomeomorph_iff_isCoveringMap.mp hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsLocalHomeomorph.covering_compact then
    throwError "Refusing to shadow existing declaration IsLocalHomeomorph.covering_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalHomeomorph.covering_compact ``Submission.IsLocalHomeomorph.covering_compact

end IsLocalHomeomorph

namespace IsCoveringMap
open _root_.IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}

open _root_.IsCoveringMap in
theorem bijective_sc
    [PreconnectedSpace E] [Nonempty E]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (hf : IsCoveringMap f) : Function.Bijective f := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  obtain ⟨s, ⟨hs0, hsp⟩, -⟩ :=
    hf.existsUnique_continuousMap_lifts (ContinuousMap.id X) (f e₀) e₀ rfl
  have hfs : Function.RightInverse s f := by
    intro x
    have h := congrFun hsp x
    simpa using h
  refine ⟨?_, hfs.surjective⟩
  have hsf : (⇑s ∘ f) = id := by
    refine hf.eq_of_comp_eq
      (g₁ := ⇑s ∘ f) (g₂ := id)
      (s.continuous.comp hf.continuous) continuous_id ?_ e₀ ?_
    · funext e
      simp only [Function.comp_apply, id_eq, hfs (f e)]
    · simp only [Function.comp_apply, id_eq, hs0]
  have hli : Function.LeftInverse s f := fun e => congrFun hsf e
  exact hli.injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoveringMap.bijective_sc then
    throwError "Refusing to shadow existing declaration IsCoveringMap.bijective_sc"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoveringMap.bijective_sc ``Submission.IsCoveringMap.bijective_sc

open _root_.IsCoveringMap in
noncomputable def homeomorphSc
    [PreconnectedSpace E] [Nonempty E]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (hf : IsCoveringMap f) : E ≃ₜ X :=
  (Equiv.ofBijective f hf.bijective_sc).toHomeomorphOfContinuousOpen
    hf.continuous hf.isOpenMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoveringMap.homeomorphSc then
    throwError "Refusing to shadow existing declaration IsCoveringMap.homeomorphSc"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoveringMap.homeomorphSc ``Submission.IsCoveringMap.homeomorphSc

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 F H}
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 F' H'}
variable [ChartedSpace H E] [IsManifold I ∞ E]
variable [ChartedSpace H' X] [IsManifold I' ∞ X]

open _root_.IsCoveringMap in
noncomputable def diffeomorphSc
    [PreconnectedSpace E] [Nonempty E]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (hf : IsCoveringMap f) (hloc : IsLocalDiffeomorph I I' ∞ f) :
    Diffeomorph I I' E X ∞ :=
  hloc.diffeomorphOfBijective hf.bijective_sc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoveringMap.diffeomorphSc then
    throwError "Refusing to shadow existing declaration IsCoveringMap.diffeomorphSc"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoveringMap.diffeomorphSc ``Submission.IsCoveringMap.diffeomorphSc

omit [IsManifold I ∞ E] [IsManifold I' ∞ X] in
open _root_.IsCoveringMap in
@[simp] theorem coe_diffeomorph_sc
    [PreconnectedSpace E] [Nonempty E]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (hf : IsCoveringMap f) (hloc : IsLocalDiffeomorph I I' ∞ f) :
    ⇑(hf.diffeomorphSc hloc) = f := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoveringMap.coe_diffeomorph_sc then
    throwError "Refusing to shadow existing declaration IsCoveringMap.coe_diffeomorph_sc"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoveringMap.coe_diffeomorph_sc ``Submission.IsCoveringMap.coe_diffeomorph_sc

end Smooth

end IsCoveringMap

end
