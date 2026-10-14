import Submission.DifferentialGeometry.Topology.Manifold.NormalOrientationCover
import Submission.DifferentialGeometry.Topology.Covering.BoolCocyclePullback
import Submission.DifferentialGeometry.Topology.Manifold.NormalSideParity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter _root_.Set _root_.Topology

noncomputable section

universe u v

namespace DifferentialGeometry.Topology.EmbeddingRealNormalAtlas

variable {B : Type u} {A : Type v} [TopologicalSpace B] [TopologicalSpace A]
  {f : B → A} (C : EmbeddingRealNormalAtlas f)

private def ambientBaseSet : Option B → Set A
  | none => (Set.range f)ᶜ
  | some i => C.chart i '' ((C.chart i).source ∩ (C.baseSet i ×ˢ Set.univ))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientBaseSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientBaseSet target :: scope.openDecls } }

private def ambientSide : Option B → A → Bool
  | none, _ => _root_.Bool.false
  | some i, a => realNormalSide ((C.chart i).symm a).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientSide
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientSide target :: scope.openDecls } }

private def ambientParity (i j : Option B) (a : A) : Bool := by
  classical
  exact if ha : a ∈ Set.range f then
    match i, j with
    | some i, _root_.Option.some j => C.transitionParity i j (Classical.choose ha)
    | _, _ => _root_.Bool.false
  else Bool.xor (C.ambientSide i a) (C.ambientSide j a)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientParity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientParity target :: scope.openDecls } }

private theorem apply_mem_ambientBaseSet_some {i x : B} (hx : x ∈ C.baseSet i) :
    f x ∈ C.ambientBaseSet (_root_.Option.some i) := by
  exact ⟨(x, 0), ⟨C.zero_mem_source i hx, hx, Set.mem_univ 0⟩, C.apply_zero i hx⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.apply_mem_ambientBaseSet_some
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.apply_mem_ambientBaseSet_some target :: scope.openDecls } }

private theorem mem_ambientBaseSet_some_iff {i : B} {a : A} :
    a ∈ C.ambientBaseSet (_root_.Option.some i) ↔
      a ∈ (C.chart i).target ∧ ((C.chart i).symm a).1 ∈ C.baseSet i := by
  constructor
  · rintro ⟨q, ⟨hq, hbase⟩, rfl⟩
    refine ⟨(C.chart i).map_source hq, ?_⟩
    rw [(C.chart i).left_inv hq]
    exact hbase.1
  · rintro ⟨ha, hbase⟩
    exact ⟨(C.chart i).symm a,
      ⟨(C.chart i).map_target ha, hbase, Set.mem_univ _⟩,
      (C.chart i).right_inv ha⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.mem_ambientBaseSet_some_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.mem_ambientBaseSet_some_iff target :: scope.openDecls } }

private theorem symm_apply_f_of_mem_ambientBaseSet_some
    (hf : Function.Injective f) {i x : B}
    (hx : f x ∈ C.ambientBaseSet (_root_.Option.some i)) :
    x ∈ C.baseSet i ∧ (C.chart i).symm (f x) = (x, 0) := by
  rcases hx with ⟨q, ⟨hq, hbase⟩, hqfx⟩
  have hqzero : q.2 = 0 :=
    (C.range_iff_zero i q hq).mp ⟨x, hqfx.symm⟩
  have hqprod : q = (q.1, 0) := Prod.ext rfl hqzero
  have hqfirst : q.1 = x := by
    apply hf
    rw [← C.apply_zero i hbase.1, ← hqprod]
    exact hqfx
  constructor
  · simpa only [hqfirst] using hbase.1
  · rw [← hqfx, (C.chart i).left_inv hq, hqprod, hqfirst]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.symm_apply_f_of_mem_ambientBaseSet_some
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.symm_apply_f_of_mem_ambientBaseSet_some target :: scope.openDecls } }

private theorem apply_mem_ambientBaseSet_some_iff
    (hf : Function.Injective f) {i x : B} :
    f x ∈ C.ambientBaseSet (_root_.Option.some i) ↔ x ∈ C.baseSet i := by
  exact ⟨fun hx ↦ (C.symm_apply_f_of_mem_ambientBaseSet_some hf hx).1,
    C.apply_mem_ambientBaseSet_some⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.apply_mem_ambientBaseSet_some_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.apply_mem_ambientBaseSet_some_iff target :: scope.openDecls } }

private theorem ambientParity_apply_some
    (hf : Function.Injective f) (i j x : B) :
    C.ambientParity (_root_.Option.some i) (_root_.Option.some j) (f x) = C.transitionParity i j x := by
  have hx : f x ∈ Set.range f := ⟨x, rfl⟩
  have hchoose : Classical.choose hx = x := hf (Classical.choose_spec hx)
  simp only [ambientParity, dif_pos hx, hchoose]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientParity_apply_some
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientParity_apply_some target :: scope.openDecls } }

private theorem ambientParity_of_not_mem_range
    (i j : Option B) {a : A} (ha : a ∉ Set.range f) :
    C.ambientParity i j a = Bool.xor (C.ambientSide i a) (C.ambientSide j a) := by
  simp only [ambientParity, dif_neg ha]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientParity_of_not_mem_range
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientParity_of_not_mem_range target :: scope.openDecls } }

private theorem ambientParity_self
    (hf : Function.Injective f) (i : Option B) (a : A)
    (ha : a ∈ C.ambientBaseSet i) :
    C.ambientParity i i a = false := by
  by_cases hfrange : a ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hfrange
    cases i with
    | none => exact False.elim (ha ⟨x, rfl⟩)
    | some i =>
      rw [C.ambientParity_apply_some hf]
      exact C.transitionParity_self i
        ((C.apply_mem_ambientBaseSet_some_iff hf).mp ha)
  · rw [C.ambientParity_of_not_mem_range i i hfrange]
    exact Bool.xor_self _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientParity_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientParity_self target :: scope.openDecls } }

private theorem ambientParity_comp
    (hf : Function.Injective f) (i j k : Option B) (a : A)
    (ha : a ∈ C.ambientBaseSet i ∩ C.ambientBaseSet j ∩ C.ambientBaseSet k) :
    Bool.xor (C.ambientParity i j a) (C.ambientParity j k a) =
      C.ambientParity i k a := by
  by_cases hfrange : a ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hfrange
    cases i with
    | none => exact False.elim (ha.1.1 ⟨x, rfl⟩)
    | some i =>
      cases j with
      | none => exact False.elim (ha.1.2 ⟨x, rfl⟩)
      | some j =>
        cases k with
        | none => exact False.elim (ha.2 ⟨x, rfl⟩)
        | some k =>
          rw [C.ambientParity_apply_some hf, C.ambientParity_apply_some hf,
            C.ambientParity_apply_some hf]
          exact C.transitionParity_comp i j k
            ⟨⟨(C.apply_mem_ambientBaseSet_some_iff hf).mp ha.1.1,
              (C.apply_mem_ambientBaseSet_some_iff hf).mp ha.1.2⟩,
              (C.apply_mem_ambientBaseSet_some_iff hf).mp ha.2⟩
  · rw [C.ambientParity_of_not_mem_range i j hfrange,
      C.ambientParity_of_not_mem_range j k hfrange,
      C.ambientParity_of_not_mem_range i k hfrange]
    cases C.ambientSide i a <;> cases C.ambientSide j a <;>
      cases C.ambientSide k a <;> rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientParity_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientParity_comp target :: scope.openDecls } }


private theorem isOpen_ambientBaseSet (hclosed : IsClosed (_root_.Set.range f)) (i : Option B) :
    IsOpen (C.ambientBaseSet i) := by
  cases i with
  | none => exact hclosed.isOpen_compl
  | some i =>
    exact (C.chart i).isOpen_image_source_inter
      ((C.isOpen_baseSet i).prod isOpen_univ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.isOpen_ambientBaseSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.isOpen_ambientBaseSet target :: scope.openDecls } }

private theorem ambientBaseSet_cover (a : A) : ∃ i, a ∈ C.ambientBaseSet i := by
  by_cases ha : a ∈ _root_.Set.range f
  · obtain ⟨x, rfl⟩ := ha
    exact ⟨some x, C.apply_mem_ambientBaseSet_some (C.mem_baseSet_self x)⟩
  · exact ⟨none, ha⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientBaseSet_cover
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientBaseSet_cover target :: scope.openDecls } }

private theorem continuousOn_ambientSide_compl (i : Option B) :
    ContinuousOn (C.ambientSide i) (C.ambientBaseSet i ∩ (_root_.Set.range f)ᶜ) := by
  cases i with
  | none => exact continuousOn_const
  | some i =>
    intro a ha
    have ht : a ∈ (C.chart i).target :=
      ((C.mem_ambientBaseSet_some_iff).mp ha.1).1
    have hn : ((C.chart i).symm a).2 ≠ 0 := by
      intro hzero
      apply ha.2
      have hr := (C.range_iff_zero i _ ((C.chart i).map_target ht)).mpr hzero
      rwa [(C.chart i).right_inv ht] at hr
    exact ((continuousAt_realNormalSide hn).comp
      (f := fun a => ((C.chart i).symm a).2)
      ((C.chart i).symm.continuousAt ht).snd).continuousWithinAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.continuousOn_ambientSide_compl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.continuousOn_ambientSide_compl target :: scope.openDecls } }

private def ambientTransitionPoint (i j : B)
    (a : (C.ambientBaseSet (_root_.Option.some i) ∩ C.ambientBaseSet (_root_.Option.some j) : Set A)) :
    (C.transition i j).source :=
  ⟨(C.chart i).symm a, by
    have hi := (C.mem_ambientBaseSet_some_iff).mp a.property.1
    have hj := (C.mem_ambientBaseSet_some_iff).mp a.property.2
    change (C.chart i).symm a ∈ (C.chart i).source ∧
      C.chart i ((C.chart i).symm a) ∈ (C.chart j).target
    exact ⟨(C.chart i).map_target hi.1, by rw [(C.chart i).right_inv hi.1]; exact hj.1⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientTransitionPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientTransitionPoint target :: scope.openDecls } }

private theorem continuous_ambientTransitionPoint (i j : B) :
    Continuous (C.ambientTransitionPoint i j) := by
  apply Continuous.subtype_mk
  exact (C.chart i).symm.continuousOn.comp_continuous continuous_subtype_val
    (fun a ↦ ((C.mem_ambientBaseSet_some_iff).mp a.property.1).1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.continuous_ambientTransitionPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.continuous_ambientTransitionPoint target :: scope.openDecls } }

private theorem extendedNormalParity_ambientTransitionPoint
    (hf : Function.Injective f) (i j : B)
    (a : (C.ambientBaseSet (_root_.Option.some i) ∩ C.ambientBaseSet (_root_.Option.some j) : Set A)) :
    OpenPartialHomeomorph.extendedNormalParity (C.transition i j)
        (C.transition_zeroLocus_iff_zero i j) (C.ambientTransitionPoint i j a) =
      C.ambientParity (_root_.Option.some i) (_root_.Option.some j) a := by
  rcases a with ⟨a, ha⟩
  by_cases hfrange : a ∈ _root_.Set.range f
  · obtain ⟨x, rfl⟩ := hfrange
    have hi := C.symm_apply_f_of_mem_ambientBaseSet_some hf ha.1
    have hj := C.symm_apply_f_of_mem_ambientBaseSet_some hf ha.2
    rw [C.ambientParity_apply_some hf,
      C.transitionParity_eq_normalSideFlipAt ⟨hi.1, hj.1⟩]
    have hpoint : C.ambientTransitionPoint i j ⟨f x, ha⟩ =
        ⟨(x, 0), C.zero_mem_transition_source hi.1 hj.1⟩ :=
      Subtype.ext hi.2
    rw [hpoint, OpenPartialHomeomorph.extendedNormalParity_zero]
    rfl
  · have hi := (C.mem_ambientBaseSet_some_iff).mp ha.1
    have hn : ((C.chart i).symm a).2 ≠ 0 := by
      intro hzero
      apply hfrange
      have hr := (C.range_iff_zero i _ ((C.chart i).map_target hi.1)).mpr hzero
      rwa [(C.chart i).right_inv hi.1] at hr
    rw [OpenPartialHomeomorph.extendedNormalParity_of_ne_zero _ _ _ hn,
      C.ambientParity_of_not_mem_range (_root_.Option.some i) (_root_.Option.some j) hfrange]
    change Bool.xor (realNormalSide ((C.chart i).symm a).2)
        (realNormalSide ((C.chart j).symm (C.chart i ((C.chart i).symm a))).2) =
      Bool.xor (realNormalSide ((C.chart i).symm a).2)
        (realNormalSide ((C.chart j).symm a).2)
    rw [(C.chart i).right_inv hi.1]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.extendedNormalParity_ambientTransitionPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.extendedNormalParity_ambientTransitionPoint target :: scope.openDecls } }

private theorem continuousOn_ambientParity
    (hf : Function.Injective f) (i j : Option B) :
    ContinuousOn (C.ambientParity i j) (C.ambientBaseSet i ∩ C.ambientBaseSet j) := by
  cases i with
  | none =>
    have hj : ContinuousOn (C.ambientSide j)
        (C.ambientBaseSet _root_.Option.none ∩ C.ambientBaseSet j) :=
      (C.continuousOn_ambientSide_compl j).mono (fun _ ha ↦ ⟨ha.2, ha.1⟩)
    apply hj.congr
    intro a ha
    rw [C.ambientParity_of_not_mem_range _root_.Option.none j ha.1]
    exact Bool.false_xor _
  | some i =>
    cases j with
    | none =>
      apply (C.continuousOn_ambientSide_compl (_root_.Option.some i)).congr
      intro a ha
      rw [C.ambientParity_of_not_mem_range (_root_.Option.some i) _root_.Option.none ha.2]
      exact Bool.xor_false _
    | some j =>
      rw [continuousOn_iff_continuous_domRestrict]
      apply ((OpenPartialHomeomorph.continuous_extendedNormalParity
        (C.transition i j) (C.transition_zeroLocus_iff_zero i j)).comp
        (C.continuous_ambientTransitionPoint i j)).congr
      intro a
      exact C.extendedNormalParity_ambientTransitionPoint hf i j a

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.continuousOn_ambientParity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.continuousOn_ambientParity target :: scope.openDecls } }

def ambientBoolCocycle (hf : Function.Injective f) (hclosed : IsClosed (_root_.Set.range f)) :
    BoolCocycle (Option B) A where
  baseSet := C.ambientBaseSet
  isOpen_baseSet := C.isOpen_ambientBaseSet hclosed
  indexAt a := Classical.choose (C.ambientBaseSet_cover a)
  mem_baseSet_at a := Classical.choose_spec (C.ambientBaseSet_cover a)
  parity := C.ambientParity
  parity_self := C.ambientParity_self hf
  continuousOn_parity := C.continuousOn_ambientParity hf
  parity_comp := C.ambientParity_comp hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientBoolCocycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientBoolCocycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientBoolCocycle ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientBoolCocycle

theorem ambientBoolCocycle_parity_apply_some
    (hf : Function.Injective f) (hclosed : IsClosed (_root_.Set.range f)) (i j x : B) :
    (C.ambientBoolCocycle hf hclosed).parity (_root_.Option.some i) (_root_.Option.some j) (f x) =
      C.transitionParity i j x :=
  C.ambientParity_apply_some hf i j x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientBoolCocycle_parity_apply_some then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientBoolCocycle_parity_apply_some"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientBoolCocycle_parity_apply_some ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.ambientBoolCocycle_parity_apply_some

theorem preimage_ambientBoolCocycle_baseSet_some
    (hf : Function.Injective f) (hclosed : IsClosed (_root_.Set.range f)) (i : B) :
    f ⁻¹' (C.ambientBoolCocycle hf hclosed).baseSet (_root_.Option.some i) = C.baseSet i := by
  ext x
  exact C.apply_mem_ambientBaseSet_some_iff hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.preimage_ambientBoolCocycle_baseSet_some then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.preimage_ambientBoolCocycle_baseSet_some"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.preimage_ambientBoolCocycle_baseSet_some ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.preimage_ambientBoolCocycle_baseSet_some

theorem nonempty_coorientation_of_simplyConnected_ambient
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (hf : _root_.Topology.IsEmbedding f) (hclosed : IsClosed (_root_.Set.range f)) :
    Nonempty C.toBoolCocycle.Coorientation := by
  let D := C.ambientBoolCocycle hf.injective hclosed
  exact BoolCocycle.nonempty_coorientation_of_simplyConnected_pullback
    (C := C.toBoolCocycle) (D := D) f hf.continuous _root_.Option.some
    (fun _ _ hx ↦ C.apply_mem_ambientBaseSet_some hx)
    (fun i j x _ ↦ C.ambientParity_apply_some hf.injective i j x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.nonempty_coorientation_of_simplyConnected_ambient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.nonempty_coorientation_of_simplyConnected_ambient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.nonempty_coorientation_of_simplyConnected_ambient ``Submission.DifferentialGeometry.Topology.EmbeddingRealNormalAtlas.nonempty_coorientation_of_simplyConnected_ambient

end DifferentialGeometry.Topology.EmbeddingRealNormalAtlas
