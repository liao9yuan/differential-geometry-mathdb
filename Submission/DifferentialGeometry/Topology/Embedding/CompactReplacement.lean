import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Separation.Hausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace Topology.IsEmbedding
open _root_.Topology _root_.Topology.IsEmbedding

variable {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z]

open _root_.Topology _root_.Topology.IsEmbedding in
theorem exists_replacement_of_isClosed
    {e g : X → Y} (he : _root_.Topology.IsEmbedding e) {D : Set X} (hD : IsClosed D)
    (hg : ContinuousOn g D) (hginj : _root_.Set.InjOn g D)
    (hboundary : _root_.Set.EqOn g e (frontier D))
    (hdisj : Disjoint (g '' D) (e '' Dᶜ)) :
    ∃ f : X → Y, _root_.Topology.IsEmbedding f ∧ _root_.Set.EqOn f g D ∧ _root_.Set.EqOn f e Dᶜ ∧
      range f = g '' D ∪ e '' Dᶜ := by
  classical
  let f := D.piecewise g e
  have hf : Continuous f := continuous_piecewise hboundary
    (hD.closure_eq.symm ▸ hg) he.continuous.continuousOn
  have hfinj : Function.Injective f := (_root_.Set.injective_piecewise_iff D).mpr
    ⟨hginj, he.injective.injOn, fun x hx y hy hxy =>
      disjoint_left.mp hdisj (_root_.Set.mem_image_of_mem g hx) ⟨y, hy, hxy.symm⟩⟩
  exact ⟨f, (hf.isClosedEmbedding hfinj).isEmbedding,
    _root_.Set.piecewise_eqOn D g e, _root_.Set.piecewise_eqOn_compl D g e, _root_.Set.range_piecewise D g e⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Topology.IsEmbedding.exists_replacement_of_isClosed then
    throwError "Refusing to shadow existing declaration Topology.IsEmbedding.exists_replacement_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `Topology.IsEmbedding.exists_replacement_of_isClosed ``Submission.Topology.IsEmbedding.exists_replacement_of_isClosed

open _root_.Topology _root_.Topology.IsEmbedding in
theorem exists_replacement_of_openPartialHomeomorph
    {e : X → Y} (he : _root_.Topology.IsEmbedding e)
    (φ : OpenPartialHomeomorph Z X) {K : Set Z} (hK : IsCompact K)
    (hKφ : K ⊆ φ.source) {g : Z → Y}
    (hg : ContinuousOn g K) (hginj : _root_.Set.InjOn g K)
    (hboundary : ∀ x ∈ frontier K, g x = e (φ x))
    (hdisj : Disjoint (g '' K) (e '' (φ '' K)ᶜ)) :
    ∃ f : X → Y, _root_.Topology.IsEmbedding f ∧ (∀ x ∈ K, f (φ x) = g x) ∧
      EqOn f e (φ '' K)ᶜ ∧ _root_.Set.range f = g '' K ∪ e '' (φ '' K)ᶜ := by
  let _ : T2Space X := he.t2Space
  let D := φ '' K
  have hDc : IsClosed D := (hK.image_of_continuousOn (φ.continuousOn.mono hKφ)).isClosed
  have hDφ : D ⊆ φ.target := fun _ hx => by
    obtain ⟨x, hx, rfl⟩ := hx
    exact φ.map_source (hKφ hx)
  have hφD : φ.IsImage K D := by
    intro x hx
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (φ.injOn (hKφ hy) hx hyx) ▸ hy
    · exact _root_.Set.mem_image_of_mem φ
  have hmaps : _root_.Set.MapsTo φ.symm D K := by
    intro y hy
    exact (hφD.symm (hDφ hy)).mpr hy
  have hboundary' : _root_.Set.EqOn (g ∘ φ.symm) e (frontier D) := by
    intro y hy
    have hyD : y ∈ D := hDc.closure_eq ▸ frontier_subset_closure hy
    have hx := (hφD.symm.frontier (hDφ hyD)).mpr hy
    change g (φ.symm y) = e y
    rw [hboundary (φ.symm y) hx, φ.right_inv (hDφ hyD)]
  have himage : (g ∘ φ.symm) '' D = g '' K := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact _root_.Set.mem_image_of_mem g (hmaps hx)
    · rintro ⟨x, hx, rfl⟩
      exact ⟨φ x, _root_.Set.mem_image_of_mem φ hx, congrArg g (φ.left_inv (hKφ hx))⟩
  obtain ⟨f, hf, hformula, hfix, hrange⟩ := he.exists_replacement_of_isClosed hDc
    (hg.comp (φ.symm.continuousOn.mono hDφ) hmaps)
    (hginj.comp (φ.symm.injOn.mono hDφ) hmaps)
    hboundary' (himage.symm ▸ hdisj)
  refine ⟨f, hf, ?_, hfix, hrange.trans ?_⟩
  · intro x hx
    exact (hformula (_root_.Set.mem_image_of_mem φ hx)).trans (congrArg g (φ.left_inv (hKφ hx)))
  · rw [himage]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Topology.IsEmbedding.exists_replacement_of_openPartialHomeomorph then
    throwError "Refusing to shadow existing declaration Topology.IsEmbedding.exists_replacement_of_openPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Topology.IsEmbedding.exists_replacement_of_openPartialHomeomorph ``Submission.Topology.IsEmbedding.exists_replacement_of_openPartialHomeomorph

end Topology.IsEmbedding
