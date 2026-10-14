import Submission.DifferentialGeometry.Topology.ProperMap.CompactSupport
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Separation.Hausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter
open scoped _root_.Topology

namespace Homeomorph
open _root_.Homeomorph

open _root_.Homeomorph in
theorem exists_piecewise_of_isClosed {X : Type*} [TopologicalSpace X] [T2Space X]
    {A U K : Set X} {f : X → X} (hA : IsClosed A) (hU : IsOpen U)
    (hf : ContinuousOn f (A ∩ U)) (hinj : _root_.Set.InjOn f (A ∩ U))
    (hmap : _root_.Set.MapsTo f (A ∩ U) U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hfixed : _root_.Set.EqOn f id ((A ∩ U) \ K)) :
    ∃ H : A ≃ₜ ↥((A \ U) ∪ f '' (A ∩ U)),
      (∀ x : A, x.val ∈ U → (H x).val = f x.val) ∧
      ∀ x : A, x.val ∉ K → (H x).val = x.val := by
  classical
  let F : X → X := U.piecewise f id
  have hFfix (x : X) (hx : x ∈ A) (hxK : x ∉ K) : F x = x := by
    by_cases hxU : x ∈ U
    · exact (_root_.Set.piecewise_eq_of_mem U f id hxU).trans (hfixed ⟨⟨hx, hxU⟩, hxK⟩)
    · exact _root_.Set.piecewise_eq_of_notMem U f id hxU
  have hF : ContinuousOn F A := by
    intro x hx
    by_cases hxU : x ∈ U
    · have hc : ContinuousWithinAt f A x :=
        (continuousWithinAt_inter (hU.mem_nhds hxU)).mp (hf x ⟨hx, hxU⟩)
      apply hc.congr_of_eventuallyEq_of_mem _ hx
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds hxU)] with y hy
      exact _root_.Set.piecewise_eq_of_mem U f id hy
    · have hxK : x ∉ K := fun h => hxU (hKU h)
      apply continuousWithinAt_id.congr_of_eventuallyEq_of_mem _ hx
      filter_upwards
        [eventually_nhdsWithin_of_eventually_nhds (hK.isClosed.isOpen_compl.mem_nhds hxK),
          self_mem_nhdsWithin] with y hyK hyA
      exact hFfix y hyA hyK
  have hFinj : _root_.Set.InjOn F A := by
    intro x hx y hy heq
    by_cases hxU : x ∈ U <;> by_cases hyU : y ∈ U
    · apply hinj ⟨hx, hxU⟩ ⟨hy, hyU⟩
      simpa only [F, _root_.Set.piecewise_eq_of_mem U f id hxU, _root_.Set.piecewise_eq_of_mem U f id hyU] using heq
    · have hfx := hmap ⟨hx, hxU⟩
      have he : f x = y := by simpa only [F, _root_.Set.piecewise_eq_of_mem U f id hxU,
        _root_.Set.piecewise_eq_of_notMem U f id hyU, id_eq] using heq
      exact False.elim (hyU (he ▸ hfx))
    · have hfy := hmap ⟨hy, hyU⟩
      have he : x = f y := by
        simpa only [F, _root_.Set.piecewise_eq_of_notMem U f id hxU,
          _root_.Set.piecewise_eq_of_mem U f id hyU, id_eq] using heq
      exact False.elim (hxU (he.symm ▸ hfy))
    · simpa only [F, _root_.Set.piecewise_eq_of_notMem U f id hxU,
        _root_.Set.piecewise_eq_of_notMem U f id hyU, id_eq] using heq
  have hc : Continuous (fun x : A => F x.val) := continuousOn_iff_continuous_domRestrict.mp hF
  have hi : Function.Injective (fun x : A => F x.val) := by
    intro x y heq
    exact Subtype.ext (hFinj x.property y.property heq)
  have hrange : _root_.Set.range (fun x : A => F x.val) = (A \ U) ∪ f '' (A ∩ U) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hxU : x.val ∈ U
      · right
        exact ⟨x.val, ⟨x.property, hxU⟩, (_root_.Set.piecewise_eq_of_mem U f id hxU).symm⟩
      · left
        change F x.val ∈ A \ U
        rw [show F x.val = x.val from _root_.Set.piecewise_eq_of_notMem U f id hxU]
        exact ⟨x.property, hxU⟩
    · rintro (hy | ⟨x, hx, rfl⟩)
      · exact ⟨⟨y, hy.1⟩, _root_.Set.piecewise_eq_of_notMem U f id hy.2⟩
      · exact ⟨⟨x, hx.1⟩, _root_.Set.piecewise_eq_of_mem U f id hx.2⟩
  have hproper : IsProperMap (fun x : A => F x.val) :=
    hA.isClosedEmbedding_subtypeVal.isProperMap.of_eventuallyEq_cocompact hc (by
      filter_upwards [(hA.isClosedEmbedding_subtypeVal.isCompact_preimage hK).compl_mem_cocompact]
        with x hx
      exact hFfix x.val x.property hx)
  have hemb : Topology.IsClosedEmbedding (fun x : A => F x.val) :=
    .of_continuous_injective_isClosedMap hc hi hproper.isClosedMap
  let H := hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  refine ⟨H, ?_, ?_⟩
  · intro x hxU
    exact _root_.Set.piecewise_eq_of_mem U f id hxU
  · intro x hxK
    exact hFfix x.val x.property hxK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.exists_piecewise_of_isClosed then
    throwError "Refusing to shadow existing declaration Homeomorph.exists_piecewise_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.exists_piecewise_of_isClosed ``Submission.Homeomorph.exists_piecewise_of_isClosed

open _root_.Homeomorph in
theorem exists_piecewise_of_isCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    {A U K : Set X} {f : X → X} (hA : IsCompact A) (hU : IsOpen U)
    (hf : ContinuousOn f (A ∩ U)) (hinj : _root_.Set.InjOn f (A ∩ U))
    (hmap : _root_.Set.MapsTo f (A ∩ U) U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hfixed : _root_.Set.EqOn f id ((A ∩ U) \ K)) :
    ∃ H : A ≃ₜ ↥((A \ U) ∪ f '' (A ∩ U)),
      (∀ x : A, x.val ∈ U → (H x).val = f x.val) ∧
      ∀ x : A, x.val ∉ K → (H x).val = x.val := by
  obtain ⟨H, hH, hHfix⟩ := exists_piecewise_of_isClosed hA.isClosed hU hf hinj hmap
    (hA.inter_right hK) (inter_subset_right.trans hKU)
    (by
      rintro x ⟨hx, hxK⟩
      exact hfixed ⟨hx, fun h => hxK ⟨hx.1, h⟩⟩)
  exact ⟨H, hH, fun x hx => hHfix x (fun h => hx h.2)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.exists_piecewise_of_isCompact then
    throwError "Refusing to shadow existing declaration Homeomorph.exists_piecewise_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.exists_piecewise_of_isCompact ``Submission.Homeomorph.exists_piecewise_of_isCompact

end Homeomorph

namespace OpenPartialHomeomorph
open _root_.OpenPartialHomeomorph

open _root_.OpenPartialHomeomorph in
theorem exists_homeomorph_eqOn_of_isClosed {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    (e : OpenPartialHomeomorph X Y) {A : Set X} (hA : IsClosed A)
    {f : Y → Y} (hf : ContinuousOn f (e '' (A ∩ e.source)))
    (hinj : _root_.Set.InjOn f (e '' (A ∩ e.source)))
    (hmap : _root_.Set.MapsTo f (e '' (A ∩ e.source)) e.target)
    {K : Set Y} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hfixed : _root_.Set.EqOn f id ((e '' (A ∩ e.source)) \ K)) :
    ∃ H : A ≃ₜ ↥((A \ e.source) ∪ e.symm '' (f '' (e '' (A ∩ e.source)))),
      (∀ x : A, x.val ∈ e.source → (H x).val = e.symm (f (e x.val))) ∧
      ∀ x : A, x.val ∉ e.symm '' K → (H x).val = x.val := by
  have he : ContinuousOn e (A ∩ e.source) := e.continuousOn.mono _root_.Set.inter_subset_right
  have hfe : ContinuousOn (fun x => f (e x)) (A ∩ e.source) :=
    hf.comp he (fun x hx => _root_.Set.mem_image_of_mem e hx)
  have htarget (x : X) (hx : x ∈ A ∩ e.source) : f (e x) ∈ e.target :=
    hmap (_root_.Set.mem_image_of_mem e hx)
  have hcont : ContinuousOn (fun x => e.symm (f (e x))) (A ∩ e.source) :=
    e.continuousOn_symm.comp hfe htarget
  have hfi : _root_.Set.InjOn (fun x => e.symm (f (e x))) (A ∩ e.source) := by
    intro x hx y hy heq
    apply e.injOn hx.2 hy.2
    apply hinj (_root_.Set.mem_image_of_mem e hx) (_root_.Set.mem_image_of_mem e hy)
    exact e.symm.injOn (htarget x hx) (htarget y hy) heq
  have hL : IsCompact (e.symm '' K) := hK.image_of_continuousOn (e.continuousOn_symm.mono hKt)
  obtain ⟨H, hH, hHfix⟩ := Homeomorph.exists_piecewise_of_isClosed hA e.open_source
    hcont hfi (fun x hx => e.map_target (htarget x hx)) hL
    (by rintro _ ⟨y, hy, rfl⟩; exact e.map_target (hKt hy))
    (by
      rintro x ⟨hx, hxK⟩
      have heK : e x ∉ K := fun h => hxK ⟨e x, h, e.left_inv hx.2⟩
      change e.symm (f (e x)) = x
      rw [hfixed ⟨mem_image_of_mem e hx, heK⟩, id_eq, e.left_inv hx.2])
  have heq : (A \ e.source) ∪ (fun x => e.symm (f (e x))) '' (A ∩ e.source) =
      (A \ e.source) ∪ e.symm '' (f '' (e '' (A ∩ e.source))) := by
    rw [_root_.Set.image_image, _root_.Set.image_image]
  exact ⟨H.trans (Homeomorph.setCongr heq), hH, hHfix⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.exists_homeomorph_eqOn_of_isClosed then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.exists_homeomorph_eqOn_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.exists_homeomorph_eqOn_of_isClosed ``Submission.OpenPartialHomeomorph.exists_homeomorph_eqOn_of_isClosed

open _root_.OpenPartialHomeomorph in
theorem exists_homeomorph_eqOn_of_isCompact {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    (e : OpenPartialHomeomorph X Y) {A : Set X} (hA : IsCompact A)
    {f : Y → Y} (hf : ContinuousOn f (e '' (A ∩ e.source)))
    (hinj : _root_.Set.InjOn f (e '' (A ∩ e.source)))
    (hmap : _root_.Set.MapsTo f (e '' (A ∩ e.source)) e.target)
    {K : Set Y} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hfixed : _root_.Set.EqOn f id ((e '' (A ∩ e.source)) \ K)) :
    ∃ H : A ≃ₜ ↥((A \ e.source) ∪ e.symm '' (f '' (e '' (A ∩ e.source)))),
      (∀ x : A, x.val ∈ e.source → (H x).val = e.symm (f (e x.val))) ∧
      ∀ x : A, x.val ∉ e.symm '' K → (H x).val = x.val := by
  exact e.exists_homeomorph_eqOn_of_isClosed hA.isClosed hf hinj hmap hK hKt hfixed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.exists_homeomorph_eqOn_of_isCompact then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.exists_homeomorph_eqOn_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.exists_homeomorph_eqOn_of_isCompact ``Submission.OpenPartialHomeomorph.exists_homeomorph_eqOn_of_isCompact

end OpenPartialHomeomorph
