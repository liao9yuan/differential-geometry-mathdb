import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter _root_.Topology
open scoped _root_.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open _root_.IsLocalHomeomorphOn in
theorem IsLocalHomeomorphOn.isOpenEmbedding_restrict_of_injOn
    {f : X → Y} {Ω : Set X} (hf : IsLocalHomeomorphOn f Ω)
    (hΩ : IsOpen Ω) (hi : _root_.Set.InjOn f Ω) : _root_.Topology.IsOpenEmbedding (Ω.domRestrict f) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuousOn_iff_continuous_domRestrict.mp hf.continuousOn)
    (fun x y hxy => Subtype.ext (hi x.property y.property hxy))
  apply isOpenMap_iff_nhds_le.mpr
  intro x
  have he : Filter.map (Ω.domRestrict f) (𝓝 x) = 𝓝 (f x) := by
    change Filter.map (f ∘ Subtype.val) (𝓝 x) = _
    rw [← Filter.map_map, hΩ.isOpenEmbedding_subtypeVal.map_nhds_eq, hf.map_nhds_eq x.property]
  exact he.ge

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsLocalHomeomorphOn
  let env ← Lean.getEnv
  if env.contains `IsLocalHomeomorphOn.isOpenEmbedding_restrict_of_injOn then
    throwError "Refusing to shadow existing declaration IsLocalHomeomorphOn.isOpenEmbedding_restrict_of_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalHomeomorphOn.isOpenEmbedding_restrict_of_injOn ``Submission.IsLocalHomeomorphOn.isOpenEmbedding_restrict_of_injOn

open _root_.IsLocalHomeomorphOn in
theorem IsLocalHomeomorphOn.exists_openPartialHomeomorph_of_injOn [Nonempty X]
    {f : X → Y} {Ω : Set X} (hf : IsLocalHomeomorphOn f Ω)
    (hΩ : IsOpen Ω) (hi : _root_.Set.InjOn f Ω) :
    ∃ e : OpenPartialHomeomorph X Y, e.source = Ω ∧ e.target = f '' Ω ∧ (e : X → Y) = f := by
  let e := hi.toPartialEquiv f Ω
  let E := OpenPartialHomeomorph.ofContinuousOpenRestrict e hf.continuousOn
    (hf.isOpenEmbedding_restrict_of_injOn hΩ hi).isOpenMap hΩ
  exact ⟨E, rfl, rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsLocalHomeomorphOn.exists_openPartialHomeomorph_of_injOn then
    throwError "Refusing to shadow existing declaration IsLocalHomeomorphOn.exists_openPartialHomeomorph_of_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalHomeomorphOn.exists_openPartialHomeomorph_of_injOn ``Submission.IsLocalHomeomorphOn.exists_openPartialHomeomorph_of_injOn

end

end
