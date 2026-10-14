import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Separation.Hausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry

open _root_.Bundle _root_.Set _root_.Topology

instance FiberBundle.t2Space_totalSpace
    {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    {E : B → Type*} [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [T2Space B] [T2Space F] :
    T2Space (Bundle.TotalSpace F E) := by
  refine ⟨fun x y hxy => ?_⟩
  by_cases hproj : (π F E) x = (π F E) y
  · set e := _root_.FiberBundle.trivializationAt F E ((π F E) x) with he
    have hxs : x ∈ e.source := by
      rw [e.mem_source]; exact _root_.FiberBundle.mem_baseSet_trivializationAt F E _
    have hys : y ∈ e.source := by
      rw [e.mem_source, ← hproj]; exact _root_.FiberBundle.mem_baseSet_trivializationAt F E _
    have hexy : e x ≠ e y := fun h => hxy (e.toOpenPartialHomeomorph.injOn hxs hys h)
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hexy
    refine ⟨e.source ∩ e ⁻¹' U, e.source ∩ e ⁻¹' V,
      e.toOpenPartialHomeomorph.isOpen_inter_preimage hU,
      e.toOpenPartialHomeomorph.isOpen_inter_preimage hV,
      ⟨hxs, hxU⟩, ⟨hys, hyV⟩, ?_⟩
    exact (hUV.preimage e).mono _root_.Set.inter_subset_right _root_.Set.inter_subset_right
  · obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hproj
    refine ⟨(π F E) ⁻¹' U, (π F E) ⁻¹' V,
      hU.preimage (FiberBundle.continuous_proj F E),
      hV.preimage (FiberBundle.continuous_proj F E), hxU, hyV, ?_⟩
    exact hUV.preimage _

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.FiberBundle
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.FiberBundle.t2Space_totalSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.FiberBundle.t2Space_totalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.FiberBundle.t2Space_totalSpace ``Submission.DifferentialGeometry.FiberBundle.t2Space_totalSpace

end DifferentialGeometry
