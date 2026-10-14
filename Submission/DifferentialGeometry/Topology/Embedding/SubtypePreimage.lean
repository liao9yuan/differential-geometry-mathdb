import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Compactness.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Topology
universe u
namespace Topology.IsInducing
open _root_.Topology _root_.Topology.IsInducing

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

open _root_.Topology _root_.Topology.IsInducing in
theorem isCompact_image_subtype_preimage {U : Set E} {e : U → X}
    (he : _root_.Topology.IsInducing e) {L : Set X} (hL : IsCompact L) (hLe : L ⊆ _root_.Set.range e) :
    IsCompact (Subtype.val '' (e ⁻¹' L)) :=
  (he.isCompact_preimage' hL hLe).image continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Topology.IsInducing.isCompact_image_subtype_preimage then
    throwError "Refusing to shadow existing declaration Topology.IsInducing.isCompact_image_subtype_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `Topology.IsInducing.isCompact_image_subtype_preimage ``Submission.Topology.IsInducing.isCompact_image_subtype_preimage

end Topology.IsInducing

namespace Function.Injective
open _root_.Function _root_.Function.Injective

variable {E X : Type*}

open _root_.Function _root_.Function.Injective in
theorem image_subtype_preimage_subset {U W : Set E} {e : U → X}
    (he : _root_.Function.Injective e) {L : Set X}
    (hLe : L ⊆ e '' {z : U | (z : E) ∈ W}) :
    Subtype.val '' (e ⁻¹' L) ⊆ W := by
  rintro z ⟨u, hu, rfl⟩
  obtain ⟨v, hv, huv⟩ := hLe hu
  exact (he huv) ▸ hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Function.Injective.image_subtype_preimage_subset then
    throwError "Refusing to shadow existing declaration Function.Injective.image_subtype_preimage_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Function.Injective.image_subtype_preimage_subset ``Submission.Function.Injective.image_subtype_preimage_subset

end Function.Injective

end

end
