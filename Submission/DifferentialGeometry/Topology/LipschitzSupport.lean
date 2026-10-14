import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


namespace LocallyLipschitzOn
open _root_.LocallyLipschitzOn

open _root_.Filter _root_.Set
open scoped _root_.Topology

open _root_.LocallyLipschitzOn in
theorem locallyLipschitz_of_tsupport_subset
    {X F : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace F] [Zero F]
    {Ω : Set X} (hΩ : IsOpen Ω) {u : X → F}
    (hu : LocallyLipschitzOn Ω u) (hsupport : tsupport u ⊆ Ω) : LocallyLipschitz u := by
  intro x
  by_cases hx : x ∈ Ω
  · obtain ⟨C, V, hV, hC⟩ := hu hx
    exact ⟨C, V, by simpa only [hΩ.nhdsWithin_eq hx] using hV, hC⟩
  · refine ⟨0, (tsupport u)ᶜ,
      (isClosed_tsupport u).isOpen_compl.mem_nhds (fun h => hx (hsupport h)), ?_⟩
    intro y hy z hz
    rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hz,
      _root_.PseudoEMetricSpace.edist_self]
    exact bot_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LocallyLipschitzOn.locallyLipschitz_of_tsupport_subset then
    throwError "Refusing to shadow existing declaration LocallyLipschitzOn.locallyLipschitz_of_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `LocallyLipschitzOn.locallyLipschitz_of_tsupport_subset ``Submission.LocallyLipschitzOn.locallyLipschitz_of_tsupport_subset

end LocallyLipschitzOn
