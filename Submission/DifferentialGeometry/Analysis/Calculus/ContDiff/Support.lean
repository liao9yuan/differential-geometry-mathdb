import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : E → F} {s t : Set E}

open _root_.ContDiffOn in
theorem ContDiffOn.contDiffOn_of_tsupport_subset (hf : ContDiffOn 𝕜 n f (s ∩ t))
    (hs : IsOpen s) (hfs : tsupport f ∩ t ⊆ s) : ContDiffOn 𝕜 n f t := by
  intro x hx
  by_cases hfx : x ∈ tsupport f
  · have hxs : x ∈ s := hfs ⟨hfx, hx⟩
    apply (contDiffWithinAt_inter (hs.mem_nhds hxs)).mp
    exact (hf x ⟨hxs, hx⟩).mono (by rw [_root_.Set.inter_comm])
  · exact contDiffAt_const.contDiffWithinAt.congr_of_eventuallyEq
      (Filter.EventuallyEq.filter_mono (notMem_tsupport_iff_eventuallyEq.mp hfx)
        nhdsWithin_le_nhds) (image_eq_zero_of_notMem_tsupport hfx)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContDiffOn
  let env ← Lean.getEnv
  if env.contains `ContDiffOn.contDiffOn_of_tsupport_subset then
    throwError "Refusing to shadow existing declaration ContDiffOn.contDiffOn_of_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffOn.contDiffOn_of_tsupport_subset ``Submission.ContDiffOn.contDiffOn_of_tsupport_subset

open _root_.ContDiffOn in
theorem ContDiffOn.contDiff_of_tsupport_subset (hf : ContDiffOn 𝕜 n f s)
    (hs : IsOpen s) (hfs : tsupport f ⊆ s) : ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ]
  apply ContDiffOn.contDiffOn_of_tsupport_subset (s := s)
  · simpa only [_root_.Set.inter_univ] using hf
  · exact hs
  · simpa only [_root_.Set.inter_univ] using hfs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffOn.contDiff_of_tsupport_subset then
    throwError "Refusing to shadow existing declaration ContDiffOn.contDiff_of_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffOn.contDiff_of_tsupport_subset ``Submission.ContDiffOn.contDiff_of_tsupport_subset

open _root_.ContDiffOn in
theorem ContDiffOn.indicator_of_tsupport_subset (hf : ContDiffOn 𝕜 n f (s ∩ t))
    (hs : IsOpen s) (hfs : tsupport f ∩ t ⊆ s) :
    ContDiffOn 𝕜 n ((s ∩ t).indicator f) t := by
  classical
  have hsub : tsupport ((s ∩ t).indicator f) ⊆ tsupport f := by
    apply closure_mono
    rw [_root_.Set.support_indicator]
    exact _root_.Set.inter_subset_right
  apply ContDiffOn.contDiffOn_of_tsupport_subset
    (hf.congr fun x hx => _root_.Set.indicator_of_mem hx f) hs
  intro x hx
  exact hfs ⟨hsub hx.1, hx.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffOn.indicator_of_tsupport_subset then
    throwError "Refusing to shadow existing declaration ContDiffOn.indicator_of_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffOn.indicator_of_tsupport_subset ``Submission.ContDiffOn.indicator_of_tsupport_subset
