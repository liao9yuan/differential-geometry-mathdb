import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.Order.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞} {f : M × ℝ → N} {S : Set M} {a b : ℝ}

open _root_.ContMDiffOn in
theorem ContMDiffOn.prod_Icc_of_prod_Ico_of_locally_Icc
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' n f (S ×ˢ _root_.Set.Ico a b))
    (hb : ∀ x ∈ S, ∃ s < b, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' n f ((S ∩ V) ×ˢ _root_.Set.Icc s b)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' n f (S ×ˢ _root_.Set.Icc a b) := by
  rintro ⟨x, t⟩ ⟨hx, hat, htb⟩
  rcases lt_or_eq_of_le htb with htb | htb
  · apply (hf (x, t) ⟨hx, hat, htb⟩).mono_of_mem_nhdsWithin
    have ht : {p : M × ℝ | p.2 < b} ∈ 𝓝[S ×ˢ _root_.Set.Icc a b] (x, t) :=
      continuous_snd.continuousWithinAt (Iio_mem_nhds htb)
    filter_upwards [self_mem_nhdsWithin, ht] with p hp hpt
    exact ⟨hp.1, hp.2.1, hpt⟩
  · change t = b at htb
    subst t
    obtain ⟨s, hsb, V, hV, hxV, hfV⟩ := hb x hx
    apply (hfV (x, b) ⟨⟨hx, hxV⟩, hsb.le, le_rfl⟩).mono_of_mem_nhdsWithin
    have hVn : {p : M × ℝ | p.1 ∈ V} ∈ 𝓝[S ×ˢ _root_.Set.Icc a b] (x, b) :=
      continuous_fst.continuousWithinAt (hV.mem_nhds hxV)
    have hsn : {p : M × ℝ | s < p.2} ∈ 𝓝[S ×ˢ _root_.Set.Icc a b] (x, b) :=
      continuous_snd.continuousWithinAt (Ioi_mem_nhds hsb)
    filter_upwards [self_mem_nhdsWithin, hVn, hsn] with p hp hpV hps
    exact ⟨⟨hp.1, hpV⟩, hps.le, hp.2.2⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffOn
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.prod_Icc_of_prod_Ico_of_locally_Icc then
    throwError "Refusing to shadow existing declaration ContMDiffOn.prod_Icc_of_prod_Ico_of_locally_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.prod_Icc_of_prod_Ico_of_locally_Icc ``Submission.ContMDiffOn.prod_Icc_of_prod_Ico_of_locally_Icc
