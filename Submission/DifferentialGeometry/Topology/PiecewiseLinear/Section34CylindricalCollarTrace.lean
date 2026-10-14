import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SynchronizedShellTraces

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem cylindrical_trace_of_collar_level_traces
    {E M X ι : Type*} {u : E → M} {ρ : E × ℝ → E} {F : X × ℝ → M}
    {R W S : Set E} {A : Set M} {B : Set X} {η : ι → ℝ → X} {c : ℝ}
    (hSR : S ⊆ R) (hW : ρ '' (S ×ˢ _root_.Set.Icc (0 : ℝ) c) = W)
    (hzero : ∀ x ∈ S, ρ (x, 0) = x)
    (htrace : u '' R ∩ A = F '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1)) (hcore : ∀ k, η k 0 ∈ B)
    (hlevels : ∀ t ∈ _root_.Set.Ioc (0 : ℝ) c, (u ∘ ρ) '' (S ×ˢ {t}) ∩ A =
      ⋃ k, F '' ({η k t} ×ˢ _root_.Set.Icc (0 : ℝ) 1)) :
    u '' (R ∪ W) ∩ A = F '' ((B ∪ ⋃ k, η k '' _root_.Set.Icc (0 : ℝ) c) ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
  have hbase : u '' R ∩ A ⊆
      F '' ((B ∪ ⋃ k, η k '' _root_.Set.Icc (0 : ℝ) c) ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    rw [htrace]
    exact _root_.Set.image_mono (_root_.Set.prod_mono_left _root_.Set.subset_union_left)
  apply Subset.antisymm
  · rintro y ⟨⟨x, hx, rfl⟩, hxA⟩
    rcases hx with hx | hx
    · exact hbase ⟨mem_image_of_mem u hx, hxA⟩
    · obtain ⟨⟨p, t⟩, ⟨hp, ht⟩, rfl⟩ := hW.symm.subset hx
      by_cases ht0 : t = 0
      · rw [ht0, hzero p hp] at hxA ⊢
        exact hbase ⟨mem_image_of_mem u (hSR hp), hxA⟩
      · have htp : t ∈ _root_.Set.Ioc (0 : ℝ) c := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
        have hm := (hlevels t htp).subset
          ⟨⟨(p, t), ⟨hp, rfl⟩, rfl⟩, hxA⟩
        obtain ⟨k, ⟨⟨q, s⟩, ⟨hq, hs⟩, heq⟩⟩ := mem_iUnion.mp hm
        refine ⟨(q, s), ⟨Or.inr (mem_iUnion.mpr ⟨k, ?_⟩), hs⟩, heq⟩
        exact ⟨t, ht, hq.symm⟩
  · rintro y ⟨⟨q, s⟩, ⟨hq, hs⟩, rfl⟩
    rcases hq with hq | hq
    · obtain ⟨hyR, hyA⟩ := htrace.symm.subset (_root_.Set.mem_image_of_mem F ⟨hq, hs⟩)
      exact ⟨image_mono _root_.Set.subset_union_left hyR, hyA⟩
    · obtain ⟨k, ⟨t, ht, rfl⟩⟩ := mem_iUnion.mp hq
      by_cases ht0 : t = 0
      · subst t
        obtain ⟨hyR, hyA⟩ := htrace.symm.subset (_root_.Set.mem_image_of_mem F ⟨hcore k, hs⟩)
        exact ⟨image_mono _root_.Set.subset_union_left hyR, hyA⟩
      · have htp : t ∈ _root_.Set.Ioc (0 : ℝ) c := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
        have hm := (hlevels t htp).symm.subset
          (mem_iUnion.mpr ⟨k, (η k t, s), ⟨rfl, hs⟩, rfl⟩)
        obtain ⟨⟨⟨p, r⟩, ⟨hp, hr⟩, heq⟩, hyA⟩ := hm
        have hrt : r = t := hr
        subst r
        exact ⟨⟨ρ (p, t), Or.inr (hW.subset (_root_.Set.mem_image_of_mem ρ ⟨hp, ht⟩)), heq⟩, hyA⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.cylindrical_trace_of_collar_level_traces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.cylindrical_trace_of_collar_level_traces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.cylindrical_trace_of_collar_level_traces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cylindrical_trace_of_collar_level_traces

end DifferentialGeometry.Topology.PiecewiseLinear
