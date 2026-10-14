import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology

namespace ModelWithCorners
open _root_.ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

open _root_.ModelWithCorners in
theorem dense_interior : Dense (I.interior M) := by
  rw [dense_iff_inter_open]
  intro V hVopen hVne
  obtain ⟨x, hxV⟩ := hVne
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source]; exact hxsrc
  let s : Set M := V ∩ (chartAt H x).source
  have hs_open : IsOpen s := hVopen.inter (chartAt H x).open_source
  have hxs : x ∈ s := ⟨hxV, hxsrc⟩
  have h_img_nhdW : (extChartAt I x) '' s ∈ 𝓝[_root_.Set.range I] (extChartAt I x x) := by
    rw [← map_extChartAt_nhds (x := x)]
    exact Filter.image_mem_map (hs_open.mem_nhds hxs)
  obtain ⟨U, hU_open, hU_mem, hU_sub⟩ := mem_nhdsWithin.mp h_img_nhdW
  have hxImg_inRange : extChartAt I x x ∈ _root_.Set.range I :=
    extChartAt_target_subset_range x ((extChartAt I x).map_source hxext)
  have hxImg_inClosure : extChartAt I x x ∈ closure (interior (_root_.Set.range I)) := by
    rw [← I.range_eq_closure_interior]; exact hxImg_inRange
  obtain ⟨p, hp_U, hp_int⟩ := mem_closure_iff.mp hxImg_inClosure U hU_open hU_mem
  obtain ⟨y, hys, hyEq⟩ := hU_sub ⟨hp_U, interior_subset hp_int⟩
  refine ⟨y, hys.1, ?_⟩
  have hp_inExtTarget : ((chartAt H x).extend I) y ∈
      interior ((chartAt H x).extend I).target := by
    have hI_inInterior : I ((chartAt H x) y) ∈ interior (_root_.Set.range I) := by
      change extChartAt I x y ∈ interior (_root_.Set.range I)
      rw [hyEq]; exact hp_int
    exact (chartAt H x).mem_interior_extend_target
      ((chartAt H x).map_source hys.2) hI_inInterior
  exact (I.isInteriorPoint_iff_of_mem_atlas (n := 1) one_ne_zero
    (chart_mem_atlas H x) hys.2).mpr hp_inExtTarget

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ModelWithCorners.dense_interior then
    throwError "Refusing to shadow existing declaration ModelWithCorners.dense_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `ModelWithCorners.dense_interior ``Submission.ModelWithCorners.dense_interior

end ModelWithCorners
