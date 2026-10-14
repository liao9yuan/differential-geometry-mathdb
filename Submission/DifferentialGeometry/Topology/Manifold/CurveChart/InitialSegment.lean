import Mathlib.Geometry.Manifold.ChartedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry
namespace Geometry

variable {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M]

theorem exists_chart_initial_segment
    {a b : Real} (hab : a < b) {gamma : Real → M}
    (hgamma : ContinuousOn gamma (_root_.Set.Icc a b)) {p : M}
    (hp : gamma a ∈ (chartAt H p).source) :
    ∃ c : Real, a < c ∧ c ≤ b ∧
      MapsTo gamma (_root_.Set.Icc a c) (chartAt H p).source := by
  have hcont : ContinuousWithinAt gamma (_root_.Set.Icc a b) a :=
    hgamma a ⟨le_rfl, hab.le⟩
  have hpre : gamma ⁻¹' (chartAt H p).source ∈ 𝓝[_root_.Set.Icc a b] a :=
    hcont ((chartAt H p).open_source.mem_nhds hp)
  rw [nhdsWithin_Icc_eq_nhdsGE hab] at hpre
  have hinter : gamma ⁻¹' (chartAt H p).source ∩ _root_.Set.Icc a b ∈ 𝓝[≥] a :=
    _root_.Filter.inter_mem hpre (Icc_mem_nhdsGE hab)
  obtain ⟨c, hac, hsub⟩ :=
    mem_nhdsGE_iff_exists_Icc_subset.mp hinter
  have hc : c ∈ gamma ⁻¹' (chartAt H p).source ∩ _root_.Set.Icc a b :=
    hsub ⟨hac.le, le_rfl⟩
  exact ⟨c, hac, hc.2.2, fun s hs ↦ (hsub hs).1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_chart_initial_segment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_chart_initial_segment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_chart_initial_segment ``Submission.DifferentialGeometry.Geometry.exists_chart_initial_segment

end Geometry
end DifferentialGeometry
