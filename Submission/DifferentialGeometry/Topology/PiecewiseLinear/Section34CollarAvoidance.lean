import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtensionSupport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_short_collar_disjoint_of_closed
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S P : Set X} (hS : IsCompact S) {c : ℝ} (hc : 0 < c)
    {ρ : X × ℝ → X} (hρ : ContinuousOn ρ (S ×ˢ _root_.Set.Icc (0 : ℝ) c))
    (hρP : _root_.Set.MapsTo ρ (S ×ˢ _root_.Set.Icc (0 : ℝ) c) P)
    (hzero : ∀ x ∈ S, ρ (x, 0) = x) {u : X → Y} (hu : ContinuousOn u P)
    {Z : Set Y} (hZ : IsClosed Z) (hdis : Disjoint (u '' S) Z) :
    ∃ d : ℝ, 0 < d ∧ d ≤ c ∧ Disjoint ((u ∘ ρ) '' (S ×ˢ _root_.Set.Icc (0 : ℝ) d)) Z := by
  have hO : Zᶜ ∈ 𝓝ˢ[_root_.Set.univ] (u '' S) := by
    simpa only [nhdsSetWithin, Filter.principal_univ, inf_top_eq] using
      hZ.isOpen_compl.mem_nhdsSet.mpr (disjoint_left.mp hdis)
  obtain ⟨d, hd, hdc, hsmall⟩ := exists_short_product_image_subset_of_compact hS hc
    (hu.comp hρ hρP) (_root_.Set.mapsTo_univ _ _)
    (fun x hx => by
      change u (ρ (x, 0)) ∈ u '' S
      rw [hzero x hx]
      exact _root_.Set.mem_image_of_mem u hx) hO
  exact ⟨d, hd, hdc, disjoint_left.mpr fun x hx => hsmall hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_short_collar_disjoint_of_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_short_collar_disjoint_of_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_short_collar_disjoint_of_closed ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_short_collar_disjoint_of_closed

end DifferentialGeometry.Topology.PiecewiseLinear
