/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.ChartParity
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34ConnectedCarriers
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexIncidentEdge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.DifferentialGeometry.LocalDegree

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34_vertex_chart [FiniteDimensional ℝ Ea]
    {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ E3}
    {Sd : Section34SimplexIndex 𝒦 3 → Set E3}
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (w : Section34VertexIndex 𝒦 𝒦') :
    ∃ c : OpenPartialHomeomorph M₂ E3,
      c ∈ (plGroupoid 3).maximalAtlas M₂ ∧ Q w ⊆ c.source := by
  obtain ⟨s, hs⟩ := exists_section34Vertex_triangle hframe w
  obtain ⟨hct, hsource⟩ := htor.1 s
  exact ⟨ct s, hct, fun y hy => hsource (mem_iUnion₂.mpr ⟨w, hs, hy⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_vertex_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_vertex_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_vertex_chart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_section34_vertex_chart

theorem section34_vertex_chart_transfer_eq
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends
      Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hsep : ∀ w w', w ≠ w' →
      Disjoint (h '' simplexBody 𝒦' w.1) (G w' '' Cp w'))
    (hDvsub : ∀ w, Dv w ⊆ G w '' Cp w)
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦))
    (w : Section34VertexIndex 𝒦 𝒦')
    (c c' : OpenPartialHomeomorph M₂ E3)
    (hQc : Q w ⊆ c.source) (hQc' : Q w ⊆ c'.source)
    {x y : M₂} (hx : x ∈ h '' src (.vertexBall w)) (hy : y ∈ Dv w) :
    chartOrientationParity c c' x
        (hQc (section34_image_vertexBall_subset_Q hprep w hx))
        (hQc' (section34_image_vertexBall_subset_Q hprep w hx)) =
      chartOrientationParity c c' y (hQc (hDvQ w hy)) (hQc' (hDvQ w hy)) := by
  obtain ⟨hA, hAQ⟩ := section34_vertex_carrier_connected
    hU hh hframe hprep hsep hDvsub hDv hDvQ hQlf hDnbhd w
  exact chartOrientationParity_eq_of_isPreconnected c c' hA.isPreconnected
    (hAQ.trans hQc) (hAQ.trans hQc') (Or.inl hx) (Or.inr hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_vertex_chart_transfer_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_vertex_chart_transfer_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_vertex_chart_transfer_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_vertex_chart_transfer_eq

end DifferentialGeometry.Topology.PiecewiseLinear
