/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexInteriorOverlap
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexBallStar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ :
    Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem section34_image_vertexBall_subset_Q
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends
      Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (w : Section34VertexIndex 𝒦 𝒦') :
    h '' src (.vertexBall w) ⊆ Q w := by
  obtain ⟨-, -, hsubs, -, -, -, hCcQ, -⟩ := hprep
  exact (_root_.Set.image_mono (hsubs w).1).trans ((hCcQ w).trans interior_subset)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_image_vertexBall_subset_Q then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_image_vertexBall_subset_Q"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_image_vertexBall_subset_Q ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_image_vertexBall_subset_Q

theorem section34_vertex_carrier_connected
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
    (w : Section34VertexIndex 𝒦 𝒦') :
    IsConnected (h '' src (.vertexBall w) ∪ Dv w) ∧
      h '' src (.vertexBall w) ∪ Dv w ⊆ Q w := by
  obtain ⟨-, -, -, hcell, -, -, -, -, hcover, -⟩ := id hframe
  have hsrcU : src (.vertexBall w) ⊆ U :=
    (_root_.Set.subset_iUnion src (.vertexBall w)).trans hcover.subset
  have hcont : ContinuousOn h (src (.vertexBall w)) :=
    (continuousOn_iff_continuous_domRestrict.mpr hh.continuous).mono hsrcU
  have hsrcConn : IsConnected (h '' src (.vertexBall w)) :=
    (hcell (.vertexBall w)).isConnected.image h hcont
  have hDvConn : IsConnected (Dv w) := (hDv w).isConnected
  obtain ⟨y, hy₁, hy₂⟩ :=
    section34_source_target_vertex_interiors_meet hU hh hframe hsep hDvsub
      hDv hDvQ hQlf hDnbhd w
  have hinter : (h '' src (.vertexBall w) ∩ Dv w).Nonempty := by
    obtain ⟨x, hx, rfl⟩ := hy₁
    exact ⟨h x, ⟨x, interior_subset hx, rfl⟩, interior_subset hy₂⟩
  exact ⟨hsrcConn.union hinter hDvConn,
    _root_.Set.union_subset (section34_image_vertexBall_subset_Q hprep w) (hDvQ w)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_vertex_carrier_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_vertex_carrier_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_vertex_carrier_connected ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_vertex_carrier_connected

end DifferentialGeometry.Topology.PiecewiseLinear
