/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.ClosedBallImage
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BicollarEmbedding
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes
import Submission.DifferentialGeometry.Topology.Simplex.NormedBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLBall.isConnected_compl_image {P U : Set E3} (hP : IsPLBall 3 P)
    (hU : IsOpen U) {f : E3 → E3} (hf : ContinuousOn f U) (hinj : _root_.Set.InjOn f U)
    (hPU : P ⊆ U) : IsConnected (f '' P)ᶜ := by
  obtain ⟨g, hg⟩ := id hP
  have hcell : IsTopologicalCell 3 P :=
    ⟨hg.homeomorph.symm.trans
      (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph
        (EuclideanSpace.equiv (Fin 3) ℝ).symm)⟩
  obtain ⟨φ⟩ := hcell.image_of_continuousOn_injOn (hf.mono hPU) (hinj.mono hPU)
  exact isConnected_compl_of_homeomorphClosedBall_of_isBicollared
    (by rw [← Module.finrank_eq_rank']; norm_num) φ
    (hP.isBicollared_frontier_image hU hf hinj hPU)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isConnected_compl_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isConnected_compl_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isConnected_compl_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isConnected_compl_image

theorem IsPLBall.not_isBounded_connectedComponentIn_compl_of_subset_image
    {P U O : Set E3} (hP : IsPLBall 3 P) (hU : IsOpen U) {f : E3 → E3}
    (hf : ContinuousOn f U) (hinj : _root_.Set.InjOn f U) (hPU : P ⊆ U) (hOP : O ⊆ f '' P)
    {y : E3} (hy : y ∉ f '' P) :
    ¬ Bornology.IsBounded (connectedComponentIn Oᶜ y) := by
  have hconn := hP.isConnected_compl_image hU hf hinj hPU
  have hsub : (f '' P)ᶜ ⊆ connectedComponentIn Oᶜ y :=
    hconn.isPreconnected.subset_connectedComponentIn hy (compl_subset_compl.mpr hOP)
  have hcpt : IsCompact (f '' P) :=
    hP.isPolyhedron.isCompact.image_of_continuousOn (hf.mono hPU)
  intro hb
  have huniv : Bornology.IsBounded (_root_.Set.univ : Set E3) := by
    simpa only [_root_.Set.union_compl_self] using hcpt.isBounded.union (hb.subset hsub)
  have hcptU : IsCompact (_root_.Set.univ : Set E3) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_univ, huniv⟩
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace E3))
    (isCompact_univ_iff.mp hcptU)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.not_isBounded_connectedComponentIn_compl_of_subset_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.not_isBounded_connectedComponentIn_compl_of_subset_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.not_isBounded_connectedComponentIn_compl_of_subset_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.not_isBounded_connectedComponentIn_compl_of_subset_image

end DifferentialGeometry.Topology.PiecewiseLinear
