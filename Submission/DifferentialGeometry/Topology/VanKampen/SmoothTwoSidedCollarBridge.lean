/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import Submission.DifferentialGeometry.Topology.VanKampen.TwoSidedCollarRescale

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.ContDiff

noncomputable section

universe u v w x

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

variable
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type x} [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {S : Type*} [TopologicalSpace S] [ChartedSpace H S]
    {M : Type*} [TopologicalSpace M] [ChartedSpace G M]
    {e : S → M} (h : SmoothTwoSidedCollar I J e)

noncomputable def toTwoSidedCollar : ThreeManifold.TwoSidedCollar e :=
  ThreeManifold.TwoSidedCollar.ofOpenInterval h.radius_pos h.toFun
    h.isOpenEmbedding_toFun h.toFun_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toTwoSidedCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.toTwoSidedCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toTwoSidedCollar ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.toTwoSidedCollar

@[simp]
theorem toTwoSidedCollar_toFun (p : S × ℝ) :
    h.toTwoSidedCollar.toFun p =
      h.toFun (p.1, ThreeManifold.TwoSidedCollar.realHomeomorphIoo
        h.radius h.radius_pos p.2) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toTwoSidedCollar_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.toTwoSidedCollar_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toTwoSidedCollar_toFun ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.toTwoSidedCollar_toFun

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
