/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.EmbeddingParity
import Mathlib.Topology.Instances.RealVectorSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

theorem euclideanLocalDegree_sub_eq_one_of_eqOn_compl_isCompact
    {f : E → E} (hf : Continuous f) (hinj : Function.Injective f)
    {K : Set E} (hK : IsCompact K) (hfix : _root_.Set.EqOn f id Kᶜ) (x : E) :
    euclideanLocalDegree (fun z => f z - f x) x
      (isolatedZero_sub_of_injOn isOpen_univ hf.continuousOn hinj.injOn (_root_.Set.mem_univ x)) = 1 := by
  obtain ⟨y, hy⟩ := Set.nonempty_compl.mpr hK.ne_univ
  have heq : f =ᶠ[𝓝 y] id :=
    Filter.mem_of_superset (hK.isClosed.isOpen_compl.mem_nhds hy) (fun z hz => hfix hz)
  have hzero := embeddingOrientationParity_congr isOpen_univ isOpen_univ
    hf.continuousOn hinj.injOn continuousOn_id (_root_.Set.injOn_id _root_.Set.univ)
    (_root_.Set.mem_univ y) (_root_.Set.mem_univ y) heq
  rw [embeddingOrientationParity_id] at hzero
  apply (embeddingOrientationParity_eq_zero_iff isOpen_univ hf.continuousOn
    hinj.injOn ⟨x, _root_.Set.mem_univ x⟩).mp
  exact (embeddingOrientationParity_eq_of_isPreconnected isOpen_univ hf.continuousOn
    hinj.injOn _root_.PreconnectedSpace.isPreconnected_univ Subset.rfl (_root_.Set.mem_univ x) (_root_.Set.mem_univ y)).trans hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_eq_one_of_eqOn_compl_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_eq_one_of_eqOn_compl_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_eq_one_of_eqOn_compl_isCompact ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_eq_one_of_eqOn_compl_isCompact

end DifferentialGeometry.LocalDegree
