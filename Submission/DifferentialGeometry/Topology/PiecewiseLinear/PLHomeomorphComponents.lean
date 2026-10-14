/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ComponentPartitionEquivalence
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLHomeomorphOn.exists_component_equiv
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (Q : Geometry.SimplicialComplex ℝ F) {f : E → F}
    (hf : IsPLHomeomorphOn f K.space Q.space) :
    ∃ e : ConnectedComponents K.space ≃ ConnectedComponents Q.space,
      ∀ c, IsPLHomeomorphOn f (connectedComponentComplex K c).space
        (connectedComponentComplex Q (e c)).space := by
  let _ : Finite (ConnectedComponents K.space) := finite_connectedComponents_space K
  let _ (c : ConnectedComponents K.space) : Finite (connectedComponentComplex K c).faces :=
    (connectedComponentComplex_faces_finite K c).to_subtype
  let B := fun c => (connectedComponentComplex K c).space
  have hBsub (c : ConnectedComponents K.space) : B c ⊆ K.space :=
    (_root_.Set.subset_iUnion B c).trans (iUnion_connectedComponentComplex_space K).subset
  have hfB (c : ConnectedComponents K.space) : IsPLHomeomorphOn f (B c) (f '' B c) :=
    hf.restrict (isPolyhedron_space (connectedComponentComplex K c)) (hBsub c)
  have hconn (c : ConnectedComponents K.space) : IsConnected (f '' B c) :=
    (isConnected_connectedComponentComplex_space K c).image f
      (hfB c).isPiecewiseAffineOn.continuousOn
  have hclosed (c : ConnectedComponents K.space) : IsClosed (f '' B c) :=
    ((isPolyhedron_space (connectedComponentComplex K c)).image_of_isPiecewiseAffineOn
      (hfB c).isPiecewiseAffineOn (hfB c).bijOn.injOn).isClosed
  have hdis : Pairwise fun c d => Disjoint (f '' B c) (f '' B d) := by
    intro c d hcd
    apply disjoint_left.mpr
    rintro y ⟨z, hz, hzy⟩ ⟨w, hw, hwy⟩
    have hzw := hf.bijOn.injOn (hBsub c hz) (hBsub d hw) (hzy.trans hwy.symm)
    exact disjoint_left.mp (pairwise_disjoint_connectedComponentComplex_space K hcd)
      hz (hzw.symm ▸ hw)
  have hcover : Q.space = ⋃ c, f '' B c := by
    calc Q.space = f '' K.space := hf.image_eq.symm
      _ = f '' (⋃ c, B c) := congrArg (fun P : Set E => f '' P)
        (iUnion_connectedComponentComplex_space K).symm
      _ = ⋃ c, f '' B c := by rw [_root_.Set.image_iUnion]
  obtain ⟨e, he⟩ := exists_equiv_connectedComponents_of_finite_partition Q
    (fun c => f '' B c) hconn hclosed hdis hcover
  refine ⟨e, fun c => ?_⟩
  rw [he c]
  exact hfB c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_component_equiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_component_equiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_component_equiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_component_equiv

end DifferentialGeometry.Topology.PiecewiseLinear
