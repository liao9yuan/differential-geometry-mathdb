/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DiskLocalDegreeOrientation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.JordanDiskPasting
import Submission.DifferentialGeometry.Topology.LocalDegree.HomeomorphConjugation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Submission.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.DifferentialGeometry.LocalDegree

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "D1" => _root_.Metric.closedBall (0 : Plane) 1
local notation "B1" => _root_.Metric.ball (0 : Plane) 1
local notation "S1" => _root_.Metric.sphere (0 : Plane) 1

theorem isPLCirclePositive_frontier_iff_orientationParity_eq_zero
    {P : Set Plane} (hP : IsPLBall 2 P) {f : Plane → Plane}
    (hf : ContinuousOn f P) (hfi : _root_.Set.InjOn f P)
    (hB : _root_.Set.MapsTo f (interior P) (interior P)) (hS : _root_.Set.BijOn f (frontier P) (frontier P))
    {x : Plane} (hx : x ∈ interior P) :
    IsPLCirclePositive (frontier P) f ↔
      embeddingOrientationParity isOpen_interior (hf.mono interior_subset)
        (hfi.mono interior_subset) ⟨x, hx⟩ = 0 := by
  obtain ⟨e, heS, heP, heB⟩ := exists_homeomorph_image_closure_inside_eq_closedBall
    (isJordanCurve_of_isPLSphere_one hP.isPLSphere_frontier)
  rw [← hP.interior_eq_inside_frontier, hP.closure_interior] at heP
  rw [← hP.interior_eq_inside_frontier] at heB
  have hback (T T' : Set Plane) (hTT' : e '' T = T') : _root_.Set.MapsTo e.symm T' T := by
    rintro y hy
    obtain ⟨z, hz, rfl⟩ := hTT'.symm.subset hy
    rwa [e.symm_apply_apply]
  have hPS : _root_.Set.BijOn e (frontier P) S1 := by
    rw [← heS]
    exact e.injective.injOn.bijOn_image
  have hSP : _root_.Set.BijOn e.symm S1 (frontier P) :=
    ⟨hback _ _ heS, e.symm.injective.injOn,
      fun z hz => ⟨e z, hPS.mapsTo hz, e.symm_apply_apply z⟩⟩
  let g : Plane → Plane := e ∘ f ∘ e.symm
  have hg : ContinuousOn g D1 := e.continuous.comp_continuousOn
    (hf.comp e.symm.continuous.continuousOn (hback _ _ heP))
  have hgi : _root_.Set.InjOn g D1 := fun y hy z hz hyz =>
    e.symm.injective (hfi (hback _ _ heP hy) (hback _ _ heP hz) (e.injective hyz))
  have hgB : _root_.Set.MapsTo g B1 B1 := by
    intro y hy
    rw [← heB]
    exact ⟨f (e.symm y), hB (hback _ _ heB hy), rfl⟩
  have hgS : _root_.Set.BijOn g S1 S1 := hPS.comp (hS.comp hSP)
  have hyB : e x ∈ B1 := heB ▸ _root_.Set.mem_image_of_mem e hx
  have hpos : IsPLCirclePositive (frontier P) f ↔ IsPLCirclePositive S1 g := by
    constructor
    · intro hp
      have hp' := hp.conj hS.mapsTo e.continuous.continuousOn hPS
      apply hp'.of_eqOn
      intro y hy
      have hi : Function.invFunOn e (frontier P) y = e.symm y :=
        e.injective ((hPS.invOn_invFunOn.2 hy).trans (e.apply_symm_apply y).symm)
      exact congrArg (fun z => e (f z)) hi.symm
    · intro hp
      have hp' := hp.conj hgS.mapsTo e.symm.continuous.continuousOn hSP
      apply hp'.of_eqOn
      intro y hy
      have hi : Function.invFunOn e.symm S1 y = e y :=
        e.symm.injective ((hSP.invOn_invFunOn.2 hy).trans (e.symm_apply_apply y).symm)
      simp only [Function.comp_apply, hi, g, e.symm_apply_apply]
  have hgV : ContinuousOn g (e.symm ⁻¹' interior P) :=
    e.continuous.comp_continuousOn
      ((hf.mono interior_subset).comp e.symm.continuous.continuousOn (fun _ hz => hz))
  have hgiV : _root_.Set.InjOn g (e.symm ⁻¹' interior P) := fun y hy z hz hyz =>
    e.symm.injective (hfi (interior_subset hy) (interior_subset hz) (e.injective hyz))
  have hyV : e x ∈ e.symm ⁻¹' interior P := by
    simpa only [_root_.Set.mem_preimage, e.symm_apply_apply] using hx
  have hconj : embeddingOrientationParity (isOpen_interior.preimage e.symm.continuous)
      hgV hgiV ⟨e x, hyV⟩ =
      embeddingOrientationParity isOpen_interior (hf.mono interior_subset)
        (hfi.mono interior_subset) ⟨x, hx⟩ :=
    embeddingOrientationParity_conj_homeomorph e isOpen_interior
      (hf.mono interior_subset) (hfi.mono interior_subset) ⟨x, hx⟩
  have hrestrict := embeddingOrientationParity_congr _root_.Metric.isOpen_ball
    (isOpen_interior.preimage e.symm.continuous)
    (hg.mono _root_.Metric.ball_subset_closedBall) (hgi.mono _root_.Metric.ball_subset_closedBall)
    hgV hgiV hyB hyV Filter.EventuallyEq.rfl
  have hround := (isPLCirclePositive_iff_localDegree_sub_eq_one hg hgi hgB hgS hyB).trans
    (embeddingOrientationParity_eq_zero_iff _root_.Metric.isOpen_ball
      (hg.mono _root_.Metric.ball_subset_closedBall) (hgi.mono _root_.Metric.ball_subset_closedBall) ⟨e x, hyB⟩).symm
  rw [hpos, hround, hrestrict, hconj]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_frontier_iff_orientationParity_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_frontier_iff_orientationParity_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_frontier_iff_orientationParity_eq_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLCirclePositive_frontier_iff_orientationParity_eq_zero

end DifferentialGeometry.Topology.PiecewiseLinear
