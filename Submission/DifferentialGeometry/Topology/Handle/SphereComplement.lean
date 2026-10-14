import Submission.DifferentialGeometry.Topology.Handle.SphereNormalization
import Submission.DifferentialGeometry.Topology.Embedding.LinearEquiv
import Submission.DifferentialGeometry.Topology.Manifold.StereographicChart
import Submission.DifferentialGeometry.Topology.Manifold.StereographicClosedBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.Handle

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

private local instance _root_.Submission.DifferentialGeometry.Topology.Handle.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry (k : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = k + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Handle.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Handle.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry target :: scope.openDecls } }

theorem isSmoothEmbedding_stereographic_symm_closedCell (m : ℕ)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1)
    {r : ℝ} (hr : r ≠ 0) :
    Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
      (fun x : ClosedCell (m + 1) => (stereographic' (m + 1) p).symm (r • x.val)) := by
  let A : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)
  have hA := (closedCellInclusion_isSmoothEmbedding m).continuousLinearEquiv_comp A
  have hc := DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph
    (n := m + 1) p
  exact ⟨hA.isImmersion.isLocalDiffeomorphOn_comp (fun x => hc x.val),
    ((stereographic' (m + 1) p).symm.isOpenEmbedding (by simp)).isEmbedding.comp hA.isEmbedding⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isSmoothEmbedding_stereographic_symm_closedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isSmoothEmbedding_stereographic_symm_closedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isSmoothEmbedding_stereographic_symm_closedCell ``Submission.DifferentialGeometry.Topology.Handle.isSmoothEmbedding_stereographic_symm_closedCell

theorem range_stereographic_symm_closedCell (m : ℕ)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1)
    {r : ℝ} (hr : 0 < r) :
    _root_.Set.range (fun x : ClosedCell (m + 1) => (stereographic' (m + 1) p).symm (r • x.val)) =
      (stereographic' (m + 1) p).symm '' _root_.Metric.closedBall 0 r := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨r • x.val, ?_, rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left x.property hr.le
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖r⁻¹ • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      simpa only [inv_mul_cancel₀ hr.ne'] using
        mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) (inv_nonneg.mpr hr.le)
    refine ⟨⟨r⁻¹ • x, hx'⟩, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.range_stereographic_symm_closedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.range_stereographic_symm_closedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.range_stereographic_symm_closedCell ``Submission.DifferentialGeometry.Topology.Handle.range_stereographic_symm_closedCell

theorem exists_isSmoothEmbedding_closedCell_complement_sphere (m : ℕ)
    {u : ClosedCell (m + 1) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    ∃ v : ClosedCell (m + 1) →
        Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1,
      Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ v ∧
      range v = closure ((_root_.Set.range u)ᶜ) := by
  obtain ⟨p, H, _, _, _, hHimage, _⟩ :=
    exists_isotopy_image_closedCell_sphere m (r := 2) (by norm_num) hu
  let c := stereographic' (m + 1) p
  let a := fun x : ClosedCell (m + 1) => c.symm ((2 : ℝ) • x.val)
  have ha := isSmoothEmbedding_stereographic_symm_closedCell m p (r := 2) (by norm_num)
  let N := DifferentialGeometry.Topology.Manifold.sphereAntipodalDiffeomorph
    (E := EuclideanSpace ℝ (Fin ((m + 1) + 1))) (n := m + 1)
  let v := H 1 ∘ N ∘ a
  have hv : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ v :=
    (ha.diffeomorph_comp N).diffeomorph_comp (H 1)
  have hcap : _root_.Set.range a = c.symm '' _root_.Metric.closedBall 0 2 :=
    range_stereographic_symm_closedCell m p (by norm_num)
  have hN : N '' (c.symm '' _root_.Metric.closedBall 0 2) =
      (interior (c.symm '' _root_.Metric.closedBall 0 2))ᶜ := by
    rw [DifferentialGeometry.Topology.Manifold.interior_image_stereographic_symm_closedBall
      p (by norm_num)]
    change Neg.neg '' ((stereographic' (m + 1) p).symm '' _root_.Metric.closedBall 0 2) = _
    simpa only [show (4 : ℝ) / 2 = 2 by norm_num] using
      DifferentialGeometry.Topology.Manifold.antipodal_image_stereographic_symm_closedBall
        p (r := 2) (by norm_num)
  refine ⟨v, hv, ?_⟩
  change _root_.Set.range (H 1 ∘ (N ∘ a)) = _
  rw [_root_.Set.range_comp, _root_.Set.range_comp, hcap, hN]
  have hi : H 1 '' interior (c.symm '' _root_.Metric.closedBall 0 2) = interior (_root_.Set.range u) :=
    ((H 1).toHomeomorph.image_interior _).trans (congrArg interior hHimage)
  have hcompl : H 1 '' (interior (c.symm '' _root_.Metric.closedBall 0 2))ᶜ =
      (H 1 '' interior (c.symm '' _root_.Metric.closedBall 0 2))ᶜ := (H 1).toEquiv.image_compl _
  rw [hcompl, hi, closure_compl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.exists_isSmoothEmbedding_closedCell_complement_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.exists_isSmoothEmbedding_closedCell_complement_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.exists_isSmoothEmbedding_closedCell_complement_sphere ``Submission.DifferentialGeometry.Topology.Handle.exists_isSmoothEmbedding_closedCell_complement_sphere

theorem isConnected_compl_range_closedCell_sphere (m : ℕ)
    {u : ClosedCell (m + 1) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    IsConnected (_root_.Set.range u)ᶜ := by
  obtain ⟨v, hv, hvrange⟩ := exists_isSmoothEmbedding_closedCell_complement_sphere m hu
  have hc := isConnected_interior_range_closedCell_sphere m hv
  rwa [hvrange, closure_compl, interior_compl,
    closure_interior_range_closedCell_sphere m hu] at hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isConnected_compl_range_closedCell_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isConnected_compl_range_closedCell_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isConnected_compl_range_closedCell_sphere ``Submission.DifferentialGeometry.Topology.Handle.isConnected_compl_range_closedCell_sphere

end DifferentialGeometry.Topology.Handle
