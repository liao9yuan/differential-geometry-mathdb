import Submission.DifferentialGeometry.Topology.Manifold.BoundaryCollar.ChartField

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Topology _root_.Filter _root_.Manifold _root_.WithLp
open scoped _root_.ContDiff
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.BoundaryCollar


def normalSplit (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ]
    (ℝ × EuclideanSpace ℝ (Fin n)) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun v => (v 0, _root_.WithLp.toLp 2 (fun i => v i.succ))
      invFun := fun p => _root_.WithLp.toLp 2 (Fin.cons p.1 (_root_.WithLp.ofLp p.2))
      left_inv := by
        intro v
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      right_inv := by intro p; rfl
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.normalSplit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.normalSplit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.normalSplit ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.normalSplit


@[simp] theorem normalSplit_fst (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    (normalSplit n v).1 = v 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_fst ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_fst


@[simp] theorem normalSplit_symm_zero (n : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    (normalSplit n).symm p 0 = p.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_symm_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_symm_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_symm_zero ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_symm_zero


theorem normalSplit_symm_mem_range_iff (n : ℕ) (q : ℝ × EuclideanSpace ℝ (Fin n)) :
    (normalSplit n).symm q ∈ _root_.Set.range (𝓡∂ (n + 1)) ↔ 0 ≤ q.1 := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_symm_mem_range_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_symm_mem_range_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_symm_mem_range_iff ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_symm_mem_range_iff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]


def normalChartField (p : M) (V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y) :
    (ℝ × EuclideanSpace ℝ (Fin n)) → ℝ × EuclideanSpace ℝ (Fin n) :=
  fun q => normalSplit n (chartField (𝓡∂ (n + 1)) p V ((normalSplit n).symm q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.normalChartField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.normalChartField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.normalChartField ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.normalChartField


theorem normalSplit_extChartAt_boundary [IsManifold (𝓡∂ (n + 1)) 1 M]
    {p : M} (hp : (𝓡∂ (n + 1)).IsBoundaryPoint p) :
    normalSplit n (extChartAt (𝓡∂ (n + 1)) p p) =
      (0, (normalSplit n (extChartAt (𝓡∂ (n + 1)) p p)).2) := by
  apply Prod.ext
  · exact (chartHeight_eq_zero_iff p (mem_chart_source _ p)).mpr hp
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_extChartAt_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_extChartAt_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_extChartAt_boundary ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.normalSplit_extChartAt_boundary

theorem exists_normalChartField_neighborhood [IsManifold (𝓡∂ (n + 1)) ∞ M]
    {p : M} (hp : (𝓡∂ (n + 1)).IsBoundaryPoint p)
    {V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y}
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hpos : 0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p)) :
    ∃ U : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsOpen U ∧
      (0, (normalSplit n (extChartAt (𝓡∂ (n + 1)) p p)).2) ∈ U ∧
      ContDiffOn ℝ ∞ (normalChartField p V)
        ((_root_.Set.Ici (0 : ℝ) ×ˢ (_root_.Set.univ : Set (EuclideanSpace ℝ (Fin n)))) ∩ U) ∧
      (∀ q ∈ (_root_.Set.Ici (0 : ℝ) ×ˢ (_root_.Set.univ : Set (EuclideanSpace ℝ (Fin n)))) ∩ U,
        (normalSplit n).symm q ∈ (extChartAt (𝓡∂ (n + 1)) p).target) ∧
      0 < (normalChartField p V
        (0, (normalSplit n (extChartAt (𝓡∂ (n + 1)) p p)).2)).1 := by
  let I := 𝓡∂ (n + 1)
  let a := extChartAt I p p
  have ha := normalSplit_extChartAt_boundary hp
  obtain ⟨B, hB, hBT⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
    (extChartAt_target_mem_nhdsWithin (I := I) p)
  obtain ⟨O, hOB, hO, haO⟩ := mem_nhds_iff.mp hB
  let U := (normalSplit n).symm ⁻¹' O
  have hU : IsOpen U := hO.preimage (normalSplit n).symm.continuous
  have h0U : (0, (normalSplit n a).2) ∈ U := by
    rw [← ha]
    change (normalSplit n).symm (normalSplit n a) ∈ O
    simpa only [(normalSplit n).symm_apply_apply] using haO
  have hmaps : _root_.Set.MapsTo (normalSplit n).symm
      ((_root_.Set.Ici (0 : ℝ) ×ˢ (_root_.Set.univ : Set (EuclideanSpace ℝ (Fin n)))) ∩ U)
      (extChartAt I p).target := by
    intro q hq
    exact hBT ⟨hOB hq.2, (normalSplit_symm_mem_range_iff n q).mpr hq.1.1⟩
  refine ⟨U, hU, h0U, ?_, hmaps, ?_⟩
  · exact (normalSplit n).contDiff.comp_contDiffOn
      ((contDiffOn_chartField I p hV).comp (normalSplit n).symm.contDiff.contDiffOn hmaps)
  · rw [← ha]
    change 0 < (normalSplit n (chartField I p V ((normalSplit n).symm (normalSplit n a)))).1
    rw [(normalSplit n).symm_apply_apply, normalSplit_fst, chartField_self]
    exact hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.exists_normalChartField_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.exists_normalChartField_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.exists_normalChartField_neighborhood ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.exists_normalChartField_neighborhood

end DifferentialGeometry.Manifold.BoundaryCollar
