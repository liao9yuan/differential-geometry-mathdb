import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Analysis

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoEMetricSpace X]

private theorem exists_sphere_point_between {p x y : E} {r : ℝ}
    (hx : x ∈ _root_.Metric.closedBall p r) (hy : r ≤ _root_.Dist.dist y p) :
    ∃ z : E, _root_.Dist.dist z p = r ∧ _root_.Dist.dist x z ≤ _root_.Dist.dist x y ∧ _root_.Dist.dist z y ≤ _root_.Dist.dist x y := by
  let c : ℝ → E := AffineMap.lineMap x y
  have hc : Continuous (fun t => _root_.Dist.dist (c t) p) :=
    (AffineMap.lineMap_continuous (p := x) (q := y)).dist continuous_const
  have hends : r ∈ _root_.Set.Icc (_root_.Dist.dist (c 0) p) (_root_.Dist.dist (c 1) p) := by
    simpa only [c, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
      _root_.Metric.mem_closedBall, _root_.Set.mem_Icc] using
      And.intro hx hy
  obtain ⟨t, ht, htr⟩ := intermediate_value_Icc zero_le_one hc.continuousOn hends
  have hzseg : c t ∈ segment ℝ x y := lineMap_mem_segment ℝ x y ht
  have hd := dist_add_dist_of_mem_segment hzseg
  exact ⟨c t, htr, by linarith [dist_nonneg (x := c t) (y := y)],
    by linarith [dist_nonneg (x := x) (y := c t)]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.exists_sphere_point_between
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.exists_sphere_point_between target :: scope.openDecls } }

theorem lipschitzWith_piecewise_closedBall_of_eqOn_sphere
    {p : E} {r : ℝ} {f g : E → X} {K L : ℝ≥0}
    (hf : LipschitzOnWith K f (_root_.Metric.closedBall p r))
    (hg : LipschitzOnWith L g {x | r ≤ _root_.Dist.dist x p})
    (heq : _root_.Set.EqOn f g (_root_.Metric.sphere p r)) :
    letI : DecidablePred (· ∈ _root_.Metric.closedBall p r) := Classical.decPred _
    LipschitzWith (K + L) ((_root_.Metric.closedBall p r).piecewise f g) := by
  classical
  have hcross (x y : E) (hx : x ∈ _root_.Metric.closedBall p r) (hy : y ∉ _root_.Metric.closedBall p r) :
      edist (f x) (g y) ≤ ((K + L : ℝ≥0) : ℝ≥0∞) * _root_.EDist.edist x y := by
    have hyr : r ≤ _root_.Dist.dist y p := (not_le.mp (by simpa only [_root_.Metric.mem_closedBall, _root_.Set.mem_Icc] using hy)).le
    obtain ⟨z, hz, hzx, hzy⟩ := exists_sphere_point_between hx hyr
    have hzball : z ∈ _root_.Metric.closedBall p r := mem_closedBall.mpr hz.le
    have hzsphere : z ∈ _root_.Metric.sphere p r := mem_sphere.mpr hz
    calc
      edist (f x) (g y) ≤ _root_.EDist.edist (f x) (f z) + _root_.EDist.edist (f z) (g y) := _root_.PseudoEMetricSpace.edist_triangle _ _ _
      _ = _root_.EDist.edist (f x) (f z) + _root_.EDist.edist (g z) (g y) := by rw [heq hzsphere]
      _ ≤ (K : ℝ≥0∞) * _root_.EDist.edist x z + (L : ℝ≥0∞) * _root_.EDist.edist z y :=
        add_le_add (hf hx hzball) (hg hz.ge hyr)
      _ ≤ (K : ℝ≥0∞) * _root_.EDist.edist x y + (L : ℝ≥0∞) * _root_.EDist.edist x y := by
        apply add_le_add <;> apply mul_le_mul_right
        · simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hzx
        · simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hzy
      _ = _ := by rw [ENNReal.coe_add, add_mul]
  intro x y
  by_cases hx : x ∈ _root_.Metric.closedBall p r
  · by_cases hy : y ∈ _root_.Metric.closedBall p r
    · rw [_root_.Set.piecewise_eq_of_mem _ _ _ hx, _root_.Set.piecewise_eq_of_mem _ _ _ hy]
      exact (hf hx hy).trans
        (mul_le_mul_left (by exact_mod_cast le_add_of_nonneg_right L.coe_nonneg) _)
    · rw [_root_.Set.piecewise_eq_of_mem _ _ _ hx, _root_.Set.piecewise_eq_of_notMem _ _ _ hy]
      exact hcross x y hx hy
  · by_cases hy : y ∈ _root_.Metric.closedBall p r
    · rw [_root_.Set.piecewise_eq_of_notMem _ _ _ hx, _root_.Set.piecewise_eq_of_mem _ _ _ hy, _root_.PseudoEMetricSpace.edist_comm, _root_.PseudoEMetricSpace.edist_comm x y]
      exact hcross y x hy hx
    · rw [_root_.Set.piecewise_eq_of_notMem _ _ _ hx, _root_.Set.piecewise_eq_of_notMem _ _ _ hy]
      have hxr : r ≤ _root_.Dist.dist x p := (not_le.mp (by simpa only [_root_.Metric.mem_closedBall, _root_.Set.mem_Icc] using hx)).le
      have hyr : r ≤ _root_.Dist.dist y p := (not_le.mp (by simpa only [_root_.Metric.mem_closedBall, _root_.Set.mem_Icc] using hy)).le
      exact (hg hxr hyr).trans
        (mul_le_mul_left (by exact_mod_cast le_add_of_nonneg_left K.coe_nonneg) _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lipschitzWith_piecewise_closedBall_of_eqOn_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lipschitzWith_piecewise_closedBall_of_eqOn_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lipschitzWith_piecewise_closedBall_of_eqOn_sphere ``Submission.DifferentialGeometry.Analysis.lipschitzWith_piecewise_closedBall_of_eqOn_sphere

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Analysis

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoEMetricSpace X]

theorem lipschitzOnWith_piecewise_closedBall_of_eqOn_sphere
    {S : Set E} (hS : Convex ℝ S) {p : E} {r : ℝ} {f g : E → X} {K L : ℝ≥0}
    (hf : LipschitzOnWith K f (S ∩ _root_.Metric.closedBall p r))
    (hg : LipschitzOnWith L g (S ∩ {x | r ≤ _root_.Dist.dist x p}))
    (heq : _root_.Set.EqOn f g (S ∩ _root_.Metric.sphere p r)) :
    letI : DecidablePred (· ∈ _root_.Metric.closedBall p r) := Classical.decPred _
    LipschitzOnWith (K + L) ((_root_.Metric.closedBall p r).piecewise f g) S := by
  classical
  have hcross (x y : E) (hxS : x ∈ S) (hyS : y ∈ S)
      (hx : x ∈ _root_.Metric.closedBall p r) (hy : y ∉ _root_.Metric.closedBall p r) :
      edist (f x) (g y) ≤ ((K + L : ℝ≥0) : ℝ≥0∞) * _root_.EDist.edist x y := by
    have hyr : r ≤ _root_.Dist.dist y p := (not_le.mp hy).le
    let c : ℝ → E := AffineMap.lineMap x y
    have hc : Continuous (fun t => _root_.Dist.dist (c t) p) :=
      (AffineMap.lineMap_continuous (p := x) (q := y)).dist continuous_const
    have hends : r ∈ _root_.Set.Icc (_root_.Dist.dist (c 0) p) (_root_.Dist.dist (c 1) p) := by
      simpa only [c, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
        _root_.Metric.mem_closedBall, _root_.Set.mem_Icc] using And.intro hx hyr
    obtain ⟨t, ht, htr⟩ := intermediate_value_Icc zero_le_one hc.continuousOn hends
    have hzseg : c t ∈ segment ℝ x y := lineMap_mem_segment ℝ x y ht
    have hzS : c t ∈ S := hS.segment_subset hxS hyS hzseg
    have hd := dist_add_dist_of_mem_segment hzseg
    have hzx : _root_.Dist.dist x (c t) ≤ _root_.Dist.dist x y := by linarith [dist_nonneg (x := c t) (y := y)]
    have hzy : _root_.Dist.dist (c t) y ≤ _root_.Dist.dist x y := by linarith [dist_nonneg (x := x) (y := c t)]
    calc
      edist (f x) (g y) ≤ _root_.EDist.edist (f x) (f (c t)) + _root_.EDist.edist (f (c t)) (g y) :=
        _root_.PseudoEMetricSpace.edist_triangle _ _ _
      _ = _root_.EDist.edist (f x) (f (c t)) + _root_.EDist.edist (g (c t)) (g y) := by rw [heq ⟨hzS, htr⟩]
      _ ≤ (K : ℝ≥0∞) * _root_.EDist.edist x (c t) + (L : ℝ≥0∞) * _root_.EDist.edist (c t) y :=
        add_le_add (hf ⟨hxS, hx⟩ ⟨hzS, htr.le⟩) (hg ⟨hzS, htr.ge⟩ ⟨hyS, hyr⟩)
      _ ≤ (K : ℝ≥0∞) * _root_.EDist.edist x y + (L : ℝ≥0∞) * _root_.EDist.edist x y := by
        apply add_le_add <;> apply mul_le_mul' le_rfl
        · simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hzx
        · simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hzy
      _ = _ := by rw [ENNReal.coe_add, add_mul]
  intro x hxS y hyS
  by_cases hx : x ∈ _root_.Metric.closedBall p r
  · by_cases hy : y ∈ _root_.Metric.closedBall p r
    · rw [_root_.Set.piecewise_eq_of_mem _ _ _ hx, _root_.Set.piecewise_eq_of_mem _ _ _ hy]
      exact (hf ⟨hxS, hx⟩ ⟨hyS, hy⟩).trans
        (mul_le_mul' (by exact_mod_cast le_add_of_nonneg_right L.coe_nonneg) le_rfl)
    · rw [_root_.Set.piecewise_eq_of_mem _ _ _ hx, _root_.Set.piecewise_eq_of_notMem _ _ _ hy]
      exact hcross x y hxS hyS hx hy
  · by_cases hy : y ∈ _root_.Metric.closedBall p r
    · rw [_root_.Set.piecewise_eq_of_notMem _ _ _ hx, _root_.Set.piecewise_eq_of_mem _ _ _ hy,
        _root_.PseudoEMetricSpace.edist_comm, _root_.PseudoEMetricSpace.edist_comm x y]
      exact hcross y x hyS hxS hy hx
    · rw [_root_.Set.piecewise_eq_of_notMem _ _ _ hx, _root_.Set.piecewise_eq_of_notMem _ _ _ hy]
      have hxr : r ≤ _root_.Dist.dist x p := (not_le.mp hx).le
      have hyr : r ≤ _root_.Dist.dist y p := (not_le.mp hy).le
      exact (hg ⟨hxS, hxr⟩ ⟨hyS, hyr⟩).trans
        (mul_le_mul' (by exact_mod_cast le_add_of_nonneg_left K.coe_nonneg) le_rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lipschitzOnWith_piecewise_closedBall_of_eqOn_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lipschitzOnWith_piecewise_closedBall_of_eqOn_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lipschitzOnWith_piecewise_closedBall_of_eqOn_sphere ``Submission.DifferentialGeometry.Analysis.lipschitzOnWith_piecewise_closedBall_of_eqOn_sphere

end DifferentialGeometry.Analysis

end

end
