import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! Compatibility names for the native finite standard simplex of Mathlib v4.33.1.
The underlying type and its topology are unchanged. -/

noncomputable section

namespace DifferentialGeometry.MathlibCompat

abbrev StdSimplex (R I : Type*) [Semiring R] [PartialOrder R] [Fintype I] : Type _ :=
  ↥(_root_.stdSimplex R I)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex

namespace StdSimplex

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

abbrev weights (t : StdSimplex ℝ I) : I → ℝ := t.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.weights then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.weights"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.weights ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.weights

@[simp] lemma weights_nonneg (t : StdSimplex ℝ I) (i : I) : 0 ≤ t.weights i := t.property.1 i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.weights_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.weights_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.weights_nonneg ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.weights_nonneg
@[simp] lemma sum_weights (t : StdSimplex ℝ I) : ∑ i, t.weights i = 1 := t.property.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.sum_weights then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.sum_weights"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.sum_weights ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.sum_weights

abbrev single [DecidableEq I] (i : I) : StdSimplex ℝ I := _root_.stdSimplex.vertex i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.single ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.single
abbrev map (f : I → J) (t : StdSimplex ℝ I) : StdSimplex ℝ J := _root_.stdSimplex.map f t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.map ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.map

lemma continuous_map (R : Type*) [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [TopologicalSpace R] [IsTopologicalSemiring R] (f : I → J) :
    Continuous (_root_.stdSimplex.map (S := R) f) := _root_.stdSimplex.continuous_map f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.continuous_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.continuous_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.continuous_map ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.continuous_map

lemma isEmbedding_toFun_comp_weights (R : Type*) [Semiring R] [PartialOrder R]
    [TopologicalSpace R] (I : Type*) [Fintype I] :
    Topology.IsEmbedding (fun t : StdSimplex R I => (t.val : I → R)) :=
  Topology.IsEmbedding.subtypeVal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.isEmbedding_toFun_comp_weights then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.isEmbedding_toFun_comp_weights"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.isEmbedding_toFun_comp_weights ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.isEmbedding_toFun_comp_weights

lemma isBounded_range_toFun_comp_weights (I : Type*) [Fintype I] :
    Bornology.IsBounded (Set.range (weights (I := I))) := by
  simpa only [weights, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using bounded_stdSimplex I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.isBounded_range_toFun_comp_weights then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.isBounded_range_toFun_comp_weights"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.isBounded_range_toFun_comp_weights ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.isBounded_range_toFun_comp_weights

lemma diam_range_toFun_comp_weights_subset_closedBall (I : Type*) [Fintype I] :
    Metric.diam (Set.range (weights (I := I))) ≤ 1 := by
  simpa only [weights, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
    (diam_stdSimplex_le (ι := I))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall

def affineMapMk (v : I → StdSimplex ℝ J) (t : StdSimplex ℝ I) : StdSimplex ℝ J :=
  ⟨fun j => ∑ i, t.weights i * (v i).weights j,
    fun j => Finset.sum_nonneg (fun i _ => mul_nonneg (t.property.1 i) ((v i).property.1 j)),
    by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sum_weights, mul_one]
      exact sum_weights t⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk

@[simp] lemma weights_affineMapMk (v : I → StdSimplex ℝ J) (t : StdSimplex ℝ I) (j : J) :
    (affineMapMk v t).weights j = ∑ i, t.weights i * (v i).weights j := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.weights_affineMapMk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.weights_affineMapMk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.weights_affineMapMk ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.weights_affineMapMk

@[simp] lemma affineMapMk_single [DecidableEq I] (v : I → StdSimplex ℝ J) (i : I) :
    affineMapMk v (single i) = v i := by
  apply Subtype.ext
  funext j
  simp [affineMapMk, weights, Pi.single_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_single ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_single

@[simp] lemma affineMapMk_single_vertices [DecidableEq I] (t : StdSimplex ℝ I) :
    affineMapMk (fun i => single i) t = t := by
  apply Subtype.ext
  funext j
  simp [affineMapMk, weights, Pi.single_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_single_vertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_single_vertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_single_vertices ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_single_vertices

lemma affineMapMk_comp (v : J → StdSimplex ℝ K) (w : I → StdSimplex ℝ J)
    (t : StdSimplex ℝ I) :
    affineMapMk v (affineMapMk w t) = affineMapMk (affineMapMk v ∘ w) t := by
  apply Subtype.ext
  funext k
  change (∑ j, (∑ i, t.weights i * (w i).weights j) * (v j).weights k) =
    ∑ i, t.weights i * ∑ j, (w i).weights j * (v j).weights k
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_comp ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_comp

lemma affineMapMk_single_comp [DecidableEq J] (f : I → J) (t : StdSimplex ℝ I) :
    affineMapMk (fun i => single (f i)) t = map f t := by
  classical
  apply Subtype.ext
  funext j
  change (∑ i, t i * (Pi.single (f i) (1 : ℝ) : J → ℝ) j) =
    FunOnFinite.linearMap ℝ ℝ f t j
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Pi.single_apply, Finset.sum_filter, eq_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_single_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_single_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_single_comp ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.affineMapMk_single_comp

abbrev barycenter [Nonempty I] : StdSimplex ℝ I := _root_.stdSimplex.barycenter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MathlibCompat.StdSimplex.barycenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MathlibCompat.StdSimplex.barycenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MathlibCompat.StdSimplex.barycenter ``Submission.DifferentialGeometry.MathlibCompat.StdSimplex.barycenter

end StdSimplex

end DifferentialGeometry.MathlibCompat
