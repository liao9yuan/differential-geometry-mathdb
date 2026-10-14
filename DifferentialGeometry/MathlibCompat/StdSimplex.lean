import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.Basic

/-! Compatibility names for the native finite standard simplex of Mathlib v4.33.1.
The underlying type and its topology are unchanged. -/

noncomputable section

namespace DifferentialGeometry.MathlibCompat

abbrev StdSimplex (R I : Type*) [Semiring R] [PartialOrder R] [Fintype I] : Type _ :=
  ↥(_root_.stdSimplex R I)

namespace StdSimplex

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

abbrev weights (t : StdSimplex ℝ I) : I → ℝ := t.val

@[simp] lemma weights_nonneg (t : StdSimplex ℝ I) (i : I) : 0 ≤ t.weights i := t.property.1 i
@[simp] lemma sum_weights (t : StdSimplex ℝ I) : ∑ i, t.weights i = 1 := t.property.2

abbrev single [DecidableEq I] (i : I) : StdSimplex ℝ I := _root_.stdSimplex.vertex i
abbrev map (f : I → J) (t : StdSimplex ℝ I) : StdSimplex ℝ J := _root_.stdSimplex.map f t

lemma continuous_map (R : Type*) [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [TopologicalSpace R] [IsTopologicalSemiring R] (f : I → J) :
    Continuous (_root_.stdSimplex.map (S := R) f) := _root_.stdSimplex.continuous_map f

lemma isEmbedding_toFun_comp_weights (R : Type*) [Semiring R] [PartialOrder R]
    [TopologicalSpace R] (I : Type*) [Fintype I] :
    Topology.IsEmbedding (fun t : StdSimplex R I => (t.val : I → R)) :=
  Topology.IsEmbedding.subtypeVal

lemma isBounded_range_toFun_comp_weights (I : Type*) [Fintype I] :
    Bornology.IsBounded (Set.range (weights (I := I))) := by
  simpa only [weights, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using bounded_stdSimplex I

lemma diam_range_toFun_comp_weights_subset_closedBall (I : Type*) [Fintype I] :
    Metric.diam (Set.range (weights (I := I))) ≤ 1 := by
  simpa only [weights, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
    (diam_stdSimplex_le (ι := I))

def affineMapMk (v : I → StdSimplex ℝ J) (t : StdSimplex ℝ I) : StdSimplex ℝ J :=
  ⟨fun j => ∑ i, t.weights i * (v i).weights j,
    fun j => Finset.sum_nonneg (fun i _ => mul_nonneg (t.property.1 i) ((v i).property.1 j)),
    by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sum_weights, mul_one]
      exact sum_weights t⟩

@[simp] lemma weights_affineMapMk (v : I → StdSimplex ℝ J) (t : StdSimplex ℝ I) (j : J) :
    (affineMapMk v t).weights j = ∑ i, t.weights i * (v i).weights j := rfl

@[simp] lemma affineMapMk_single [DecidableEq I] (v : I → StdSimplex ℝ J) (i : I) :
    affineMapMk v (single i) = v i := by
  apply Subtype.ext
  funext j
  simp [affineMapMk, weights, Pi.single_apply]

@[simp] lemma affineMapMk_single_vertices [DecidableEq I] (t : StdSimplex ℝ I) :
    affineMapMk (fun i => single i) t = t := by
  apply Subtype.ext
  funext j
  simp [affineMapMk, weights, Pi.single_apply]

lemma affineMapMk_comp (v : J → StdSimplex ℝ K) (w : I → StdSimplex ℝ J)
    (t : StdSimplex ℝ I) :
    affineMapMk v (affineMapMk w t) = affineMapMk (affineMapMk v ∘ w) t := by
  apply Subtype.ext
  funext k
  change (∑ j, (∑ i, t.weights i * (w i).weights j) * (v j).weights k) =
    ∑ i, t.weights i * ∑ j, (w i).weights j * (v j).weights k
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

lemma affineMapMk_single_comp [DecidableEq J] (f : I → J) (t : StdSimplex ℝ I) :
    affineMapMk (fun i => single (f i)) t = map f t := by
  classical
  apply Subtype.ext
  funext j
  change (∑ i, t i * (Pi.single (f i) (1 : ℝ) : J → ℝ) j) =
    FunOnFinite.linearMap ℝ ℝ f t j
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Pi.single_apply, Finset.sum_filter, eq_comm]

abbrev barycenter [Nonempty I] : StdSimplex ℝ I := _root_.stdSimplex.barycenter

end StdSimplex

end DifferentialGeometry.MathlibCompat
