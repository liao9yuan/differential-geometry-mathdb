import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexMaps
import Mathlib.Analysis.Normed.Module.Convex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Actual affine singular simplices and their original faces -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual barycentric affine simplex with the specified ordered vertices. -/
def affineSimplexMap {ι : Type*} [Fintype ι] (v : ι → E) : C(stdSimplex ℝ ι, E) :=
  ⟨fun t => ∑ i, t.val i • v i,
    continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).smul continuous_const)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSimplexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSimplexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSimplexMap ``Submission.DifferentialGeometry.Topology.affineSimplexMap

/-- Its original barycentric vertex evaluates to the specified vertex. -/
theorem affineSimplexMap_vertex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → E) (i : ι) : affineSimplexMap v (stdSimplex.vertex i) = v i := by
  change ∑ j, (Pi.single i (1 : ℝ) : ι → ℝ) j • v j = v i
  simp [Pi.single_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSimplexMap_vertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSimplexMap_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSimplexMap_vertex ``Submission.DifferentialGeometry.Topology.affineSimplexMap_vertex

/-- Every point of the actual affine simplex lies in the convex hull of
its original vertices. -/
theorem affineSimplexMap_mem_convexHull {ι : Type*} [Fintype ι] (v : ι → E)
    (t : stdSimplex ℝ ι) : affineSimplexMap v t ∈ convexHull ℝ (_root_.Set.range v) :=
  (convex_convexHull ℝ (_root_.Set.range v)).sum_mem (fun i _ => t.property.1 i) t.property.2
    (fun i _ => subset_convexHull ℝ (_root_.Set.range v) ⟨i, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSimplexMap_mem_convexHull then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSimplexMap_mem_convexHull"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSimplexMap_mem_convexHull ``Submission.DifferentialGeometry.Topology.affineSimplexMap_mem_convexHull

/-- The affine simplex respects the original barycentric pushforward for
every map of its finite vertex sets. -/
theorem affineSimplexMap_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (v : κ → E) (t : stdSimplex ℝ ι) :
    affineSimplexMap v (stdSimplex.map f t) = affineSimplexMap (v ∘ f) t := by
  classical
  change (∑ j, (FunOnFinite.linearMap ℝ ℝ f t.val) j • v j) = ∑ i, t.val i • v (f i)
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_smul]
  calc
    (∑ j, ∑ i with f i = j, t.val i • v j) =
        ∑ j, ∑ i with f i = j, t.val i • v (f i) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i, t.val i • v (f i) := Finset.sum_fiberwise Finset.univ f _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSimplexMap_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSimplexMap_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSimplexMap_map ``Submission.DifferentialGeometry.Topology.affineSimplexMap_map

/-- The same affine map as an original singular simplex. -/
def affineSingularSimplex (n : ℕ) (v : Fin (n + 1) → E) : integralSingularSimplex n E :=
  (integralSingularSimplexEquiv n E).symm (affineSimplexMap v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularSimplex ``Submission.DifferentialGeometry.Topology.affineSingularSimplex

/-- Its original ordered face deletes exactly that same vertex. -/
theorem affineSingularSimplex_face (n : ℕ) (v : Fin (n + 2) → E) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of E)).δ i (affineSingularSimplex (n + 1) v) =
      affineSingularSimplex n (v ∘ i.succAbove) := by
  apply (integralSingularSimplexEquiv n E).injective
  apply ContinuousMap.ext
  intro t
  change (TopCat.of E).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of E)).δ i
    (affineSingularSimplex (n + 1) v)) t = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv (n + 1) E
    ((integralSingularSimplexEquiv (n + 1) E).symm (affineSimplexMap v))
      (stdSimplex.map i.succAbove t) =
    integralSingularSimplexEquiv n E ((integralSingularSimplexEquiv n E).symm
      (affineSimplexMap (v ∘ i.succAbove))) t
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact affineSimplexMap_map i.succAbove v t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularSimplex_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularSimplex_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularSimplex_face ``Submission.DifferentialGeometry.Topology.affineSingularSimplex_face

end DifferentialGeometry.Topology
