import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.ContinuousMap.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Finset
namespace DifferentialGeometry.Simplex
variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


def vertexMap (v : ι → E) : C(stdSimplex ℝ ι, E) where
  toFun x := ∑ i, x.val i • v i
  continuous_toFun := continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp continuous_subtype_val).smul continuous_const)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexMap ``Submission.DifferentialGeometry.Simplex.vertexMap


@[simp]
theorem vertexMap_apply (v : ι → E) (x : stdSimplex ℝ ι) :
    vertexMap v x = ∑ i, x.val i • v i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexMap_apply ``Submission.DifferentialGeometry.Simplex.vertexMap_apply


theorem vertexMap_mem_convexHull (v : ι → E) (x : stdSimplex ℝ ι) :
    vertexMap v x ∈ convexHull ℝ (Set.range v) :=
  (convex_convexHull ℝ _).sum_mem (fun i _ => x.prop.1 i) x.prop.2
    (fun i _ => subset_convexHull ℝ _ (Set.mem_range_self i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexMap_mem_convexHull then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexMap_mem_convexHull"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexMap_mem_convexHull ``Submission.DifferentialGeometry.Simplex.vertexMap_mem_convexHull

theorem vertexMap_map (v : κ → E) (f : ι → κ) (x : stdSimplex ℝ ι) :
    vertexMap v (stdSimplex.map f x) = vertexMap (v ∘ f) x := by
  classical
  change (∑ j, FunOnFinite.linearMap ℝ ℝ f x.val j • v j) =
    ∑ i, x.val i • (v ∘ f) i
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_smul]
  have h : (∑ j, ∑ i ∈ _root_.Finset.univ with f i = j, x.val i • v j) =
      ∑ j, ∑ i ∈ _root_.Finset.univ with f i = j, x.val i • v (f i) := by
    apply _root_.Finset.sum_congr rfl
    intro j _
    apply _root_.Finset.sum_congr rfl
    intro i hi
    rw [(mem_filter.mp hi).2]
  rw [h]
  exact Finset.sum_fiberwise Finset.univ f (fun i => x.val i • v (f i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexMap_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexMap_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexMap_map ``Submission.DifferentialGeometry.Simplex.vertexMap_map

theorem range_vertexMap (v : ι → E) :
    Set.range (vertexMap v) = convexHull ℝ (Set.range v) := by
  classical
  let L : (ι → ℝ) →ₗ[ℝ] E := ∑ i, (LinearMap.proj i).smulRight (v i)
  have hL : ∀ x : ι → ℝ, L x = ∑ i, x i • v i := by
    intro x
    simp [L, LinearMap.sum_apply]
  have hr : Set.range (vertexMap v) = L '' stdSimplex ℝ ι := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.prop, hL x.val⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hL x).symm⟩
  rw [hr, ← convexHull_rangle_single_eq_stdSimplex, LinearMap.image_convexHull, ← Set.range_comp]
  congr 2
  funext i
  simp [hL, Pi.single_apply, eq_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.range_vertexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.range_vertexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.range_vertexMap ``Submission.DifferentialGeometry.Simplex.range_vertexMap

theorem vertexMap_injective {v : ι → E} (hv : AffineIndependent ℝ v) :
    Function.Injective (vertexMap v) := by
  intro x y h
  apply Subtype.ext
  apply (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ v).mp hv
    x.val y.val x.prop.2 y.prop.2
  rw [Finset.affineCombination_eq_linear_combination _ _ _ x.prop.2,
    Finset.affineCombination_eq_linear_combination _ _ _ y.prop.2]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexMap_injective ``Submission.DifferentialGeometry.Simplex.vertexMap_injective

end DifferentialGeometry.Simplex
