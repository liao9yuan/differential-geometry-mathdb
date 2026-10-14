import Submission.DifferentialGeometry.Topology.Simplex.VertexMap
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Simplex
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


def vertexMapToHull (v : ι → E) : C(stdSimplex ℝ ι, convexHull ℝ (Set.range v)) where
  toFun x := ⟨vertexMap v x, vertexMap_mem_convexHull v x⟩
  continuous_toFun := (vertexMap v).continuous.subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexMapToHull then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexMapToHull"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexMapToHull ``Submission.DifferentialGeometry.Simplex.vertexMapToHull


theorem vertexMapToHull_surjective (v : ι → E) : Function.Surjective (vertexMapToHull v) := by
  intro x
  have hx : x.val ∈ Set.range (vertexMap v) := (range_vertexMap v).symm ▸ x.prop
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexMapToHull_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexMapToHull_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexMapToHull_surjective ``Submission.DifferentialGeometry.Simplex.vertexMapToHull_surjective

def vertexHomeomorphism {v : ι → E} (hv : AffineIndependent ℝ v) :
    stdSimplex ℝ ι ≃ₜ convexHull ℝ (Set.range v) :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (vertexMapToHull v)
    ⟨fun _ _ h => vertexMap_injective hv (congrArg Subtype.val h), vertexMapToHull_surjective v⟩)
    (vertexMapToHull v).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexHomeomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexHomeomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexHomeomorphism ``Submission.DifferentialGeometry.Simplex.vertexHomeomorphism


@[simp]
theorem vertexHomeomorphism_apply {v : ι → E} (hv : AffineIndependent ℝ v)
    (x : stdSimplex ℝ ι) : (vertexHomeomorphism hv x : E) = ∑ i, x.val i • v i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexHomeomorphism_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexHomeomorphism_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexHomeomorphism_apply ``Submission.DifferentialGeometry.Simplex.vertexHomeomorphism_apply

end DifferentialGeometry.Simplex
