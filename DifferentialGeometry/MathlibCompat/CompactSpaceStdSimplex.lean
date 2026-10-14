import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Analysis.Convex.StdSimplex

/-!
Compatibility with Mathlib v4.33.1: singular simplices have domain
`stdSimplex ℝ (Fin (n + 1))`, whose compactness instance is already supplied by
`Mathlib.Analysis.Convex.StdSimplex`. The newer
`Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex` module concerns a
different representation and is not needed for this version of singular chains.
-/

open Simplicial

namespace DifferentialGeometry.MathlibCompat

universe u

/-- The image of a singular simplex is compact in the Mathlib v4.33.1 API. -/
theorem isCompact_singularSimplex_range (X : TopCat.{u}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    IsCompact (Set.range (X.toSSetObjEquiv _ σ)) :=
  isCompact_range (X.toSSetObjEquiv _ σ).continuous

end DifferentialGeometry.MathlibCompat
