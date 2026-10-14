import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Classification

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HamiltonPositiveRicci

open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem hamilton_positive_ricci
    (hM : isClosedThreeManifold (I := I) (M := M))
    (hpos : admitsPositiveRicci (I := I) (M := M)) :
    admitsConstantPositiveSectionalCurvature (I := I) (M := M) ∧
      isSphericalSpaceForm (I := I) (M := M) := by
  have : I.Boundaryless := hM.2.2.1
  have : NeZero (Module.finrank Real E) := ⟨by
    rw [hM.2.2.2]; norm_num⟩
  have hconst :
      admitsConstantPositiveSectionalCurvature (I := I) (M := M) :=
    hamilton_admits_constant_positive_sectional_curvature
      (I := I) (M := M) hM hpos
  exact ⟨hconst,
    (constant_positive_sectional_curvature_iff_spherical_space_form
      (I := I) (M := M) hM).1 hconst⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_positive_ricci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_positive_ricci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_positive_ricci ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_positive_ricci


end HamiltonPositiveRicci
end RicciFlow
end PDE
end DifferentialGeometry
