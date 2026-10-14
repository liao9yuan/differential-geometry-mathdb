import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientHomeomorph
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverCylinderQuotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} I ancientTimeInterval)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance sphereTwoDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoDimension target :: scope.openDecls } }

theorem AncientCylinderBranch.not_compactSpace
    (h : AncientCylinderBranch F) : ¬ CompactSpace F.M := by
  intro hcompact
  let _ : CompactSpace F.M := hcompact
  let _ : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ⟨sphereEquator 0⟩
  rcases h with ⟨C, htrivial | hantipodal | hdiagonal⟩
  · obtain ⟨e, _⟩ := htrivial.1
    have hc := e.toHomeomorph.symm.compactSpace
    exact (not_compactSpace_iff.mpr
      (inferInstance : NoncompactSpace ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) × ℝ))) hc
  · obtain ⟨e, _⟩ := hantipodal.1
    let _ : Nonempty SphereAntipodalQuotient :=
      ⟨SphereAntipodalQuotient.proj (sphereEquator 0)⟩
    have hc := e.toHomeomorph.symm.compactSpace
    exact (not_compactSpace_iff.mpr
      (inferInstance : NoncompactSpace (SphereAntipodalQuotient × ℝ))) hc
  · obtain ⟨e, _⟩ := hdiagonal.1
    obtain ⟨d, _⟩ := CylinderDiagonalQuotient.exists_homeomorph_orbitQuotient
    let _ : CompactSpace CylinderDiagonalQuotient := e.toHomeomorph.symm.compactSpace
    have hc := d.compactSpace
    exact (not_compactSpace_iff.mpr
      DifferentialGeometry.Geometry.noncompactSpace_cylinderDiagonalQuotient) hc

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch.not_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch.not_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch.not_compactSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch.not_compactSpace

theorem ancientKappa_curvatureOperatorPositive_of_compact {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    [CompactSpace F.M] : AncientPositiveCurvatureOperator F := by
  rcases (xor_iff_or_and_not_and _ _).mp
    (ancientKappa_three_dimensional_split_branch F hF hdim) with ⟨hpos | hcylinder, _⟩
  · exact hpos
  · exact (AncientCylinderBranch.not_compactSpace F hcylinder inferInstance).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_curvatureOperatorPositive_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_curvatureOperatorPositive_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_curvatureOperatorPositive_of_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_curvatureOperatorPositive_of_compact

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
