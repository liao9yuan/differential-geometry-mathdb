import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Restriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D D' : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} I D}
  {kappa : ℝ}

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem IsAncientKappaSolution.timeRestrict
    (hF : IsAncientKappaSolution kappa F)
    (hcarrier : D'.carrier = D.carrier) (hregular : D'.regular = D.regular) :
    IsAncientKappaSolution kappa (F.timeRestrict D' hcarrier.subset hregular.subset) where
  kappa_pos := hF.kappa_pos
  carrier_eq := hcarrier.trans hF.carrier_eq
  regular_eq := hregular.trans hF.regular_eq
  connected := hF.connected
  complete t ht := hF.complete t (hcarrier.subset ht)
  nonnegativeCurvatureOperator t ht := hF.nonnegativeCurvatureOperator t (hcarrier.subset ht)
  globalScalarBound := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    exact ⟨C, fun t ht x => hC t (hcarrier.subset ht) x⟩
  noncollapsed := by
    intro t B
    exact hF.noncollapsed ⟨(t : ℝ), hcarrier.subset t.2⟩ ⟨B.center, B.radius, B.radius_pos⟩
  notFlat := by
    obtain ⟨t, ht, x, hx⟩ := hF.notFlat
    exact ⟨t, hcarrier.symm.subset ht, x, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.timeRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.timeRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.timeRestrict ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.timeRestrict

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
