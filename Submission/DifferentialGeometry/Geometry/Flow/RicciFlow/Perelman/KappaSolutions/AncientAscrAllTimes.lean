import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientAscrInfinite
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AscrCurvatureNormalization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance ancientAscrAllTimesTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesTopology
local instance ancientAscrAllTimesCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesCharted
local instance ancientAscrAllTimesSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesSmooth
local instance ancientAscrAllTimesC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrAllTimesC1

theorem ancientKappaThree_ascr_eq_top {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoncompact : NoncompactSpace F.M) (t0 : ℝ) (ht0 : t0 ∈ D.carrier) (p : F.M) :
    asymptoticScalarCurvatureRatio (I := I) (F.S.base.metric t0) p = ⊤ := by
  have ht0le : t0 ≤ 0 := by
    simpa only [hF.carrier_eq, Set.mem_Iic] using ht0
  obtain ⟨hQ, hdata⟩ :=
    ancientKappa_exists_curvatureNormalization_ascr F hF t0 ht0le p
  let G := curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
    t0 (F.S.scalar t0 p) hQ ht0 p
  have hG : IsAncientKappaSolution (I := I) kappa G := hdata.1
  have hnoncompactG : @NoncompactSpace G.M G.topology := by
    change @NoncompactSpace F.M F.topology
    exact hnoncompact
  have hascr :
      @asymptoticScalarCurvatureRatio E _ _ _ _ H _ I F.M F.topology F.charted F.smooth
      (G.S.base.metric 0) p =
      asymptoticScalarCurvatureRatio (F.S.base.metric t0) p := hdata.2.2 p
  calc
    asymptoticScalarCurvatureRatio (F.S.base.metric t0) p =
        @asymptoticScalarCurvatureRatio E _ _ _ _ H _ I F.M F.topology F.charted F.smooth
          (G.S.base.metric 0) p :=
      hascr.symm
    _ = ⊤ := ancientKappaThree_terminal_ascr_eq_top G hG hdim hnoncompactG p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_ascr_eq_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_ascr_eq_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_ascr_eq_top ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_ascr_eq_top

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
