import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalReducedVolume
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CollapsedReducedVolume

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff


def universalKappaTheta : ℝ :=
  Classical.choose (exists_collapsedVolumeTail_small (27 / 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaTheta then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaTheta"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaTheta ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaTheta

theorem universalKappaTheta_spec :
    0 < universalKappaTheta ∧ universalKappaTheta ≤ 1 ∧
      collapsedReducedVolumeTail (27 / 2) universalKappaTheta < Real.exp (-1) / 4 :=
  Classical.choose_spec (exists_collapsedVolumeTail_small (27 / 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaTheta_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaTheta_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaTheta_spec ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaTheta_spec


def universalKappaConstant : ℝ :=
  (4 * Real.pi * universalKappaTheta) ^ (3 / 2 : ℝ) *
    Real.exp (-((27 / 2 : ℝ) * universalKappaTheta)) * Real.exp (-1) / 4

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaConstant ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaConstant

theorem universalKappaConstant_pos : 0 < universalKappaConstant := by
  have htheta := universalKappaTheta_spec.1
  unfold universalKappaConstant
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaConstant_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaConstant_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaConstant_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaConstant_pos


theorem universalKappaConstant_normalization :
    (4 * Real.pi * universalKappaTheta) ^ (-(3 / 2 : ℝ)) *
      Real.exp ((27 / 2 : ℝ) * universalKappaTheta) * universalKappaConstant =
        Real.exp (-1) / 4 := by
  have hb : 0 < 4 * Real.pi * universalKappaTheta := by
    have htheta := universalKappaTheta_spec.1
    positivity
  have hp : (4 * Real.pi * universalKappaTheta) ^ (-(3 / 2 : ℝ)) *
      (4 * Real.pi * universalKappaTheta) ^ (3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hb, neg_add_cancel, Real.rpow_zero]
  have he : Real.exp ((27 / 2 : ℝ) * universalKappaTheta) *
      Real.exp (-((27 / 2 : ℝ) * universalKappaTheta)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  unfold universalKappaConstant
  calc
    _ = ((4 * Real.pi * universalKappaTheta) ^ (-(3 / 2 : ℝ)) *
          (4 * Real.pi * universalKappaTheta) ^ (3 / 2 : ℝ)) *
        (Real.exp ((27 / 2 : ℝ) * universalKappaTheta) *
          Real.exp (-((27 / 2 : ℝ) * universalKappaTheta))) * Real.exp (-1) / 4 := by ring
    _ = _ := by rw [hp, he]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaConstant_normalization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaConstant_normalization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaConstant_normalization ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaConstant_normalization

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance universalKappaTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaTopology
local instance universalKappaCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaCharted
local instance universalKappaSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaSmooth
local instance universalKappaT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaT2
local instance universalKappaSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalKappaSigma
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM : MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM target :: scope.openDecls } }


theorem ancientKappaThree_terminal_universal_noncollapsed
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnotround : ¬ IsShrinkingSphericalSpaceFormFlow F) (p : F.M)
    {r : ℝ} (hr : 0 < r)
    (hcontrol : ∀ x ∈ riemannianBallOf (F.S.base.metric 0) p r,
      r ^ 4 * F.rmNormSq (I := I) 0 x ≤ 1) :
    ENNReal.ofReal (universalKappaConstant * r ^ 3) ≤
      riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
        (riemannianBallOf (F.S.base.metric 0) p r) := by
  by_contra hvolume
  have htheta := universalKappaTheta_spec.1
  have hlower := ancientKappaThree_reducedVolume_lower F hF hdim hnotround p
    (mul_pos htheta (sq_pos_of_pos hr))
  have hupper := ancientKappaThree_collapsedBall_reducedVolume_upper F hF hdim p hr
    universalKappaConstant_pos htheta hcontrol (lt_of_not_ge hvolume)
  rw [universalKappaConstant_normalization] at hupper
  have hsmall : Real.exp (-1) / 4 +
      collapsedReducedVolumeTail (27 / 2) universalKappaTheta < Real.exp (-1) := by
    have htail := universalKappaTheta_spec.2.2
    have he := Real.exp_pos (-1 : ℝ)
    linarith
  have hnonneg : 0 ≤ Real.exp (-1) / 4 +
      collapsedReducedVolumeTail (27 / 2) universalKappaTheta :=
    add_nonneg (by positivity) (collapsedReducedVolumeTail_nonneg (27 / 2) htheta)
  exact not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnonneg).mpr hsmall)
    (hlower.trans hupper)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_terminal_universal_noncollapsed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_terminal_universal_noncollapsed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_terminal_universal_noncollapsed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_terminal_universal_noncollapsed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
