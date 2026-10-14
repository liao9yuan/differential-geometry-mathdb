import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMinimizerInterior
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.SmoothExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPullback
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Naturality
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Naturality
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Submission.DifferentialGeometry.Topology.Manifold.ModelWithCorners

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientTerminalMinimizerTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerTopology
local instance ancientTerminalMinimizerCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerCharted
local instance ancientTerminalMinimizerSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerSmooth
local instance ancientTerminalMinimizerT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerT2
local instance ancientTerminalMinimizerSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalMinimizerSigma

private theorem exists_lRegularized_minimizer_of_ancient_of_innerProductSpace
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
      alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
      IsLRegularizedGeodesicOn F.S 0 alpha (_root_.Set.Ioc 0 (Real.sqrt tau)) ∧
      lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
        lCost F.S 0 x (alpha (Real.sqrt tau)) tau := by
  obtain ⟨alpha, halpha, hgeo, ha0, hab, hact, _⟩ :=
    exists_lRegularizedMin_contMDiff_one_regularizedGeodesicOn_of_ancient F hF x y htau
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hregb : 0 - (Real.sqrt tau) ^ 2 ∈ ancientTimeInterval.regular := by
    rw [ancientTimeInterval_regular, _root_.Set.mem_Iio, zero_sub]
    exact neg_neg_of_pos (sq_pos_of_pos hb)
  obtain ⟨beta, hbeta, heq, hgeob⟩ :=
    exists_lRegularizedGeodesic_extension_Ioc_of_contMDiff_one
      F.S F.isSolution 0 hb halpha hregb hgeo
  have hb0 : beta 0 = x := (heq ⟨le_rfl, hb.le⟩).trans ha0
  have hbb : beta (Real.sqrt tau) = y := (heq ⟨hb.le, le_rfl⟩).trans hab
  refine ⟨beta, hbeta, hb0, hbb, hgeob, ?_⟩
  rw [hbb, ← hact]
  apply lRegularizedAction_congr F.S 0
  intro s hs
  rw [_root_.Set.uIoo_of_le hb.le] at hs
  exact heq ⟨hs.1.le, hs.2.le⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularized_minimizer_of_ancient_of_innerProductSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularized_minimizer_of_ancient_of_innerProductSpace target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientTerminalTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalTopology
local instance ancientTerminalCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalCharted
local instance ancientTerminalSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalSmooth
local instance ancientTerminalT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalT2
local instance ancientTerminalSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTerminalSigma

theorem exists_lRegularized_minimizer_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
      alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
      IsLRegularizedGeodesicOn F.S 0 alpha (_root_.Set.Ioc 0 (Real.sqrt tau)) ∧
      lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
        lCost F.S 0 x (alpha (Real.sqrt tau)) tau := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let J := I.transContinuousLinearEquiv e
  let Phi : F.M ≃ₘ⟮I, J⟯ F.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I F.M e
  let G := F.pullback Phi.symm
  have hG : IsAncientKappaSolution kappa G := F.pullback_isAncientKappaSolution Phi.symm hF
  obtain ⟨alpha, halpha, hstart, hend, hgeo, haction⟩ :=
    exists_lRegularized_minimizer_of_ancient_of_innerProductSpace G hG x y htau
  refine ⟨alpha, ?_, hstart, hend, ?_, ?_⟩
  · exact (Phi.symm.contMDiff.of_le (by simp)).comp halpha
  · exact hgeo.comp_diffeomorph F.S Phi.symm
  · change lRegularizedAction (F.S.pullback Phi.symm) 0 alpha 0 (Real.sqrt tau) =
      lCost (F.S.pullback Phi.symm) 0 x (alpha (Real.sqrt tau)) tau at haction
    exact (lRegularizedAction_pullback F.S Phi.symm 0 alpha 0 (Real.sqrt tau)).symm.trans
      (haction.trans (lCost_pullback F.S Phi.symm 0 x (alpha (Real.sqrt tau)) tau))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularized_minimizer_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularized_minimizer_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularized_minimizer_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularized_minimizer_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
