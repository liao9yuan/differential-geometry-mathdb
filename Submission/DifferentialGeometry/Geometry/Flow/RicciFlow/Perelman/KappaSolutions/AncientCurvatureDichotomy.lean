import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance ancientPositiveTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPositiveTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPositiveTopology target :: scope.openDecls } }
private local instance ancientPositiveCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPositiveCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPositiveCharted target :: scope.openDecls } }
private local instance ancientPositiveSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPositiveSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPositiveSmooth target :: scope.openDecls } }
private local instance ancientPositiveT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPositiveT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPositiveT2 target :: scope.openDecls } }

def AncientPositiveCurvatureOperator : Prop :=
  ∀ t : ℝ, t ≤ 0 → ∀ x : F.M, CurvatureOperatorPositiveAt (F.S.family.metric t) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.AncientPositiveCurvatureOperator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.AncientPositiveCurvatureOperator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.AncientPositiveCurvatureOperator ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.AncientPositiveCurvatureOperator

omit [I.Boundaryless] in
theorem ancientKappa_positive_or_null_plane {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3) :
    AncientPositiveCurvatureOperator F ∨
      ∃ t : ℝ, t ≤ 0 ∧ ∃ x : F.M, ∃ a b : TangentSpace I x,
        0 < (F.S.family.metric t).inner x a a * (F.S.family.metric t).inner x b b -
          ((F.S.family.metric t).inner x a b) ^ 2 ∧
        F.S.base.rm04 t x (vec4 (I := I) a b b a) = 0 := by
  classical
  by_cases hpositive : AncientPositiveCurvatureOperator F
  · exact Or.inl hpositive
  · right
    change ¬ ∀ t : ℝ, t ≤ 0 → ∀ x : F.M,
      CurvatureOperatorPositiveAt (F.S.family.metric t) x at hpositive
    push Not at hpositive
    obtain ⟨t, ht, x, hx⟩ := hpositive
    have hplanes := (not_congr
      (curvatureOperatorPositiveAt_iff_sectional (F.S.family.metric t) x hdim)).mp hx
    push Not at hplanes
    obtain ⟨a, b, hgram, hnonpos⟩ := hplanes
    refine ⟨t, ht, x, a, b, hgram, ?_⟩
    have hnonneg : 0 ≤ F.S.base.rm04 t x (vec4 (I := I) a b b a) := by
      have h := hF.nonnegativeCurvatureOperator t (by simpa using ht)
      simpa only [Fin.sum_univ_one, one_mul] using
        (h x 1 (fun _ => 1) (fun _ => a) (fun _ => b))
    exact le_antisymm hnonpos hnonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_positive_or_null_plane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_positive_or_null_plane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_positive_or_null_plane ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_positive_or_null_plane

omit [I.Boundaryless] in
theorem ancientPositiveCurvatureOperator_not_null_plane
    (hF : AncientPositiveCurvatureOperator F) (hdim : Module.finrank ℝ E = 3)
    (t : ℝ) (ht : t ≤ 0) (x : F.M) (a b : TangentSpace I x)
    (hgram : 0 <
      (F.S.family.metric t).inner x a a * (F.S.family.metric t).inner x b b -
        ((F.S.family.metric t).inner x a b) ^ 2)
    (hnull : F.S.base.rm04 t x (vec4 (I := I) a b b a) = 0) : False := by
  have hpos := (curvatureOperatorPositiveAt_iff_sectional
    (F.S.family.metric t) x hdim).mp (hF t ht x) a b hgram
  exact (ne_of_gt hpos) hnull

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPositiveCurvatureOperator_not_null_plane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPositiveCurvatureOperator_not_null_plane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPositiveCurvatureOperator_not_null_plane ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPositiveCurvatureOperator_not_null_plane

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
