import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ScalarFamilyRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem chartGram_contMDiffOn_of_cartesian
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E) (K : Set ℝ)
    (hg : ContDiffOn ℝ ∞ (cartesianMetricFamily g) (K ×ˢ (_root_.Set.univ : Set E)))
    (x₀ : E) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
      (K ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet) := by
  have hpair := (hg.clm_apply (contDiffOn_const (c := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i))).clm_apply
    (contDiffOn_const (c := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j))
  have hgram : ContDiffOn ℝ ∞
      (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
      (K ×ˢ (_root_.Set.univ : Set E)) := by
    apply hpair.congr
    intro p _
    simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber, TangentBundle.symmL_model_space]
    rfl
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact (hgram.mono (_root_.Set.prod_mono Subset.rfl (_root_.Set.subset_univ _))).contMDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.chartGram_contMDiffOn_of_cartesian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.chartGram_contMDiffOn_of_cartesian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.chartGram_contMDiffOn_of_cartesian ``Submission.DifferentialGeometry.PDE.RicciFlow.chartGram_contMDiffOn_of_cartesian

theorem rm04FamilyContinuous_of_cartesian
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E) (K : Set ℝ)
    (hK : UniqueDiffOn ℝ K)
    (hg : ContDiffOn ℝ ∞ (cartesianMetricFamily g) (K ×ˢ (_root_.Set.univ : Set E))) :
    tensor0SFamilyContinuousOnSet (I := 𝓘(ℝ, E)) (M := E) 4 K
      (fun t x => metricRm04 (g t) x) := by
  have h := rm04Cont_of_joint g K hK (chartGram_contMDiffOn_of_cartesian g K hg)
  exact h.congr (fun _ _ _ => by simp only [metricRm04_apply])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm04FamilyContinuous_of_cartesian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm04FamilyContinuous_of_cartesian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm04FamilyContinuous_of_cartesian ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04FamilyContinuous_of_cartesian

theorem PartialStandardSolution.rm04FamilyContinuous (S : PartialStandardSolution) :
    tensor0SFamilyContinuousOnSet (I := 𝓡 3) (M := EuclideanSpace ℝ (Fin 3)) 4 S.domain
      (fun t x => metricRm04 (S.metric t) x) :=
  rm04FamilyContinuous_of_cartesian S.metric S.domain
    (uniqueDiffOn_lifetimeInterval S.lifetime S.lifetime_pos) S.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.rm04FamilyContinuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.rm04FamilyContinuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.rm04FamilyContinuous ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.rm04FamilyContinuous

def PartialStandardSolution.toSolutionOn (S : PartialStandardSolution) :
    SolutionOn (I := 𝓡 3) (M := EuclideanSpace ℝ (Fin 3))
      (lifetimeInterval S.lifetime S.lifetime_pos) where
  base := { metric := S.metric }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.toSolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.toSolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.toSolutionOn ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.toSolutionOn

@[simp] theorem PartialStandardSolution.toSolutionOn_metric (S : PartialStandardSolution) (t : ℝ) :
    S.toSolutionOn.base.metric t = S.metric t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.toSolutionOn_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.toSolutionOn_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.toSolutionOn_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.toSolutionOn_metric

private theorem actualRicciNorm_smooth (S : PartialStandardSolution) (t : ℝ) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (ricciNorm S.toSolutionOn t) := by
  have h := DifferentialGeometry.Tensor.RSTensor.normSq02_smooth (S.metric t)
    (metricRicci (S.metric t))
  exact h.congr (fun _ => rfl)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.actualRicciNorm_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.actualRicciNorm_smooth target :: scope.openDecls } }

theorem PartialStandardSolution.isSolutionOn (S : PartialStandardSolution) :
    IsSolutionOn S.toSolutionOn := by
  refine
    { smoothMetric := S.metricFamilySmoothOn
      smoothConnection := ?_
      equation := ?_
      scalarCont := S.scalar_contDiffOn.continuousOn
      scalarTime := ?_
      ricciCont := ?_
      rm04Cont := S.rm04FamilyContinuous
      ricciNormSpace := ?_
      ricciNormGrad := ?_ }
  · intro t
    exact leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (S.metric t.val)
  · intro t x v w
    have ht : t.val ∈ S.domain :=
      (lifetimeInterval S.lifetime S.lifetime_pos).regular_subset t.property
    have heq := (S.equation t.val ht x v w).mono
      (fun s hs => ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mp hs).1)
    simpa only [MetricVariationEquationOn, MetricConnectionFamilyVariationEquationOn,
      PartialStandardSolution.toSolutionOn, SolutionOn.family, RicciAtFamily.toTensorField,
      SolutionOn.ricciAt, SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor] using heq
  · intro K t ht hK x
    exact S.scalarTime ht hK x
  · exact S.ricciFamilyContinuous.congr (fun _ _ _ => rfl)
  · intro t _ x
    exact (actualRicciNorm_smooth S t).mdifferentiableAt (by simp)
  · intro t _ x
    exact gradientFun_mdiffAt (S.metric t) (actualRicciNorm_smooth S t) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isSolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isSolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isSolutionOn ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.isSolutionOn
end DifferentialGeometry.PDE.RicciFlow
