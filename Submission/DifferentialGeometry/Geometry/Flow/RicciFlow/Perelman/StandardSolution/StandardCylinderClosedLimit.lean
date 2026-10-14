import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderPointedMaps
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompleteReferenceLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference : TopologicalSpace cylinderPointedReference.M := cylinderPointedReference.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNatCylinderPointedReference : ChartedSpace E3 cylinderPointedReference.M := cylinderPointedReference.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNatCylinderPointedReference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNatCylinderPointedReference target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference : T2Space cylinderPointedReference.M := cylinderPointedReference.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopMCylinderPointedReference : IsManifold (𝓡 3) ∞ cylinderPointedReference.M := cylinderPointedReference.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopMCylinderPointedReference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopMCylinderPointedReference target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference : SigmaCompactSpace cylinderPointedReference.M := cylinderPointedReference.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference target :: scope.openDecls } }
private abbrev Q := cylinderReferenceCopy.Q

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Q
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Q target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

private theorem interior_solution_of_closed_gram
    (τ : ℝ) (g : ℝ → SmoothRiemannianMetric (𝓡 3) Q)
    (hgram : ∀ (q : Q) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × Q => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) q p.2 i j)
        (_root_.Set.Icc 0 τ ×ˢ (_root_.FiberBundle.trivializationAt E3 (TangentSpace (𝓡 3)) q).baseSet))
    (hpde : ∀ t ∈ _root_.Set.Ioo 0 τ, ∀ (q : Q) (v w : TangentSpace (𝓡 3) q),
      HasDerivAt (fun s => (g s).inner q v w)
        (-2 * ricciTensor (g t) q v w) t)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ τ) :
    IsSolutionOn
      ({ base := { metric := g } } :
        SolutionOn (I := 𝓡 3) (M := Q) (RealTimeInterval.closedOpen a b hab)) := by
  apply solutionOn_of_joint hab g
  · intro q i j
    exact (hgram q i j).mono (Set.prod_mono_left (by
      intro t ht
      exact ⟨ha.le.trans ht.1, ht.2.le.trans hb⟩))
  · intro t ht q v w
    exact (hpde t ⟨ha.trans_le ht.1, ht.2.trans_le hb⟩ q v w).hasDerivWithinAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.interior_solution_of_closed_gram
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.interior_solution_of_closed_gram target :: scope.openDecls } }

theorem exists_standard_cylinder_closed_limit (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime) :
    ∀ (S : ℕ → StandardSolution) (x : ℕ → E3),
      _root_.Filter.Tendsto (fun i => (riemannianEDistOf ((S i).val.metric 0) 0 (x i)).toReal)
        _root_.Filter.atTop _root_.Filter.atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ Φ : PointedCGHMaps (standardClosedPointedFlowSequence τ hτ hlt S x)
            cylinderPointedReference φ,
          (∀ j : ℕ, ∃ hfit : transitionEnd + ((j : ℝ) + 1) ≤ ‖x (φ j)‖,
            Φ.partialDiffeomorph j = cylinderReferenceInitialMap
              (pointedInitialRotation (x (φ j))) ‖x (φ j)‖ ((j : ℝ) + 1) hfit) ∧
          let hsrc := standardClosedPointedMaps_sourceSigma Φ
          let htgt := standardClosedPointedMaps_targetSigma Φ
          ∃ bf : BumpFamily Φ,
          ∃ co : FlowMetricConvergenceData Φ cylinderReferenceMetric bf hsrc htgt 0 τ,
            (∀ j, sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ cylinderReferenceMetric j) ∧
            StrictMono (φ ∘ co.φ) ∧
            (∀ k : ℕ,
              ∃ hfit : transitionEnd + ((co.φ k : ℝ) + 1) ≤ ‖x ((φ ∘ co.φ) k)‖,
                (Φ.compSubseq co.φ co.strictMono).partialDiffeomorph k =
                  cylinderReferenceInitialMap
                    (pointedInitialRotation (x ((φ ∘ co.φ) k)))
                    ‖x ((φ ∘ co.φ) k)‖ ((co.φ k : ℝ) + 1) hfit) ∧
            co.gInf 0 = cylinderReferenceMetric ∧
            Diffeomorph.pullbackMetricCross (co.gInf 0) cylinderReferenceCopy.equiv =
              roundCylinderMetric (E := E3) (n := 2) ∧
            (∀ t ∈ _root_.Set.Icc 0 τ, RiemannianMetricComplete (co.gInf t)) ∧
            (∀ (r : ℕ) (q : Q) (i j : Fin (Module.finrank ℝ E3)),
              ContinuousOn
                (fun p : ℝ × E3 => iteratedFDeriv ℝ r
                  (chartGramOnE (co.gInf p.1) q i j) p.2)
                (_root_.Set.Icc 0 τ ×ˢ interior (extChartAt (𝓡 3) q).target)) ∧
            (∀ (q : Q) (i j : Fin (Module.finrank ℝ E3)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
                (fun p : ℝ × Q => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (co.gInf p.1) q p.2 i j)
                (_root_.Set.Icc 0 τ ×ˢ (_root_.FiberBundle.trivializationAt E3 (TangentSpace (𝓡 3)) q).baseSet)) ∧
            (∀ t ∈ _root_.Set.Ioo 0 τ, ∀ (q : Q) (v w : TangentSpace (𝓡 3) q),
              HasDerivAt (fun s => (co.gInf s).inner q v w)
                (-2 * ricciTensor (co.gInf t) q v w) t) ∧
            (∀ (a b : ℝ) (_ha : 0 < a) (hab : a < b), b ≤ τ →
              IsSolutionOn
                ({ base := { metric := co.gInf } } :
                  SolutionOn (I := 𝓡 3) (M := Q) (RealTimeInterval.closedOpen a b hab))) ∧
            (∀ K : Set Q, IsCompact K → ∀ p : ℕ, ∀ ε : ℝ, 0 < ε →
              ∃ k₀ : ℕ, ∀ k ≥ k₀,
                K ⊆ Φ.source (co.φ k) ∧
                ∀ t ∈ _root_.Set.Icc 0 τ,
                  (SourceDomainMetricData.ofRestrictPullback
                    (Φ := Φ) (k := co.φ k) (hsrc (co.φ k))
                    (fun _ => sourceMetricRestriction Φ cylinderReferenceMetric (co.φ k)) co.gInf).derivNormSupOn (I := 𝓡 3) K p t < ε) ∧
            (∀ K : Set Q, IsCompact K → ∀ p : ℕ, ∃ Lp : ℝ, 0 ≤ Lp ∧
              ∀ s ∈ _root_.Set.Icc 0 τ, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ a : ℕ, a ≤ p → ∀ q ∈ K,
                metricDerivNorm a (co.gInf s) (co.gInf t) cylinderReferenceMetric q ≤
                  Lp * |s - t|) := by
  obtain ⟨Λ, hΛ, _C, _L, _hC, _hL, hb⟩ := standard_closed_reference_bounds τ hτ hlt
  intro S x hescape
  obtain ⟨φ, hφ, Φ, hcharts, hinit⟩ := exists_standard_cylinder_pointed_maps τ hτ hlt S x hescape
  let hsrc := standardClosedPointedMaps_sourceSigma Φ
  let htgt := standardClosedPointedMaps_targetSigma Φ
  have hbounds := hb S x cylinderPointedReference φ Φ hsrc htgt hinit
  have hequiv :
      ∀ j,
        letI : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j
        letI : ChartedSpace E3 (SourceDomain Φ j) := sourceDomCharted Φ j
        letI : T2Space (SourceDomain Φ j) := sourceDomT2 Φ j
        letI : IsManifold (𝓡 3) ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j
        letI : SigmaCompactSpace (SourceDomain Φ j) := sourceDomSigmaOf Φ j (hsrc j)
        ∀ t ∈ _root_.Set.Icc 0 τ,
          MetricUniformEquivalentOn _root_.Set.univ (sourceMetricRestriction Φ cylinderReferenceMetric j)
            (sourceMetric Φ hsrc htgt j t) Λ := by
    intro j
    exact (hbounds.1 j).1
  obtain ⟨bf, co, _hlower, _hcov, hzero, hcomplete, hjets, hgram, hpde, hlip⟩ :=
    exists_complete_closed_reference_limit Φ τ hτ (fun _ ht => ht) (fun _ ht => ht)
      cylinderPointedReference_complete hsrc htgt Λ hΛ hinit hequiv hbounds.2
  refine ⟨φ, hφ, Φ, hcharts, bf, co, hinit, hφ.comp co.strictMono, ?_, hzero, ?_,
    hcomplete, hjets, hgram, hpde, ?_, ?_, hlip⟩
  · intro k
    obtain ⟨hfit, hchart⟩ := hcharts (co.φ k)
    exact ⟨hfit, hchart⟩
  · rw [hzero]
    exact pullback_cylinderReferenceMetric
  · intro a b ha hab hbτ
    exact interior_solution_of_closed_gram τ co.gInf hgram hpde a b ha hab hbτ
  · intro K hK p ε hε
    obtain ⟨kc, hkc⟩ := ofRP_supOn_convergence Φ cylinderReferenceMetric bf hsrc htgt
      0 τ co co.gInf (fun _ _ => rfl) K hK p ε hε
    obtain ⟨kg, hkg⟩ := bf.grow_cover K hK
    refine ⟨max kc kg, ?_⟩
    intro k hk
    have hkg' : K ⊆ bf.grow (co.φ k) :=
      hkg (co.φ k) (((le_max_right kc kg).trans hk).trans (co.strictMono.id_le k))
    exact ⟨hkg'.trans (bf.grow_subset (co.φ k)),
      fun t ht => hkc k ((le_max_left kc kg).trans hk) t ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_standard_cylinder_closed_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_standard_cylinder_closed_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_standard_cylinder_closed_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_standard_cylinder_closed_limit

end DifferentialGeometry.PDE.RicciFlow
