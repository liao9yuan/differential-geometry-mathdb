import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosedReferenceBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedInitialRicciEquation
import Submission.DifferentialGeometry.Geometry.Curvature.RicciRestriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Equation
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.BigOperators _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

section Maps

variable {τ : ℝ} {hτ : 0 < τ} {hlt : ENNReal.ofReal τ < uniformStandardLifetime}
  {S : ℕ → StandardSolution} {x : ℕ → E3}
  {P : PointedRiemannianManifold (𝓡 3)} {φ : ℕ → ℕ}
  (Φ : PointedCGHMaps (standardClosedPointedFlowSequence τ hτ hlt S x) P φ)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNat : TopologicalSpace P.M := P.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNat : ChartedSpace E3 P.M := P.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNat : T2Space P.M := P.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopM : IsManifold (𝓡 3) ∞ P.M := P.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNat : SigmaCompactSpace P.M := P.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfWithTopENatM : IsManifold (𝓡 3) 1 P.M :=
  IsManifold.of_le (I := 𝓡 3) (M := P.M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfWithTopENatM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfWithTopENatM target :: scope.openDecls } }

variable (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceSourceDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceSourceDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceSourceDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3SourceDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : ChartedSpace E3 (SourceDomain Φ j) := sourceDomCharted Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3SourceDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3SourceDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceSourceDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : T2Space (SourceDomain Φ j) := sourceDomT2 Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceSourceDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instT2SpaceSourceDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopSourceDomain (j : ℕ) : IsManifold (𝓡 3) ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopSourceDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopSourceDomain target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSourceDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : SigmaCompactSpace (SourceDomain Φ j) :=
  sourceDomSigmaOf Φ j (standardClosedPointedMaps_sourceSigma Φ j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSourceDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSourceDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceTargetDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : TopologicalSpace (TargetDomain Φ j) := targetDomTop Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceTargetDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceTargetDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3TargetDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : ChartedSpace E3 (TargetDomain Φ j) := targetDomCharted Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3TargetDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3TargetDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceTargetDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : T2Space (TargetDomain Φ j) := targetDomT2 Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceTargetDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instT2SpaceTargetDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopTargetDomain (j : ℕ) : IsManifold (𝓡 3) ∞ (TargetDomain Φ j) := targetDomSmooth Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopTargetDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopTargetDomain target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceTargetDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : SigmaCompactSpace (TargetDomain Φ j) :=
  targetDomSigmaOf Φ j (standardClosedPointedMaps_targetSigma Φ j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceTargetDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceTargetDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }

private theorem standard_closed_source_right_equation
    (j : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 τ)
    (q : SourceDomain Φ j) (v w : TangentSpace (𝓡 3) q) :
    HasDerivWithinAt (fun s => (sourceMetric Φ hsrc htgt j s).inner q v w)
      (-2 * ricciTensor (sourceMetric Φ hsrc htgt j t) q v w) (_root_.Set.Ici 0) t := by
  have htime : t ∈ (S (φ j)).val.domain :=
    (Icc_subset_lifetimeInterval_iff (S (φ j)).val.lifetime
      (S (φ j)).val.lifetime_pos τ hτ.le).mpr
        (hlt.trans_le (uniformStandardLifetime_le_lifetime (S (φ j)))) ht
  change HasDerivWithinAt
    (fun s => (Diffeomorph.pullbackMetric
      (((S (φ j)).val.metric s).restrictOpen (targetOpen Φ j))
      (sourceTargetDiff Φ j)).inner q v w)
    (-2 * ricciTensor (Diffeomorph.pullbackMetric
      (((S (φ j)).val.metric t).restrictOpen (targetOpen Φ j))
      (sourceTargetDiff Φ j)) q v w) (_root_.Set.Ici 0) t
  simp_rw [Diffeomorph.pullbackMetric_inner, CheegerGromovCompactness.ricciTensor_pullback,
    DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen,
    SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply]
  exact (S (φ j)).val.equation t htime _ _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_closed_source_right_equation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.standard_closed_source_right_equation target :: scope.openDecls } }

theorem standard_closed_source_ricci_converges
    (hinit : ∀ j, sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ P.metric j)
    (bf : BumpFamily Φ) (co : FlowMetricConvergenceData Φ P.metric bf hsrc htgt 0 τ)
    (q : P.M) (v w : TangentSpace (𝓡 3) q) :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ∃ hq : q ∈ Φ.source (co.φ k),
        ∀ t ∈ _root_.Set.Icc 0 τ,
          |ricciTensor (sourceMetric Φ hsrc htgt (co.φ k) t) ⟨q, hq⟩ v w -
            ricciTensor (co.gInf t) q v w| < ε := by
  classical
  obtain ⟨Λ, hΛ, _C, _L, _hC, _hL, hb⟩ := standard_closed_reference_bounds τ hτ hlt
  have hbounds := hb S x P φ Φ hsrc htgt hinit
  have hcLow : 0 < Λ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hΛ)
  have hbound : ∀ j t, t ∈ _root_.Set.Icc 0 τ → ∀ (y : SourceDomain Φ j)
      (z : TangentSpace (𝓡 3) y),
      Λ⁻¹ * P.metric.inner y.val z z ≤ (sourceMetric Φ hsrc htgt j t).inner y z z := by
    intro j t ht y z
    exact (((hbounds.1 j).1 t ht).2 y (_root_.Set.mem_univ y) z).1
  have hcovTail := covTail_of_bounds Φ P.metric bf hsrc htgt 0 τ (by
    intro a
    obtain ⟨Ca, hCa, hcov⟩ := hbounds.2.cov a
    exact ⟨Ca, hCa, fun j t ht y _ => hcov j t ht y⟩)
  obtain ⟨kg, hkg⟩ := bf.grow_cover {q} isCompact_singleton
  let gTail : ℕ → ℝ → SmoothRiemannianMetric (𝓡 3) P.M := fun k t =>
    gSeqExt Φ P.metric bf hsrc htgt (co.φ (_root_.Max.max k kg)) t
  have hqgrow (k : ℕ) : q ∈ bf.grow (co.φ (_root_.Max.max k kg)) :=
    hkg (co.φ (_root_.Max.max k kg)) ((le_max_right k kg).trans (co.strictMono.id_le _)) (_root_.Set.mem_singleton q)
  have hconv (p : ℕ) (ε : ℝ) (hε : 0 < ε) : ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ∀ t ∈ _root_.Set.Icc 0 τ, ∀ a : ℕ, a ≤ p →
        metricDerivNorm a (gTail k t) (co.gInf t) P.metric q < ε := by
    obtain ⟨k₀, hk₀⟩ := co.convergencePt {q} isCompact_singleton p ε hε
    exact ⟨k₀, fun k hk t ht a ha =>
      hk₀ (_root_.Max.max k kg) (hk.trans (le_max_left k kg)) t ht a ha q (_root_.Set.mem_singleton q)⟩
  have hinner (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 τ) (z : TangentSpace (𝓡 3) q) :
      Tendsto (fun k => (gTail k t).inner q z z) _root_.Filter.atTop (𝓝 ((co.gInf t).inner q z z)) := by
    apply metricInner_tendsto (fun k => gTail k t) (co.gInf t) P.metric q
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := hconv 0 ε hε
    exact ⟨k₀, fun k hk => hk₀ k hk t ht 0 le_rfl⟩
  let lam : ℝ := _root_.Min.min Λ⁻¹ 1
  have hlam : 0 < lam := lt_min hcLow one_pos
  have hlowSeq (k : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 τ) (z : TangentSpace (𝓡 3) q) :
      lam * P.metric.inner q z z ≤ (gTail k t).inner q z z :=
    gSeqExt_lower Φ P.metric bf hsrc htgt Λ⁻¹ 0 τ hcLow hbound _ t ht q z
  have hlowInf (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 τ) (z : TangentSpace (𝓡 3) q) :
      lam * P.metric.inner q z z ≤ (co.gInf t).inner q z z :=
    ge_of_tendsto (hinner t ht z) (Eventually.of_forall (fun k => hlowSeq k t ht z))
  choose A hA using hcovTail
  let Cmax : ℝ := _root_.Max.max (A 0) (_root_.Max.max (A 1) (A 2))
  let B : ℝ := _root_.Max.max 0 (Cmax + 1)
  have hB : 0 ≤ B := le_max_left _ _
  have hAmax (a : ℕ) (ha : a ≤ 2) : A a ≤ Cmax := by
    interval_cases a
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hbSeqC (k : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 τ) (a : ℕ) :
      metricCovDerivNorm a (gTail k t) P.metric q ≤ A a :=
    hA a _ t ht q (hqgrow k)
  have hbSeq (k : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 τ) (a : ℕ) (ha : a ≤ 2) :
      metricCovDerivNorm a (gTail k t) P.metric q ≤ B := by
    have hh := (hbSeqC k t ht a).trans (hAmax a ha)
    exact hh.trans ((le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _))
  have hbInf (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 τ) (a : ℕ) (ha : a ≤ 2) :
      metricCovDerivNorm a (co.gInf t) P.metric q ≤ B := by
    obtain ⟨k₀, hk₀⟩ := hconv 2 1 one_pos
    have hd := hk₀ k₀ le_rfl t ht a ha
    have htri := covNorm_le_add a (co.gInf t) (gTail k₀ t) P.metric q
    rw [metricDerivNorm_symm] at htri
    have hs := (hbSeqC k₀ t ht a).trans (hAmax a ha)
    exact (show metricCovDerivNorm a (co.gInf t) P.metric q ≤ Cmax + 1 by linarith).trans
      (le_max_right _ _)
  have hRic := ricciConvergence_of_dnConvergence P.metric q gTail co.gInf 0 τ lam B hlam hB
    hlowSeq hlowInf hbSeq hbInf (hconv 2) v w
  intro ε hε
  obtain ⟨kc, hkc⟩ := hRic ε hε
  refine ⟨max kc kg, ?_⟩
  intro k hk
  have hkgk : kg ≤ k := (le_max_right kc kg).trans hk
  have hqg : q ∈ bf.grow (co.φ k) := by
    simpa only [max_eq_left hkgk] using hqgrow k
  refine ⟨bf.grow_subset (co.φ k) hqg, ?_⟩
  intro t ht
  have hh := hkc k ((le_max_left kc kg).trans hk) t ht
  dsimp only [gTail] at hh
  rw [max_eq_left hkgk, gSeqExt_ricci Φ P.metric bf hsrc htgt (co.φ k) t q hqg v w] at hh
  exact hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_closed_source_ricci_converges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_closed_source_ricci_converges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_closed_source_ricci_converges ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_closed_source_ricci_converges

theorem standard_closed_source_first_time_jet_converges
    (hinit : ∀ j, sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ P.metric j)
    (bf : BumpFamily Φ) (co : FlowMetricConvergenceData Φ P.metric bf hsrc htgt 0 τ)
    (hgram : ∀ (q : P.M) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × P.M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (co.gInf p.1) q p.2 i j)
        (_root_.Set.Icc 0 τ ×ˢ (_root_.FiberBundle.trivializationAt E3 (TangentSpace (𝓡 3)) q).baseSet))
    (hpde : ∀ t ∈ _root_.Set.Ioo 0 τ, ∀ (q : P.M) (v w : TangentSpace (𝓡 3) q),
      HasDerivAt (fun s => (co.gInf s).inner q v w)
        (-2 * ricciTensor (co.gInf t) q v w) t)
    (θ : ℝ) (_hθ : 0 ≤ θ) (hθτ : θ < τ)
    (q : P.M) (v w : TangentSpace (𝓡 3) q) :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ∃ hq : q ∈ Φ.source (co.φ k),
        ∀ t ∈ _root_.Set.Icc 0 θ,
          HasDerivWithinAt
            (fun s => (sourceMetric Φ hsrc htgt (co.φ k) s).inner ⟨q, hq⟩ v w)
            (-2 * ricciTensor (sourceMetric Φ hsrc htgt (co.φ k) t) ⟨q, hq⟩ v w) (_root_.Set.Ici 0) t ∧
          HasDerivWithinAt (fun s => (co.gInf s).inner q v w)
            (-2 * ricciTensor (co.gInf t) q v w) (_root_.Set.Ici 0) t ∧
          |ricciTensor (sourceMetric Φ hsrc htgt (co.φ k) t) ⟨q, hq⟩ v w -
            ricciTensor (co.gInf t) q v w| < ε ∧
          |derivWithin (fun s => (sourceMetric Φ hsrc htgt (co.φ k) s).inner ⟨q, hq⟩ v w)
              (_root_.Set.Ici 0) t -
            derivWithin (fun s => (co.gInf s).inner q v w) (_root_.Set.Ici 0) t| < ε := by
  have hlim (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 θ) :
      HasDerivWithinAt (fun s => (co.gInf s).inner q v w)
        (-2 * ricciTensor (co.gInf t) q v w) (_root_.Set.Ici 0) t := by
    rcases eq_or_lt_of_le ht.1 with heq | hpos
    · subst t
      exact metric_right_derivative_of_closed_gram hτ co.gInf hgram hpde q v w
    · exact (hpde t ⟨hpos, ht.2.trans_lt hθτ⟩ q v w).hasDerivWithinAt
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := standard_closed_source_ricci_converges Φ hsrc htgt hinit bf co q v w
    (ε / 2) (by positivity)
  refine ⟨k₀, ?_⟩
  intro k hk
  obtain ⟨hq, hRic⟩ := hk₀ k hk
  refine ⟨hq, ?_⟩
  intro t ht
  have htτ : t ∈ _root_.Set.Icc 0 τ := ⟨ht.1, ht.2.trans hθτ.le⟩
  have hdsrc := standard_closed_source_right_equation Φ hsrc htgt (co.φ k) t htτ ⟨q, hq⟩ v w
  have hdlim := hlim t ht
  have herr := hRic t htτ
  refine ⟨hdsrc, hdlim, herr.trans (by linarith), ?_⟩
  rw [hdsrc.derivWithin (uniqueDiffOn_Ici 0 t ht.1),
    hdlim.derivWithin (uniqueDiffOn_Ici 0 t ht.1), ← mul_sub, abs_mul]
  have htwo : |(-2 : ℝ)| = 2 := by norm_num
  rw [htwo]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_closed_source_first_time_jet_converges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_closed_source_first_time_jet_converges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_closed_source_first_time_jet_converges ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_closed_source_first_time_jet_converges

end Maps
end DifferentialGeometry.PDE.RicciFlow

end
