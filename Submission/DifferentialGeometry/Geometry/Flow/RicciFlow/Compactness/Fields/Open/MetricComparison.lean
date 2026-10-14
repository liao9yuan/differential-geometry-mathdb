import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessComparisonConstruction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedExtensionTimeJets
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.UniformJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.Convergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem eventually_metric_comparison_of_extension_gram_convergence
    {X : PointedFlowSeq.{u, 0, 0} (I := I3)}
    {P : PointedRiemannianManifold.{u, 0, 0} (I := I3)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I3) X P phi)
    (R : SmoothRiemannianMetric I3 P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    {D₀ : RealTimeInterval} (L : SolutionOn (I := I3) (M := P.M) D₀) (hL : IsSolutionOn L)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ X.D.carrier) (hregular : _root_.Set.Ioo a b ⊆ X.D.regular)
    (hslab₀ : _root_.Set.Icc a b ⊆ D₀.carrier) (hregular₀ : _root_.Set.Ioo a b ⊆ D₀.regular)
    {u v : ℝ} (huv : u < v) (hJb : _root_.Set.Icc u v ⊆ _root_.Set.Icc c b)
    (hgram : ∀ (p : P.M) (i j : Fin (Module.finrank ℝ ThreeSpace)), ∀ Q : Set ThreeSpace,
      IsCompact Q → Q ⊆ (extChartAt I3 p).target → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc u v, ∀ y ∈ Q,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I3) (gSeqExt Phi R bf hsrc htgt n t) p i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I3) (L.base.metric t) p i j) y‖ ≤ ε)
    (K : Set P.M) (hK : IsCompact K) (order : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in _root_.Filter.atTop, Nonempty (MetricComparisonOn L.base.metric
      (fun t => (X.term (phi i)).S.base.metric t) (Phi.map i) K (_root_.Set.Icc u v) order ε) := by
  classical
  let G : ℕ → ℝ → SmoothRiemannianMetric I3 P.M := gSeqExt Phi R bf hsrc htgt
  obtain ⟨B, hBzero, hB⟩ := exists_pointed_extension_time_jets_on_closed_window
    Phi R bf hsrc htgt hac hcb hslab hregular
  obtain ⟨C, hCzero, hC⟩ := exists_closedWindow_metric_time_fields L hL
    hac hcb hslab₀ hregular₀
  have hG : ∀ K : Set P.M, IsCompact K → ∀ᶠ i in _root_.Filter.atTop,
      ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
      ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I3 x,
        (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
          (mfderiv I3 I3 (Phi.map i) x v) (mfderiv I3 I3 (Phi.map i) x w) := by
    intro Q hQ
    obtain ⟨N, hN⟩ := bf.grow_cover Q hQ
    filter_upwards [Filter.eventually_ge_atTop N] with i hi
    obtain ⟨W, hW, hgrow, hchi⟩ := bf.chi_one i
    refine ⟨W ∩ Phi.source i, hW.inter (Phi.source_open i),
      fun x hx => ⟨hgrow (hN i hi hx), bf.grow_subset i (hN i hi hx)⟩,
      _root_.Set.inter_subset_right, ?_⟩
    intro t x hx v w
    have heq := gSeqExt_inner_of_mem Phi R bf hsrc htgt i t x hx.2 v w
    rw [hchi x hx.1, one_smul, sub_self, zero_smul, add_zero] at heq
    exact heq.trans (pointed_srcMetric_inner_eq_pullback Phi hsrc htgt i t x hx.2 v w)
  exact eventually_pointed_metric_comparison_on_strict_closedWindow Phi L hL
    hac hcb hslab hregular hslab₀ hregular₀ G hG B C hBzero hCzero hB
    (fun q t ht x => (hC q t ht x).2) huv hJb hgram K hK order ε hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metric_comparison_of_extension_gram_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metric_comparison_of_extension_gram_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metric_comparison_of_extension_gram_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metric_comparison_of_extension_gram_convergence

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem eventually_metric_comparison_of_extension_convergence
    {X : PointedFlowSeq.{u, 0, 0} (I := I3)}
    {P : PointedRiemannianManifold.{u, 0, 0} (I := I3)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I3) X P phi)
    (R : SmoothRiemannianMetric I3 P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    {D₀ : RealTimeInterval} (L : SolutionOn (I := I3) (M := P.M) D₀) (hL : IsSolutionOn L)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ X.D.carrier) (hregular : _root_.Set.Ioo a b ⊆ X.D.regular)
    (hslab₀ : _root_.Set.Icc a b ⊆ D₀.carrier) (hregular₀ : _root_.Set.Ioo a b ⊆ D₀.regular)
    {u v : ℝ} (huv : u < v) (hJb : _root_.Set.Icc u v ⊆ _root_.Set.Icc c b)
    (gRef : SmoothRiemannianMetric I3 P.M)
    (hconv : ∀ K : Set P.M, IsCompact K → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc u v,
        metricDerivNormSupOn (I := I3) K r (gSeqExt Phi R bf hsrc htgt n t)
          (L.base.metric t) gRef < ε)
    (K : Set P.M) (hK : IsCompact K) (order : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in _root_.Filter.atTop, Nonempty (MetricComparisonOn L.base.metric
      (fun t => (X.term (phi i)).S.base.metric t) (Phi.map i) K (_root_.Set.Icc u v) order ε) := by
  apply eventually_metric_comparison_of_extension_gram_convergence Phi R bf hsrc htgt L hL
    hac hcb hslab hregular hslab₀ hregular₀ huv hJb ?_ K hK order ε hε
  intro p i j Q hQ hQt r
  exact uniform_chartGram_jets_of_metricDerivNormSupOn gRef (gSeqExt Phi R bf hsrc htgt)
    L.base.metric (_root_.Set.Icc u v) hconv p hQ hQt r i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metric_comparison_of_extension_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metric_comparison_of_extension_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metric_comparison_of_extension_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metric_comparison_of_extension_convergence

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem eventually_metric_comparison_of_extension_subsequence_convergence
    {X : PointedFlowSeq.{u, 0, 0} (I := I3)}
    {P : PointedRiemannianManifold.{u, 0, 0} (I := I3)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I3) X P phi)
    (R : SmoothRiemannianMetric I3 P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (f : ℕ → ℕ) (hf : StrictMono f)
    {D₀ : RealTimeInterval} (L : SolutionOn (I := I3) (M := P.M) D₀) (hL : IsSolutionOn L)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ X.D.carrier) (hregular : _root_.Set.Ioo a b ⊆ X.D.regular)
    (hslab₀ : _root_.Set.Icc a b ⊆ D₀.carrier) (hregular₀ : _root_.Set.Ioo a b ⊆ D₀.regular)
    {u v : ℝ} (huv : u < v) (hJb : _root_.Set.Icc u v ⊆ _root_.Set.Icc c b)
    (gRef : SmoothRiemannianMetric I3 P.M)
    (hconv : ∀ K : Set P.M, IsCompact K → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc u v,
        metricDerivNormSupOn (I := I3) K r (gSeqExt Phi R bf hsrc htgt (f n) t)
          (L.base.metric t) gRef < ε)
    (K : Set P.M) (hK : IsCompact K) (order : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in _root_.Filter.atTop, Nonempty (MetricComparisonOn L.base.metric
      (fun t => (X.term (phi (f i))).S.base.metric t) (Phi.map (f i)) K (_root_.Set.Icc u v) order ε) := by
  exact eventually_metric_comparison_of_extension_convergence (Phi.compSubseq f hf) R
    (bf.compSubseq Phi f hf) (hsrc.compSubseq Phi f hf) (htgt.compSubseq Phi f hf)
    L hL hac hcb hslab hregular hslab₀ hregular₀ huv hJb gRef hconv K hK order ε hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metric_comparison_of_extension_subsequence_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metric_comparison_of_extension_subsequence_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metric_comparison_of_extension_subsequence_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metric_comparison_of_extension_subsequence_convergence

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem eventually_metric_comparison
    {X : PointedFlowSeq.{u, 0, 0} (I := I3)}
    {P : PointedRiemannianManifold.{u, 0, 0} (I := I3)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I3) X P phi)
    (R : SmoothRiemannianMetric I3 P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    {rho : ℕ → ℕ} (hrho : StrictMono rho) {β ψ : ℝ}
    {D₀ : RealTimeInterval} (L : SolutionOn (I := I3) (M := P.M) D₀) (hL : IsSolutionOn L)
    (hconv : BumpMetricConvergence Phi R bf hsrc htgt rho L.base.metric β ψ)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ X.D.carrier) (hregular : _root_.Set.Ioo a b ⊆ X.D.regular)
    (hslab₀ : _root_.Set.Icc a b ⊆ D₀.carrier) (hregular₀ : _root_.Set.Ioo a b ⊆ D₀.regular)
    (hwindow : _root_.Set.Icc c b ⊆ _root_.Set.Icc β ψ)
    {u v : ℝ} (huv : u ≤ v) (hJb : _root_.Set.Icc u v ⊆ _root_.Set.Icc c b)
    (K : Set P.M) (hK : IsCompact K) (order : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in _root_.Filter.atTop, Nonempty (MetricComparisonOn L.base.metric
      (fun t => (X.term (phi (rho i))).S.base.metric t)
      (Phi.map (rho i)) K (_root_.Set.Icc u v) order ε) := by
  have hstrict : ∀ {u v : ℝ}, u < v → _root_.Set.Icc u v ⊆ _root_.Set.Icc c b →
      ∀ᶠ i in _root_.Filter.atTop, Nonempty (MetricComparisonOn L.base.metric
        (fun t => (X.term (phi (rho i))).S.base.metric t)
        (Phi.map (rho i)) K (_root_.Set.Icc u v) order ε) := by
    intro u v huv hJb
    apply eventually_metric_comparison_of_extension_subsequence_convergence
      Phi R bf hsrc htgt rho hrho L hL
      hac hcb hslab hregular hslab₀ hregular₀ huv hJb R ?_ K hK order ε hε
    intro Q hQ r eta heta
    obtain ⟨N, hN⟩ := hconv.convergence Q hQ r eta heta
    exact ⟨N, fun n hn t ht => hN n hn t (hwindow (hJb ht))⟩
  rcases lt_or_eq_of_le huv with hlt | rfl
  · exact hstrict hlt hJb
  · filter_upwards [hstrict (u := c) (v := b) hcb Subset.rfl] with i hi
    obtain ⟨C⟩ := hi
    simpa only [_root_.Set.Icc_self] using
      (show Nonempty (MetricComparisonOn L.base.metric
        (fun t => (X.term (phi (rho i))).S.base.metric t)
        (Phi.map (rho i)) K {u} order ε) from
        ⟨C.singleton (hJb (left_mem_Icc.mpr le_rfl))⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence.eventually_metric_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence.eventually_metric_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence.eventually_metric_comparison ``Submission.DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence.eventually_metric_comparison

end DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence

end
