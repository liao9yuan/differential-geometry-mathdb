import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.Convergence
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Continuity
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  {Φ : PointedCGHMaps (I := I) X P subseq}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private theorem eventually_bump_metric_deriv_eq
    (R : SmoothRiemannianMetric I P.M)
    (bf₁ bf₂ : BumpFamily Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    {K : Set P.M} (hK : IsCompact K) :
    ∀ᶠ i in _root_.Filter.atTop, ∀ t : ℝ, ∀ q : ℕ,
      ∀ g : SmoothRiemannianMetric I P.M, ∀ x ∈ K,
        metricDerivNorm q (gSeqExt Φ R bf₁ hsrc htgt i t) g R x =
          metricDerivNorm q (gSeqExt Φ R bf₂ hsrc htgt i t) g R x := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨N₁, hN₁⟩ := bf₁.grow_cover K hK
  obtain ⟨N₂, hN₂⟩ := bf₂.grow_cover K hK
  filter_upwards [_root_.Filter.eventually_ge_atTop (_root_.Max.max N₁ N₂)] with i hi
  obtain ⟨U₁, hU₁, hKU₁, hχ₁⟩ := bf₁.chi_one i
  obtain ⟨U₂, hU₂, hKU₂, hχ₂⟩ := bf₂.chi_one i
  let U : TopologicalSpace.Opens P.M :=
    ⟨U₁ ∩ U₂ ∩ Φ.source i, (hU₁.inter hU₂).inter (Φ.source_open i)⟩
  let _ : SigmaCompactSpace U :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  intro t q g x hx
  have hxU : x ∈ U :=
    ⟨⟨hKU₁ (hN₁ i ((le_max_left N₁ N₂).trans hi) hx),
      hKU₂ (hN₂ i ((le_max_right N₁ N₂).trans hi) hx)⟩,
      bf₁.grow_subset i (hN₁ i ((le_max_left N₁ N₂).trans hi) hx)⟩
  have heq : ∀ y : P.M, y ∈ U → ∀ v w : TangentSpace I y,
      (gSeqExt Φ R bf₁ hsrc htgt i t).inner y v w =
        (gSeqExt Φ R bf₂ hsrc htgt i t).inner y v w := by
    intro y hy v w
    rw [gSeqExt_inner_of_mem Φ R bf₁ hsrc htgt i t y hy.2 v w,
      gSeqExt_inner_of_mem Φ R bf₂ hsrc htgt i t y hy.2 v w,
      hχ₁ y hy.1.1, hχ₂ y hy.1.2]
  have hcov : metricCovDeriv (gSeqExt Φ R bf₁ hsrc htgt i t) R q x =
      metricCovDeriv (gSeqExt Φ R bf₂ hsrc htgt i t) R q x := by
    ext slots
    exact metricCovDeriv_eq_of_eqOn _ _ R U heq q ⟨x, hxU⟩ slots
  simp only [metricDerivNorm, metricDiffCovDerivAt, hcov]

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.eventually_bump_metric_deriv_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.eventually_bump_metric_deriv_eq target :: scope.openDecls } }

theorem BumpMetricConvergence.change_bump_family
    {R : SmoothRiemannianMetric I P.M}
    {bf₁ : BumpFamily Φ} (bf₂ : BumpFamily Φ)
    {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {ρ : ℕ → ℕ} (hρ : StrictMono ρ)
    {g : ℝ → SmoothRiemannianMetric I P.M} {a b : ℝ}
    (h : BumpMetricConvergence Φ R bf₁ hsrc htgt ρ g a b) :
    BumpMetricConvergence Φ R bf₂ hsrc htgt ρ g a b := by
  have hpt : ∀ K : Set P.M, IsCompact K → ∀ p : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ _root_.Set.Icc a b, ∀ q ≤ p, ∀ x ∈ K,
        metricDerivNorm q (gSeqExt Φ R bf₂ hsrc htgt (ρ i) t) (g t) R x < ε := by
    intro K hK p ε hε
    obtain ⟨N, hN⟩ := h.convergencePt K hK p ε hε
    obtain ⟨J, hJ⟩ := eventually_atTop.mp
      (eventually_bump_metric_deriv_eq R bf₁ bf₂ hsrc htgt hK)
    refine ⟨max N J, fun i hi t ht q hq x hx => ?_⟩
    rw [← hJ (ρ i) (((le_max_right N J).trans hi).trans (hρ.id_le i)) t q (g t) x hx]
    exact hN i ((le_max_left N J).trans hi) t ht q hq x hx
  refine ⟨?_, hpt⟩
  intro K hK p ε hε
  obtain ⟨N, hN⟩ := hpt K hK p (ε / 2) (by positivity)
  refine ⟨N, fun i hi t ht => ?_⟩
  have hle : metricDerivNormSupOn K p (gSeqExt Φ R bf₂ hsrc htgt (ρ i) t) (g t) R ≤ ε / 2 :=
    metricDerivNormSupOn_le_of_forall K p _ _ R (ε / 2) (by positivity)
      (fun q hq x hx => (hN i hi t ht q hq x hx).le)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence.change_bump_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence.change_bump_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence.change_bump_family ``Submission.DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence.change_bump_family

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X Y : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {f g : ℕ → ℕ}
  {Φ : PointedCGHMaps (I := I) X P f}
  {Ψ : PointedCGHMaps (I := I) Y P g}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem BumpMetricConvergence.congr_source_metric
    {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Φ} {cg : BumpFamily Ψ}
    {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {ksrc : SourceIsSigmaCompact Ψ} {ktgt : TargetIsSigmaCompact Ψ}
    {ρ τ : ℕ → ℕ} (hρ : StrictMono ρ) (hτ : StrictMono τ)
    {gInf : ℝ → SmoothRiemannianMetric I P.M} {a b : ℝ}
    (h : BumpMetricConvergence Φ R bf hsrc htgt ρ gInf a b)
    (hinner : ∀ i t, t ∈ _root_.Set.Icc a b → ∀ x : P.M,
      ∀ hx : x ∈ Φ.source (ρ i), ∀ hy : x ∈ Ψ.source (τ i),
      ∀ v w : TangentSpace I x,
        (sourceMetric Φ hsrc htgt (ρ i) t).inner ⟨x, hx⟩ v w =
          (sourceMetric Ψ ksrc ktgt (τ i) t).inner ⟨x, hy⟩ v w) :
    BumpMetricConvergence Ψ R cg ksrc ktgt τ gInf a b := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hnorm : ∀ K : Set P.M, IsCompact K →
      ∀ᶠ i in _root_.Filter.atTop, ∀ t ∈ _root_.Set.Icc a b, ∀ q : ℕ, ∀ x ∈ K,
        metricDerivNorm q (gSeqExt Φ R bf hsrc htgt (ρ i) t) (gInf t) R x =
          metricDerivNorm q (gSeqExt Ψ R cg ksrc ktgt (τ i) t) (gInf t) R x := by
    intro K hK
    obtain ⟨N, hN⟩ := bf.grow_cover K hK
    obtain ⟨J, hJ⟩ := cg.grow_cover K hK
    filter_upwards [_root_.Filter.eventually_ge_atTop (_root_.Max.max N J)] with i hi
    obtain ⟨U, hU, hKU, hχ⟩ := bf.chi_one (ρ i)
    obtain ⟨V, hV, hKV, hη⟩ := cg.chi_one (τ i)
    let W : TopologicalSpace.Opens P.M :=
      ⟨(U ∩ Φ.source (ρ i)) ∩ (V ∩ Ψ.source (τ i)),
        (hU.inter (Φ.source_open (ρ i))).inter (hV.inter (Ψ.source_open (τ i)))⟩
    let _ : SigmaCompactSpace W :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I W.isOpen)
    intro t ht q x hx
    have hxρ := hN (ρ i) (((le_max_left N J).trans hi).trans (hρ.id_le i)) hx
    have hxτ := hJ (τ i) (((le_max_right N J).trans hi).trans (hτ.id_le i)) hx
    have hxW : x ∈ W :=
      ⟨⟨hKU hxρ, bf.grow_subset (ρ i) hxρ⟩,
        ⟨hKV hxτ, cg.grow_subset (τ i) hxτ⟩⟩
    have heq : ∀ y : P.M, y ∈ W → ∀ v w : TangentSpace I y,
        (gSeqExt Φ R bf hsrc htgt (ρ i) t).inner y v w =
          (gSeqExt Ψ R cg ksrc ktgt (τ i) t).inner y v w := by
      intro y hy v w
      rw [gSeqExt_inner_of_mem Φ R bf hsrc htgt (ρ i) t y hy.1.2 v w,
        gSeqExt_inner_of_mem Ψ R cg ksrc ktgt (τ i) t y hy.2.2 v w,
        hχ y hy.1.1, hη y hy.2.1]
      simpa using hinner i t ht y hy.1.2 hy.2.2 v w
    have hcov : metricCovDeriv (gSeqExt Φ R bf hsrc htgt (ρ i) t) R q x =
        metricCovDeriv (gSeqExt Ψ R cg ksrc ktgt (τ i) t) R q x := by
      ext slots
      exact metricCovDeriv_eq_of_eqOn _ _ R W heq q ⟨x, hxW⟩ slots
    simp only [metricDerivNorm, metricDiffCovDerivAt, hcov]
  have hpt : ∀ K : Set P.M, IsCompact K → ∀ p : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ _root_.Set.Icc a b, ∀ q ≤ p, ∀ x ∈ K,
        metricDerivNorm q (gSeqExt Ψ R cg ksrc ktgt (τ i) t) (gInf t) R x < ε := by
    intro K hK p ε hε
    obtain ⟨N, hN⟩ := h.convergencePt K hK p ε hε
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hnorm K hK)
    refine ⟨max N J, fun i hi t ht q hq x hx => ?_⟩
    rw [← hJ i ((le_max_right N J).trans hi) t ht q x hx]
    exact hN i ((le_max_left N J).trans hi) t ht q hq x hx
  refine ⟨?_, hpt⟩
  intro K hK p ε hε
  obtain ⟨N, hN⟩ := hpt K hK p (ε / 2) (by positivity)
  refine ⟨N, fun i hi t ht => ?_⟩
  have hle : metricDerivNormSupOn K p (gSeqExt Ψ R cg ksrc ktgt (τ i) t)
      (gInf t) R ≤ ε / 2 :=
    metricDerivNormSupOn_le_of_forall K p _ _ R (ε / 2) (by positivity)
      (fun q hq x hx => (hN i hi t ht q hq x hx).le)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence.congr_source_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence.congr_source_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence.congr_source_metric ``Submission.DifferentialGeometry.CheegerGromovCompactness.BumpMetricConvergence.congr_source_metric

end DifferentialGeometry.CheegerGromovCompactness

end

end
