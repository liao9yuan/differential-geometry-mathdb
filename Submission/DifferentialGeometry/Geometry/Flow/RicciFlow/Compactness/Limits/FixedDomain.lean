import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.ClosedInterval
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem fixed_domain_metric_limit
    (P : PointedRiemannianManifold (I := I))
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := P.M) D)
    (hS : ∀ i, IsSolutionOn (S i))
    {a b : ℝ} (hab : a < b) (hslab : _root_.Set.Icc a b ⊆ D.carrier)
    (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (rho : ℕ → ℕ) (hrho : StrictMono rho)
    (g : ℝ → SmoothRiemannianMetric I P.M)
    (hconv : ∀ K : Set P.M, IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ _root_.Set.Icc a b,
        metricDerivNormSupOn K p ((S (rho i)).base.metric t) (g t) P.metric < epsilon)
    (htime : ∀ K : Set P.M, IsCompact K → ∀ p : ℕ, ∀ᶠ i in _root_.Filter.atTop,
      ∃ L : ℝ, ∀ s ∈ _root_.Set.Icc a b, ∀ t ∈ _root_.Set.Icc a b, ∀ q ≤ p, ∀ x ∈ K,
        metricDerivNorm q ((S i).base.metric s) ((S i).base.metric t) P.metric x ≤
          L * |s - t|) :
    IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := P.M)
      (RealTimeInterval.closed a b hab.le)) ∧
      ∀ (x : P.M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × P.M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (g p.1) x p.2 i j)
          (_root_.Set.Icc a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let X : PointedFlowSeq (I := I) := {
    D := RealTimeInterval.closed a b hab.le
    term := fun i => {
      M := P.M
      topology := P.topology
      charted := P.charted
      smooth := P.smooth
      sigmaCompact := P.sigmaCompact
      t2 := P.t2
      t2TangentBundle := P.t2TangentBundle
      basepoint := P.basepoint
      S := (S i).timeRestrict _
      isSolution := isSolutionOn_timeRestrict (hS i) hslab hreg } }
  let Phi : PointedCGHMaps (I := I) X P id := {
    partialDiffeomorph := fun _ => PartialDiffeomorph.refl (I := I) P.M
    source_exhausts := ⟨fun _ => isOpen_univ, fun _ => _root_.Set.subset_univ _,
      fun _ _ => ⟨0, fun _ _ => _root_.Set.subset_univ _⟩⟩
    base_mem := fun _ => _root_.Set.mem_univ _
    basepoint_map := fun _ => rfl }
  obtain ⟨bf₀⟩ := nonempty_bumpFamily Phi
  let bf : BumpFamily Phi := {
    bf₀ with
    chi := fun _ _ => 1
    chi_smooth := fun _ => contMDiff_const
    chi01 := fun _ _ => ⟨zero_le_one, le_rfl⟩
    chi_support := fun _ => _root_.Set.subset_univ _
    chi_one := fun _ => ⟨univ, isOpen_univ, _root_.Set.subset_univ _, fun _ _ => rfl⟩ }
  have hsrc : SourceIsSigmaCompact Phi := fun _ => isSigmaCompact_univ
  have htgt : TargetIsSigmaCompact Phi := fun _ => isSigmaCompact_univ
  have hG (i : ℕ) (t : ℝ) : gSeqExt Phi P.metric bf hsrc htgt i t =
      (S i).base.metric t := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have h := gSeqExt_inner_of_mem Phi P.metric bf hsrc htgt i t x (_root_.Set.mem_univ _) v w
    change _ = (1 : ℝ) • (sourceMetric Phi hsrc htgt i t).inner ⟨x, _root_.Set.mem_univ _⟩ v w +
      (1 - 1 : ℝ) • P.metric.inner x v w at h
    rw [one_smul, sub_self, zero_smul, add_zero] at h
    refine h.trans ((PDE.RicciFlow.Perelman.KappaSolutions.pointed_srcMetric_inner_eq_pullback
      Phi hsrc htgt i t x (_root_.Set.mem_univ _) v w).trans ?_)
    change ((S i).base.metric t).inner x (mfderiv I I id x v) (mfderiv I I id x w) = _
    rw [mfderiv_id]
    rfl
  let co : FlowMetricConvergenceData Phi P.metric bf hsrc htgt a b := {
    φ := rho
    strictMono := hrho
    gInf := g
    convergence := by
      intro K hK p epsilon hepsilon
      obtain ⟨N, hN⟩ := hconv K hK p epsilon hepsilon
      exact ⟨N, fun i hi t ht => by rw [hG]; exact hN i hi t ht⟩
    convergencePt := by
      intro K hK p epsilon hepsilon
      obtain ⟨N, hN⟩ := hconv K hK p epsilon hepsilon
      refine ⟨N, fun i hi t ht q hq x hx => ?_⟩
      rw [hG]
      exact (derivNorm_le_sup hK hq _ _ _ hx).trans_lt (hN i hi t ht) }
  have htime' : ∀ K : Set P.M, IsCompact K → ∀ p : ℕ, ∀ᶠ i in _root_.Filter.atTop,
      ∃ L : ℝ, ∀ s ∈ _root_.Set.Icc a b, ∀ t ∈ _root_.Set.Icc a b, ∀ q ≤ p, ∀ x ∈ K,
        metricDerivNorm q (gSeqExt Phi P.metric bf hsrc htgt i s)
          (gSeqExt Phi P.metric bf hsrc htgt i t) P.metric x ≤ L * |s - t| := by
    intro K hK p
    filter_upwards [htime K hK p] with i hi
    obtain ⟨L, hL⟩ := hi
    exact ⟨L, fun s hs t ht q hq x hx => by
      rw [hG, hG]
      exact hL s hs t ht q hq x hx⟩
  refine ⟨co.isSolutionOn_closed hab rfl Subset.rfl htime', ?_⟩
  apply co.gramSmoothIcc (Φ := Phi) hab Subset.rfl Subset.rfl
  apply co.gramJets_of_stage (Φ := Phi)
  intro r p i j C hC hCt
  have hK : IsCompact ((extChartAt I p).symm '' C) :=
    hC.image_of_continuousOn ((continuousOn_extChartAt_symm (I := I) p).mono hCt)
  filter_upwards [hrho.tendsto_atTop.eventually (htime' _ hK r)] with k hk
  obtain ⟨L, hL⟩ := hk
  exact chartGram_jets_continuousOn_of_metric_time_lipschitz
    (gSeqExt Phi P.metric bf hsrc htgt (rho k)) P.metric (_root_.Set.Icc a b) p r hC hCt hL i j

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.fixed_domain_metric_limit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.fixed_domain_metric_limit target :: scope.openDecls } }

theorem isSolutionOn_of_fixed_domain_metric_convergence
    (P : PointedRiemannianManifold (I := I))
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := P.M) D)
    (hS : ∀ i, IsSolutionOn (S i))
    {a b : ℝ} (hab : a < b) (hslab : _root_.Set.Icc a b ⊆ D.carrier)
    (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (rho : ℕ → ℕ) (hrho : StrictMono rho)
    (g : ℝ → SmoothRiemannianMetric I P.M)
    (hconv : ∀ K : Set P.M, IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ _root_.Set.Icc a b,
        metricDerivNormSupOn K p ((S (rho i)).base.metric t) (g t) P.metric < epsilon)
    (htime : ∀ K : Set P.M, IsCompact K → ∀ p : ℕ, ∀ᶠ i in _root_.Filter.atTop,
      ∃ L : ℝ, ∀ s ∈ _root_.Set.Icc a b, ∀ t ∈ _root_.Set.Icc a b, ∀ q ≤ p, ∀ x ∈ K,
        metricDerivNorm q ((S i).base.metric s) ((S i).base.metric t) P.metric x ≤
          L * |s - t|) :
    IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := P.M)
      (RealTimeInterval.closed a b hab.le)) :=
  (fixed_domain_metric_limit P S hS hab hslab hreg rho hrho g hconv htime).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.isSolutionOn_of_fixed_domain_metric_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.isSolutionOn_of_fixed_domain_metric_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.isSolutionOn_of_fixed_domain_metric_convergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.isSolutionOn_of_fixed_domain_metric_convergence

theorem contMDiffOn_chartGramMatrix_of_fixed_domain_metric_convergence
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := M) D)
    (hS : ∀ i, IsSolutionOn (S i)) (R : SmoothRiemannianMetric I M)
    {a b : ℝ} (hab : a < b) (hslab : _root_.Set.Icc a b ⊆ D.carrier)
    (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (rho : ℕ → ℕ) (hrho : StrictMono rho)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hconv : ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ _root_.Set.Icc a b,
        metricDerivNormSupOn K p ((S (rho i)).base.metric t) (g t) R < epsilon)
    (htime : ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ᶠ i in _root_.Filter.atTop,
      ∃ L : ℝ, ∀ s ∈ _root_.Set.Icc a b, ∀ t ∈ _root_.Set.Icc a b, ∀ q ≤ p, ∀ x ∈ K,
        metricDerivNorm q ((S i).base.metric s) ((S i).base.metric t) R x ≤ L * |s - t|) :
    ∀ (x : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (g p.1) x p.2 i j)
        (_root_.Set.Icc a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  by_cases hM : Nonempty M
  · let _ : Nonempty M := hM
    let P : PointedRiemannianManifold (I := I) := {
      M := M
      topology := inferInstance
      charted := inferInstance
      smooth := inferInstance
      sigmaCompact := inferInstance
      t2 := inferInstance
      t2TangentBundle := inferInstance
      basepoint := Classical.choice hM
      metric := R }
    exact (fixed_domain_metric_limit P S hS hab hslab hreg rho hrho g hconv htime).2
  · let _ : IsEmpty M := not_nonempty_iff.mp hM
    intro x
    exact isEmptyElim x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.contMDiffOn_chartGramMatrix_of_fixed_domain_metric_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.contMDiffOn_chartGramMatrix_of_fixed_domain_metric_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.contMDiffOn_chartGramMatrix_of_fixed_domain_metric_convergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.contMDiffOn_chartGramMatrix_of_fixed_domain_metric_convergence

end DifferentialGeometry.CheegerGromovCompactness

end
