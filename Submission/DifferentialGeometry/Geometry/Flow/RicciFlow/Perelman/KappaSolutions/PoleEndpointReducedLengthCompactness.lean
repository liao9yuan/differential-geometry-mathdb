import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthEquicontinuity
import Submission.DifferentialGeometry.Analysis.Calculus.Compactness.ExhaustionArzelaAscoli
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3 : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3 : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2 : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 target :: scope.openDecls } }

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

private theorem exists_compact_closed_cylinder
    {X : Type*} [TopologicalSpace X] {A : Set (X × _root_.Set.Ici (1 : ℝ))}
    (hA : IsCompact A) :
    ∃ (J : Set X) (c : ℝ), IsCompact J ∧ 1 ≤ c ∧
      (∀ z ∈ A, z.1 ∈ J ∧ (z.2 : ℝ) ∈ _root_.Set.Icc 1 c) ∧
      ∃ embed : A → ↥(J ×ˢ _root_.Set.Icc 1 c), Continuous embed ∧
        ∀ z : A, (embed z).1 = (z.1.1, (z.1.2 : ℝ)) := by
  let time : X × _root_.Set.Ici (1 : ℝ) → ℝ := fun z => z.2
  have htime : Continuous time := continuous_subtype_val.comp continuous_snd
  obtain ⟨C, hC⟩ := (hA.image htime).bddAbove
  let c := _root_.Max.max 1 C
  let J : Set X := Prod.fst '' A
  have hJ : IsCompact J := hA.image continuous_fst
  have hcontain : ∀ z ∈ A, z.1 ∈ J ∧ (z.2 : ℝ) ∈ _root_.Set.Icc 1 c := by
    intro z hz
    exact ⟨⟨z, hz, rfl⟩, z.2.property, (hC ⟨z, hz, rfl⟩).trans (le_max_right _ _)⟩
  let embed : A → ↥(J ×ˢ _root_.Set.Icc 1 c) :=
    fun z => ⟨(z.1.1, (z.1.2 : ℝ)), hcontain z.1 z.2⟩
  have hembed : Continuous embed :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk
        (fun z : A => hcontain z.1 z.2)
  exact ⟨J, c, hJ, le_max_left _ _, hcontain, embed, hembed, fun _ => rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_compact_closed_cylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.exists_compact_closed_cylinder target :: scope.openDecls } }

namespace HalfLineMetricConvergenceData

theorem exists_subseq_tendstoLocallyUniformly_poleEndpoint_redLength
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A) :
    ∃ (psi : ℕ → ℕ) (ellC : C(P.M × _root_.Set.Ici (1 : ℝ), ℝ)), StrictMono psi ∧
      TendstoLocallyUniformly
        (fun k (z : P.M × _root_.Set.Ici (1 : ℝ)) =>
          redLength ((U).term (phi (co.φ (psi k)))).S 0 p
            (Phi.map (co.φ (psi k)) z.1) z.2) ellC atTop := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace H P.M
  let _ : LocallyCompactSpace (_root_.Set.Ici (1 : ℝ)) := isClosed_Ici.locallyCompactSpace
  let K : CompactExhaustion (P.M × _root_.Set.Ici (1 : ℝ)) := CompactExhaustion.choice _
  let f : ℕ → P.M × _root_.Set.Ici (1 : ℝ) → ℝ := fun k z =>
    redLength ((U).term (phi (co.φ k))).S 0 p (Phi.map (co.φ k) z.1) z.2
  have hnonneg (k : ℕ) (z : P.M × _root_.Set.Ici (1 : ℝ)) : 0 ≤ f k z := by
    obtain ⟨B, hB⟩ := (hancient (phi (co.φ k))).globalScalarBound
    apply div_nonneg _ (by positivity)
    apply lCost_nonneg_of_scalar_nonneg _ 0 (zero_le_one.trans z.2.property)
    intro s hs w
    simpa only [zero_sub] using (hB (-s) (by
      rw [ancientTimeInterval_carrier]
      exact neg_nonpos.mpr hs.1) w).1
  have hequi : ∀ n, ∃ N : ℕ,
      Equicontinuous (fun k (z : K n) => f (N + k) z) := by
    intro n
    obtain ⟨J, c, hJ, _, _, embed, hembed, hembed_val⟩ :=
      exists_compact_closed_cylinder (K.isCompact n)
    obtain ⟨N, hN⟩ :=
      exists_equicontinuous_poleEndpoint_redLength_tail_on_compact_time_interval
        F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
        (a := 1) (c := c) le_rfl hbase
    refine ⟨N, fun z entourage hEntourage => ?_⟩
    have hpull := hembed.continuousAt.eventually (hN (embed z) entourage hEntourage)
    filter_upwards [hpull] with w hw
    intro k
    simpa only [f, hembed_val] using hw k
  have hbdd : ∀ n, ∃ C : ℝ, ∀ᶠ k in _root_.Filter.atTop, ∀ z ∈ K n, |f k z| ≤ C := by
    intro n
    obtain ⟨J, c, hJ, _, hcontain, _⟩ :=
      exists_compact_closed_cylinder (K.isCompact n)
    obtain ⟨V, _, hcost⟩ :=
      exists_eventually_poleEndpoint_redLength_le_on_compact_time_interval
        F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
        (a := 1) (c := c) zero_lt_one hbase
    refine ⟨V, ?_⟩
    filter_upwards [hcost] with k hk
    intro z hz
    rw [abs_of_nonneg (hnonneg k z)]
    exact hk z.1 (hcontain z hz).1 z.2 (hcontain z hz).2
  exact DifferentialGeometry.Analysis.exists_subseq_tendstoLocallyUniformly_of_eventually_equicontinuous
    K f hequi hbdd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_subseq_tendstoLocallyUniformly_poleEndpoint_redLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_subseq_tendstoLocallyUniformly_poleEndpoint_redLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_subseq_tendstoLocallyUniformly_poleEndpoint_redLength ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_subseq_tendstoLocallyUniformly_poleEndpoint_redLength

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
