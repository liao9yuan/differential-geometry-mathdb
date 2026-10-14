import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurveEnergyBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedRicciConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.Interval

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance integratedLimitTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedLimitTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedLimitTopology target :: scope.openDecls } }
private local instance integratedLimitCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedLimitCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedLimitCharted target :: scope.openDecls } }
private local instance integratedLimitSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedLimitSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedLimitSmooth target :: scope.openDecls } }
private local instance integratedLimitC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedLimitC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedLimitC1 target :: scope.openDecls } }
private local instance integratedLimitT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedLimitT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedLimitT2 target :: scope.openDecls } }

private local instance integratedMetricTopology
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedMetricTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedMetricTopology target :: scope.openDecls } }
private local instance integratedMetricCharted
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedMetricCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedMetricCharted target :: scope.openDecls } }
private local instance integratedMetricSmooth
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedMetricSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedMetricSmooth target :: scope.openDecls } }
private local instance integratedMetricC1
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedMetricC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedMetricC1 target :: scope.openDecls } }
private local instance integratedMetricT2
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedMetricT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integratedMetricT2 target :: scope.openDecls } }

theorem pointed_limit_compensated_scalar_monotoneOn
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    (hconvergence : ∀ t ∈ X.D.carrier,
      ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (L := L) t) k)
    (gamma : ℝ → L.M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma)
    {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) :
    MonotoneOn (fun t => L.S.scalar t (gamma t) +
      (1 / 2 : ℝ) * ∫ s in a..t, smoothCurveRicciEnergy L.S gamma (s, s))
      (_root_.Set.Icc a b) := by
  classical
  let scalar : ℕ → ℝ → ℝ := fun i t => (X.term (phi i)).S.scalar t (Phi.map i (gamma t))
  let energy : ℕ → ℝ → ℝ := fun i t =>
    smoothCurveRicciEnergy (X.term (phi i)).S (fun s => Phi.map i (gamma s)) (t, t)
  have hcar : _root_.Set.Icc a b ⊆ X.D.carrier := by
    intro t ht
    rw [(hsource 0).carrier_eq]
    exact ht.2.trans hb
  have hzero : (0 : ℝ) ∈ X.D.carrier := by
    rw [(hsource 0).carrier_eq]
    exact (le_rfl : (0 : ℝ) ≤ 0)
  obtain ⟨C0, hC0⟩ := hconvergence 0 hzero
  obtain ⟨B, _hB, hbound⟩ := exists_pointed_curve_ricci_energy_bound
    Phi hsource C0 hC0 gamma hgamma (a := a) hb
  have he : ∀ᶠ i in _root_.Filter.atTop, ContinuousOn (energy i) (_root_.Set.Icc a b) := by
    filter_upwards [hbound] with i hi
    obtain ⟨U, hU, hcurve, hg, _⟩ := hi
    exact (locallySmoothCurveRicciEnergy_continuousOn
      (X.term (phi i)).S (X.term (phi i)).isSolution
      (fun t => Phi.map i (gamma t)) hU hg).comp
      (continuous_id.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hcar ht, hcurve ht⟩)
  have hdom : ∀ᶠ i in _root_.Filter.atTop, ∀ t ∈ _root_.Set.Icc a b, ‖energy i t‖ ≤ B := by
    filter_upwards [hbound] with i hi
    obtain ⟨U, hU, hcurve, hg, hnorm⟩ := hi
    exact hnorm
  have hmono : ∀ᶠ i in _root_.Filter.atTop, MonotoneOn
      (fun t => scalar i t + (1 / 2 : ℝ) * ∫ s in a..t, energy i s) (_root_.Set.Icc a b) := by
    filter_upwards [hbound] with i hi
    obtain ⟨U, hU, hcurve, hg, _⟩ := hi
    exact (hsource (phi i)).compensated_scalar_monotoneOn
      (fun t => Phi.map i (gamma t)) hU hg hab hb hcurve
  have hscalar (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) :
      Tendsto (fun i => scalar i t) _root_.Filter.atTop (𝓝 (L.S.scalar t (gamma t))) := by
    obtain ⟨Ct, hCt⟩ := hconvergence t (hcar ht)
    exact pointedScalar_tendsto_of_metricCG_canonical_domains Ct hCt (gamma t)
  have henergy (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) :
      _root_.Filter.Tendsto (fun i => energy i t) _root_.Filter.atTop
        (𝓝 (smoothCurveRicciEnergy L.S gamma (t, t))) := by
    obtain ⟨Ct, hCt⟩ := hconvergence t (hcar ht)
    let v : TangentSpace I (gamma t) := mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)
    have hRicci := pointedRicci_tendsto_of_metricCG_canonical_domains Ct hCt (gamma t) v
    obtain ⟨k0, hk0⟩ := Phi.source_exhausts.subset {gamma t} isCompact_singleton
    apply hRicci.congr'
    filter_upwards [Filter.eventually_ge_atTop k0] with i hi
    have hpoint : gamma t ∈ Phi.source i := hk0 i hi (_root_.Set.mem_singleton _)
    have hmap : MDifferentiableAt I I (Phi.map i) (gamma t) :=
      ((Phi.partialDiffeomorph i).contMDiffOn_toFun.contMDiffAt
        ((Phi.source_open i).mem_nhds hpoint)).mdifferentiableAt (by simp)
    have hv : mfderiv 𝓘(ℝ, ℝ) I (fun s => Phi.map i (gamma s)) t (1 : ℝ) =
        mfderiv I I (Phi.map i) (gamma t) v := by
      change mfderiv 𝓘(ℝ, ℝ) I (Phi.map i ∘ gamma) t (1 : ℝ) = _
      rw [mfderiv_comp t hmap (hgamma.mdifferentiableAt (x := t) (by norm_num))]
      rfl
    change _ = smoothCurveRicciEnergy (X.term (phi i)).S
      (fun s => Phi.map i (gamma s)) (t, t)
    simp only [smoothCurveRicciEnergy, hv]
    rfl
  apply monotoneOn_of_frequently_monotoneOn_of_tendsto
    (l := (_root_.Filter.atTop : Filter ℕ)) hmono.frequently
  intro t ht
  have hsub : Ι a t ⊆ _root_.Set.Icc a b := by
    rw [_root_.Set.uIoc_of_le ht.1]
    intro s hs
    exact ⟨hs.1.le, hs.2.trans ht.2⟩
  have hint : _root_.Filter.Tendsto (fun i => ∫ s in a..t, energy i s) _root_.Filter.atTop
      (𝓝 (∫ s in a..t, smoothCurveRicciEnergy L.S gamma (s, s))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B)
    · filter_upwards [he] with i hi
      exact (hi.mono hsub).aestronglyMeasurable measurableSet_uIoc
    · filter_upwards [hdom] with i hi
      exact _root_.MeasureTheory.ae_of_all _root_.MeasureTheory.MeasureSpace.volume (fun s hs => hi s (hsub hs))
    · exact intervalIntegrable_const
    · exact _root_.MeasureTheory.ae_of_all _root_.MeasureTheory.MeasureSpace.volume (fun s hs => henergy s (hsub hs))
  exact (hscalar t ht).add (hint.const_mul (1 / 2 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_limit_compensated_scalar_monotoneOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_limit_compensated_scalar_monotoneOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_limit_compensated_scalar_monotoneOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_limit_compensated_scalar_monotoneOn

theorem pointed_limit_scalar_le_add_curve_ricci_integral
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    (hconvergence : ∀ t ∈ X.D.carrier,
      ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (L := L) t) k)
    (gamma : ℝ → L.M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma)
    {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) :
    L.S.scalar a (gamma a) ≤ L.S.scalar b (gamma b) +
      (1 / 2 : ℝ) * ∫ s in a..b, smoothCurveRicciEnergy L.S gamma (s, s) := by
  have h := pointed_limit_compensated_scalar_monotoneOn Phi hsource hconvergence
    gamma hgamma hab hb ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  simpa only [intervalIntegral.integral_same, _root_.MulZeroClass.mul_zero, add_zero] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_limit_scalar_le_add_curve_ricci_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_limit_scalar_le_add_curve_ricci_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_limit_scalar_le_add_curve_ricci_integral ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_limit_scalar_le_add_curve_ricci_integral

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
