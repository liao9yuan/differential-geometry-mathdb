import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.JacobianComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.SeamBase
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.ExponentialClosedStart
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.MinDomainMeasurable
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryScalarFloor
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryHorizonExtension
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaInequality
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Parametric.InjectiveAreaInequality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature (metricScalarAt)

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instMeasurableSpaceCarrier (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instMeasurableSpaceCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instMeasurableSpaceCarrier target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instBorelSpaceCarrier (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instBorelSpaceCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instBorelSpaceCarrier target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instMeasurableSpaceThreeSpace : MeasurableSpace ThreeSpace := borel ThreeSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instMeasurableSpaceThreeSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instMeasurableSpaceThreeSpace target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instBorelSpaceThreeSpace : BorelSpace ThreeSpace := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instBorelSpaceThreeSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instBorelSpaceThreeSpace target :: scope.openDecls } }

namespace ObservedHistory

variable {H : ObservedHistory.{u}} {first last k : Fin (H.eventCount + 1)} {T B v₁ v₂ : ℝ}
  {p : (H.stage last).Carrier}

theorem lintegral_image_historyMinDomain_le_of_lt {hle : first ≤ last} (hkl : k ≤ last)
    (hfk : first ≤ k)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hT : T ∈ _root_.Set.Ico (H.time last) (H.stageEndTime last)) (hv₁ : 0 < v₁) (h12 : v₁ < v₂)
    (hk : T - v₁ ^ 2 ∈ H.stageDomain k) :
    ∫⁻ q in H.historyLExp hle T v₂ p '' (Subtype.val ⁻¹' H.historyMinDomain hle T B v₂ p),
        H.regularizedDensity first last hle T B v₂ p q
        ∂riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
          (H.stageMetric first (T - v₂ ^ 2)) ≤
      ∫⁻ q in H.regularMinimizerEndpoints k last hkl T B v₁ p,
        H.regularizedDensity k last hkl T B v₁ p q
        ∂riemannianVolumeMeasure ThreeModel (H.stage k).Carrier (H.stageMetric k (T - v₁ ^ 2)) := by
  classical
  have hv₂ : 0 < v₂ := hv₁.trans h12
  set K : Set ThreeSpace := H.historyMinDomain hle T B v₂ p with hKdef
  rcases K.eq_empty_or_nonempty with hK0 | ⟨Z₀, hZ₀⟩
  · have : Subtype.val ⁻¹' H.historyMinDomain hle T B v₂ p =
        (∅ : Set (H.historyLExpDomain hle T v₂ p)) := by
      ext Z
      simp only [_root_.Set.mem_preimage, _root_.Set.mem_empty_iff_false, iff_false]
      intro hZ
      exact (hK0 ▸ hZ : Z.1 ∈ (∅ : Set ThreeSpace))
    rw [this, _root_.Set.image_empty, Measure.restrict_empty, _root_.MeasureTheory.lintegral_zero_measure]
    exact bot_le
  have hZ₀d : Z₀ ∈ H.historyLExpDomain hle T v₂ p :=
    historyMinDomain_subset_historyLExpDomain hZ₀
  have hZ₀₁ : Z₀ ∈ H.historyLExpDomain hkl T v₁ p :=
    mem_historyLExpDomain_of_le hfk hkl hv₁ h12.le hk hZ₀d
  obtain ⟨U₂, hU₂, hKU₂, hU₂d, ⟨f₂, hf₂, hf₂eq⟩, -⟩ :=
    exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain (hle := hle) (p := p)
      hv₂ hT hfloor (H.historyLExp hle T v₂ p ⟨Z₀, hZ₀d⟩)
  obtain ⟨U₁, hU₁, hKU₁, hU₁d, ⟨f₁, hf₁, hf₁eq⟩, -⟩ :=
    exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain (hle := hkl) (p := p)
      hv₁ hT hfloor (H.historyLExp hkl T v₁ p ⟨Z₀, hZ₀₁⟩)
  have hKK₁ : K ⊆ H.historyMinDomain hkl T B v₁ p :=
    historyMinDomain_subset_of_le hfloor hkl hv₁ h12.le hk
  have hKm : @MeasurableSet ThreeSpace (borel ThreeSpace) K :=
    measurableSet_historyMinDomain hv₂ hT hfloor
  have himg₂ : H.historyLExp hle T v₂ p '' (Subtype.val ⁻¹' K) = f₂ '' K := by
    ext q
    constructor
    · rintro ⟨Z, hZ, rfl⟩
      exact ⟨Z.1, hZ, hf₂eq Z.1 Z.2⟩
    · rintro ⟨Z, hZ, rfl⟩
      exact ⟨⟨Z, historyMinDomain_subset_historyLExpDomain hZ⟩, hZ,
        (hf₂eq Z (historyMinDomain_subset_historyLExpDomain hZ)).symm⟩
  have himg₁ : f₁ '' K ⊆ H.regularMinimizerEndpoints k last hkl T B v₁ p := by
    rintro _ ⟨Z, hZ, rfl⟩
    have hZd := hU₁d (hKU₁ (hKK₁ hZ))
    rw [hf₁eq Z hZd]
    exact (image_historyMinDomain_subset_of_le hfloor hkl hv₁ h12.le hk
      ⟨⟨Z, hZd⟩, hZ, rfl⟩).1
  have hinj : _root_.Set.InjOn f₁ K := by
    intro Z hZ Z' hZ' hEq
    have hZd := hU₁d (hKU₁ (hKK₁ hZ))
    have hZd' := hU₁d (hKU₁ (hKK₁ hZ'))
    rw [hf₁eq Z hZd, hf₁eq Z' hZd'] at hEq
    exact congrArg Subtype.val
      (injOn_historyLExp_of_lt_of_mem_Ico hkl hfloor hT hv₁ h12 hk hZ hZ' hEq)
  have hpt : ∀ Z ∈ K,
      ENNReal.ofReal (paramDensity (H.stageMetric first (T - v₂ ^ 2)) f₂ Z) *
          H.regularizedDensity first last hle T B v₂ p (f₂ Z) ≤
        ENNReal.ofReal (paramDensity (H.stageMetric k (T - v₁ ^ 2)) f₁ Z) *
          H.regularizedDensity k last hkl T B v₁ p (f₁ Z) := by
    intro Z hZ
    have hZd₂ : Z ∈ H.historyLExpDomain hle T v₂ p := hU₂d (hKU₂ hZ)
    have hZ₁m : Z ∈ H.historyMinDomain hkl T B v₁ p := hKK₁ hZ
    have hZd₁ : Z ∈ H.historyLExpDomain hkl T v₁ p :=
      mem_historyLExpDomain_of_le hfk hkl hv₁ h12.le hk hZd₂
    have hJ₂ : paramDensity (H.stageMetric first (T - v₂ ^ 2)) f₂ Z =
        H.historyLJacobianDensity hle T v₂ p ⟨Z, hZd₂⟩ ⟨first, le_rfl, hle⟩ v₂ := by
      refine paramDensity_eq_historyLJacobianDensity_of_eventuallyEq (Z₀ := ⟨Z, hZd₂⟩)
        ⟨first, le_rfl, hle⟩ v₂ ?_
      filter_upwards [hU₂.mem_nhds (hKU₂ hZ)] with W hW
      rw [hf₂eq W (hU₂d hW), historyLCurveMap_of_mem _ _ (hU₂d hW)]
      rfl
    have hJ₁ : paramDensity (H.stageMetric k (T - v₁ ^ 2)) f₁ Z =
        H.historyLJacobianDensity hkl T v₁ p ⟨Z, hZd₁⟩ ⟨k, le_rfl, hkl⟩ v₁ := by
      refine paramDensity_eq_historyLJacobianDensity_of_eventuallyEq (Z₀ := ⟨Z, hZd₁⟩)
        ⟨k, le_rfl, hkl⟩ v₁ ?_
      filter_upwards [hU₁.mem_nhds (hKU₁ hZ₁m)] with W hW
      rw [hf₁eq W (hU₁d hW), historyLCurveMap_of_mem _ _ (hU₁d hW)]
      rfl
    have hsrc := H.historyLSourceDensity_pos (T := T) (p := p)
    have e₂ := ofReal_historyReducedJacobian_eq hfloor hv₂ (Z₀ := ⟨Z, hZd₂⟩) hZ
    have e₁ := ofReal_historyReducedJacobian_eq hfloor hv₁ (Z₀ := ⟨Z, hZd₁⟩) hZ₁m
    have hmono := historyReducedJacobian_le_of_le hfloor hfk hkl hv₁ h12.le hk
      ⟨Z, hZd₂⟩ hZ
    have key (J s : ℝ) (hs : 0 < s) (d : ℝ≥0∞) :
        ENNReal.ofReal J * d = ENNReal.ofReal s * (ENNReal.ofReal (J / s) * d) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hs.le, mul_div_cancel₀ _ hs.ne']
    rw [hJ₂, hJ₁, hf₂eq Z hZd₂, hf₁eq Z hZd₁,
      key (H.historyLJacobianDensity hle T v₂ p ⟨Z, hZd₂⟩ ⟨first, le_rfl, hle⟩ v₂) _ hsrc,
      key (H.historyLJacobianDensity hkl T v₁ p ⟨Z, hZd₁⟩ ⟨k, le_rfl, hkl⟩ v₁) _ hsrc, ← e₂, ← e₁]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hmono)
  rw [himg₂]
  calc _ ≤ ∫⁻ Z in K, ENNReal.ofReal (paramDensity (H.stageMetric first (T - v₂ ^ 2)) f₂ Z) *
          H.regularizedDensity first last hle T B v₂ p (f₂ Z) ∂(modelHaar (E := ThreeSpace)) :=
        lintegral_image_le_lintegral_paramDensity_mul _ hU₂ hKm hKU₂ hf₂ _
    _ ≤ ∫⁻ Z in K, ENNReal.ofReal (paramDensity (H.stageMetric k (T - v₁ ^ 2)) f₁ Z) *
          H.regularizedDensity k last hkl T B v₁ p (f₁ Z) ∂(modelHaar (E := ThreeSpace)) :=
        _root_.MeasureTheory.setLIntegral_mono' hKm hpt
    _ ≤ ∫⁻ q in f₁ '' K, H.regularizedDensity k last hkl T B v₁ p q
          ∂riemannianVolumeMeasure ThreeModel (H.stage k).Carrier
            (H.stageMetric k (T - v₁ ^ 2)) :=
        lintegral_paramDensity_mul_le_lintegral_image _ hU₁ hKm
          (fun Z hZ => hKU₁ (hKK₁ hZ)) hf₁ hinj _
    _ ≤ _ := _root_.MeasureTheory.lintegral_mono_set himg₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lintegral_image_historyMinDomain_le_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lintegral_image_historyMinDomain_le_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lintegral_image_historyMinDomain_le_of_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lintegral_image_historyMinDomain_le_of_lt

end ObservedHistory

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀)

theorem reducedVolume_le_of_lt_of_mem_Ico (k : Fin (H.eventCount + 1)) (p : (H.stage k).Carrier)
    {T v₁ v₂ : ℝ} (hT : T ∈ _root_.Set.Ico (H.toHistory.time k) (H.toHistory.stageEndTime k))
    (hTk : T ∈ H.toHistory.stageDomain k) (hv₁ : 0 < v₁) (h12 : v₁ < v₂) (hv₂T : v₂ ^ 2 ≤ T) :
    H.reducedVolume k p T v₂ ≤ H.reducedVolume k p T v₁ := by
  obtain ⟨b, hb⟩ := H.exists_reducedVolume_eq_lintegral_image_historyMinDomain_of_mem_Ico
  obtain ⟨b', -, hfl⟩ := H.exists_stageMetric_scalar_lower_bound
  obtain ⟨b'', hb''⟩ := H.exists_reducedVolume_eq_lintegral
  set B₀ := _root_.Max.max b (_root_.Max.max b' b'')
  have hfloor : ∀ j, ∀ t ∈ H.toHistory.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H.toHistory.stageMetric j t) x := fun j t ht x =>
    (neg_le_neg (le_max_of_le_right (le_max_left _ _))).trans (hfl j t ht x)
  have hTI := H.mem_Icc_zero_horizon_of_mem_stageDomain hTk
  have hv₂ : 0 < v₂ := hv₁.trans h12
  have hmem (v : ℝ) (hv : 0 ≤ v) (hvT : v ^ 2 ≤ T) :
      T - v ^ 2 ∈ H.toHistory.stageDomain
        (H.toHistory.activeStage (_root_.Set.projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2))) := by
    have h := H.toHistory.activeStage_mem (_root_.Set.projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2))
    have hv' : ((_root_.Set.projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2) : ℝ)) = T - v ^ 2 := by
      rw [_root_.Set.projIcc_of_mem _ ⟨by linarith, by linarith [hTI.2, sq_nonneg v]⟩]
    rwa [hv'] at h
  have hv₁T : v₁ ^ 2 ≤ T := (pow_le_pow_left₀ hv₁.le h12.le 2).trans hv₂T
  have hT0 : T - (0 : ℝ) ^ 2 ∈ H.toHistory.stageDomain k := by simpa using hTk
  have hle₂ := ObservedHistory.first_le_of_mem_stageDomain le_rfl hv₂.le
    (hmem v₂ hv₂.le hv₂T) hT0
  have hle₁ := ObservedHistory.first_le_of_mem_stageDomain le_rfl hv₁.le
    (hmem v₁ hv₁.le hv₁T) hT0
  have hfk := ObservedHistory.first_le_of_mem_stageDomain hv₁.le h12.le
    (hmem v₂ hv₂.le hv₂T) (hmem v₁ hv₁.le hv₁T)
  rw [hb B₀ (le_max_left _ _) k p T v₂ hle₂ hv₂ hT,
    hb'' B₀ ((le_max_right _ _).trans (le_max_right _ _)) k p T v₁ hle₁]
  exact ObservedHistory.lintegral_image_historyMinDomain_le_of_lt hle₁ hfk hfloor hT hv₁ h12
    (hmem v₁ hv₁.le hv₁T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.reducedVolume_le_of_lt_of_mem_Ico then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.reducedVolume_le_of_lt_of_mem_Ico"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.reducedVolume_le_of_lt_of_mem_Ico ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.reducedVolume_le_of_lt_of_mem_Ico

end RetainedCoreHistory

theorem historyReducedVolumeMonotone_holds (P₀ : OrientedThreeStage.{u}) :
    HistoryReducedVolumeMonotone P₀ := by
  intro H k p T v₁ v₂ hT hv₁ h12 hv₂T
  rcases h12.eq_or_lt with rfl | h12
  · exact le_rfl
  obtain ⟨T', hT', G, hG, hagree⟩ := H.exists_extendHorizon_gt
  have hTle : T ≤ H.horizon := (H.mem_Icc_zero_horizon_of_mem_stageDomain hT).2
  rw [← H.reducedVolume_extendHorizon hT'.le G hG hagree k p hTle,
    ← H.reducedVolume_extendHorizon hT'.le G hG hagree k p hTle]
  exact (H.extendHorizon T' hT'.le G hG).reducedVolume_le_of_lt_of_mem_Ico k p
    (H.mem_Ico_extendHorizon_of_mem_stageDomain hT' G hG hT)
    (H.stageDomain_extendHorizon hT'.le G hG k hT) hv₁ h12 hv₂T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeMonotone_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeMonotone_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeMonotone_holds ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeMonotone_holds

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
