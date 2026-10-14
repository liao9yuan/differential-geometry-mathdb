import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonReduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.NNReal
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

section SmoothDiskTrace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

omit [IsManifold 𝓘(ℝ, F) ∞ N] in
theorem contMDiff_of_exists_smoothDisk_trace
    (u : SmoothDisk (I := 𝓘(ℝ, F)) (Q := N)) (γ : ContinuousFreeLoop N)
    (htrace : ∀ θ, u.map (diskBoundary θ) = γ θ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞ (fun t : ℝ => γ (t : Surgery.Topology.Circle)) := by
  have h := (SmoothDisk.diskSmoothUpToBoundary u).trace
  exact h.congr (fun t => (htrace (t : Surgery.Topology.Circle)).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.contMDiff_of_exists_smoothDisk_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.contMDiff_of_exists_smoothDisk_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.contMDiff_of_exists_smoothDisk_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.contMDiff_of_exists_smoothDisk_trace

end SmoothDiskTrace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [hT2 : T2Space Q] [hCompact : CompactSpace Q]
  [hBoundary : I.Boundaryless] [hSigma : SigmaCompactSpace Q]

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem diskArea_le_of_minimizingSmoothDisk_of_density
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (u : SmoothDisk (I := I) (Q := Q))
    (hmin : ∀ v : SmoothDisk (I := I) (Q := Q),
      (∀ theta, v.map (diskBoundary theta) = γ theta) →
        diskArea g u.map ≤ diskArea g v.map)
    (hdensity : ∀ v : DiskCompetitor g γ.toContinuousLoop,
      ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
        (∀ j theta, (w j).map (diskBoundary theta) = γ theta) ∧
          _root_.Filter.Tendsto (fun j => diskArea g (w j).map) _root_.Filter.atTop (𝓝 (diskArea g v.1.map))) :
    ∀ v : DiskCompetitor g γ.toContinuousLoop, diskArea g u.map ≤ diskArea g v.1.map := by
  intro v
  obtain ⟨w, htracew, hlim⟩ := hdensity v
  exact ge_of_tendsto' hlim (fun j => hmin (w j) (htracew j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_le_of_minimizingSmoothDisk_of_density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_le_of_minimizingSmoothDisk_of_density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_le_of_minimizingSmoothDisk_of_density ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_le_of_minimizingSmoothDisk_of_density

omit hSigma in
theorem diskArea_eq_leastArea_of_minimizingDiskCompetitor
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hctr : IsContractibleLoop γ.toContinuousLoop)
    (u : SmoothDisk (I := I) (Q := Q)) (σ : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (σ.map theta))
    (hmin : ∀ v : DiskCompetitor g γ.toContinuousLoop,
      diskArea g u.map ≤ diskArea g v.1.map) :
    diskArea g u.map = leastArea g γ.toContinuousLoop hctr (γ.isLipschitz g) := by
  apply le_antisymm
  · apply le_csInf (competitorAreas_nonempty g γ.toContinuousLoop hctr (γ.isLipschitz g))
    rintro _ ⟨v, rfl⟩
    exact hmin v
  · obtain ⟨ulip, hulip⟩ := u.exists_lipschitz g
    have htracelip : ∀ theta, ulip.map (diskBoundary theta) = γ (σ.map theta) := by
      simpa only [hulip] using htrace
    obtain ⟨v, hv⟩ := zero_area_trace_annulus g γ hγ σ ulip htracelip
    have hle := leastArea_le_competitor g γ.toContinuousLoop hctr (γ.isLipschitz g) v
    simpa only [hv, hulip] using hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_leastArea_of_minimizingDiskCompetitor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_leastArea_of_minimizingDiskCompetitor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_leastArea_of_minimizingDiskCompetitor ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_leastArea_of_minimizingDiskCompetitor

omit hSigma in
theorem exists_diskCompetitor_diskArea_eq_leastArea_of_minimizingDiskCompetitor
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hctr : IsContractibleLoop γ.toContinuousLoop)
    (u : SmoothDisk (I := I) (Q := Q)) (σ : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (σ.map theta))
    (hmin : ∀ v : DiskCompetitor g γ.toContinuousLoop,
      diskArea g u.map ≤ diskArea g v.1.map) :
    ∃ w : DiskCompetitor g γ.toContinuousLoop,
      diskArea g w.1.map = leastArea g γ.toContinuousLoop hctr (γ.isLipschitz g) := by
  have hA := diskArea_eq_leastArea_of_minimizingDiskCompetitor g γ hγ hctr u σ htrace hmin
  obtain ⟨ulip, hulip⟩ := u.exists_lipschitz g
  have htracelip : ∀ theta, ulip.map (diskBoundary theta) = γ (σ.map theta) := by
    simpa only [hulip] using htrace
  obtain ⟨v, hv⟩ := zero_area_trace_annulus g γ hγ σ ulip htracelip
  exact ⟨v, by rw [hv, hulip]; exact hA⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_diskCompetitor_diskArea_eq_leastArea_of_minimizingDiskCompetitor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_diskCompetitor_diskArea_eq_leastArea_of_minimizingDiskCompetitor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_diskCompetitor_diskArea_eq_leastArea_of_minimizingDiskCompetitor ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_diskCompetitor_diskArea_eq_leastArea_of_minimizingDiskCompetitor

omit hSigma in
theorem diskArea_eq_leastArea_of_minimizingSmoothDisk_of_density
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hctr : IsContractibleLoop γ.toContinuousLoop)
    (u : SmoothDisk (I := I) (Q := Q)) (σ : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (σ.map theta))
    (hmin : ∀ v : SmoothDisk (I := I) (Q := Q),
      (∀ theta, v.map (diskBoundary theta) = γ theta) →
        diskArea g u.map ≤ diskArea g v.map)
    (hdensity : ∀ v : DiskCompetitor g γ.toContinuousLoop,
      ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
        (∀ j theta, (w j).map (diskBoundary theta) = γ theta) ∧
          _root_.Filter.Tendsto (fun j => diskArea g (w j).map) _root_.Filter.atTop (𝓝 (diskArea g v.1.map))) :
    diskArea g u.map = leastArea g γ.toContinuousLoop hctr (γ.isLipschitz g) :=
  diskArea_eq_leastArea_of_minimizingDiskCompetitor g γ hγ hctr u σ htrace
    (diskArea_le_of_minimizingSmoothDisk_of_density g γ u hmin hdensity)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_leastArea_of_minimizingSmoothDisk_of_density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_leastArea_of_minimizingSmoothDisk_of_density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_leastArea_of_minimizingSmoothDisk_of_density ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_leastArea_of_minimizingSmoothDisk_of_density

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem diskArea_const_le_diskCompetitor (g : SmoothRiemannianMetric I Q) (q : Q)
    (v : DiskCompetitor g (constantLoops q)) :
    diskArea g (⇑(SmoothDisk.const (I := I) (Q := Q) q).map) ≤ diskArea g v.1.map := by
  rw [show (⇑(SmoothDisk.const (I := I) (Q := Q) q).map : Disk → Q) = (fun _ : Disk => q)
    from rfl, diskArea_const]
  exact diskArea_nonneg g v.1.map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_const_le_diskCompetitor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_const_le_diskCompetitor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_const_le_diskCompetitor ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_const_le_diskCompetitor

variable {D : RealTimeInterval} {a b : ℝ}

omit hSigma in
theorem transportedArea_at_base_eq_loopFamilyLeastArea_of_minimizingDiskCompetitor
    (W : SmoothMetricWindow (I := I) (M := Q) D a b) (t₀ : ℝ) (ht₀ : t₀ ∈ _root_.Set.Ico a b)
    (gamma : ℝ → RegularLoop I Q)
    (hgamma : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).SmoothOn
      (I := I) (_root_.Set.Icc a b))
    (hctr : IsContractibleLoop (gamma t₀).toContinuousLoop)
    (u : SmoothDisk (I := I) (Q := Q)) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) =
      (gamma t₀).toContinuousLoop (sigma.map theta))
    (hmin : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.1.map)
    (Phi : ℝ → Diffeomorph I I Q Q ∞) (hid : ∀ q, Phi t₀ q = q) :
    loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀ =
      u.transportedArea W.family.metric Phi t₀ := by
  have ht₀Icc : t₀ ∈ _root_.Set.Icc a b := ⟨ht₀.1, ht₀.2.le⟩
  have hγtsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift (gamma t₀).toContinuousLoop) := by
    have h := CurveMap.space_slice_contMDiffOn
      (curveOfLoopFamily (fun v => (gamma v).toContinuousLoop)) (_root_.Set.Icc a b) hgamma t₀ ht₀Icc
    rwa [contMDiffOn_univ] at h
  let γt : RegularLoop I Q :=
    regularLoopSlice (fun v => (gamma v).toContinuousLoop) hgamma t₀ ht₀Icc
  have hatt := diskArea_eq_leastArea_of_minimizingDiskCompetitor
    (g := W.family.metric t₀) (γ := γt) hγtsmooth hctr u sigma htrace hmin
  have htrans : u.transportedArea W.family.metric Phi t₀ =
      diskArea (W.family.metric t₀) u.map := by
    rw [SmoothDisk.transportedArea]
    congr 1
    funext z
    exact hid (u.map z)
  rw [htrans, loopFamilyLeastArea_eq (W.family.metric) (fun v => (gamma v).toContinuousLoop) t₀
    hctr (γt.isLipschitz (W.family.metric t₀))]
  exact hatt.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.transportedArea_at_base_eq_loopFamilyLeastArea_of_minimizingDiskCompetitor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.transportedArea_at_base_eq_loopFamilyLeastArea_of_minimizingDiskCompetitor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.transportedArea_at_base_eq_loopFamilyLeastArea_of_minimizingDiskCompetitor ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.transportedArea_at_base_eq_loopFamilyLeastArea_of_minimizingDiskCompetitor

omit hSigma in
theorem rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_transportedAreaDeriv
    (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ _root_.Set.Ico a b)
    (gamma : ℝ → RegularLoop I Q)
    (hgamma : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).SmoothOn
      (I := I) (_root_.Set.Icc a b))
    (hemb : ∀ t ∈ _root_.Set.Icc a b, Topology.IsEmbedding (gamma t : Surgery.Topology.Circle → Q))
    (himm : ∀ t ∈ _root_.Set.Icc a b, ∀ x, loopVelocity (I := I) (gamma t).toContinuousLoop x ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop (gamma t₀).toContinuousLoop)
    (u : SmoothDisk (I := I) (Q := Q)) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma t₀ (sigma.map theta))
    (hconformal : u.IsConformal (W.family.metric t₀))
    (hharmonic : u.IsHarmonic (W.family.metric t₀))
    (hmin : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.1.map)
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (_root_.Set.univ ×ˢ _root_.Set.Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ _root_.Set.Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta)
    (hintDensity : _root_.MeasureTheory.IntegrableOn
      (diskExtension (u.metricVariationDensity W.family.metric (_root_.Set.Icc a b) t₀))
      (Metric.closedBall (0 : ℂ) 1))
    (hintFlux : IntervalIntegrable
      (u.boundaryFluxDensity (W.family.metric t₀)
        (u.isotopyVelocity Phi (_root_.Set.Icc a b) t₀ hid)) _root_.MeasureTheory.MeasureSpace.volume 0 1)
    (hderiv : HasDerivWithinAt (u.transportedArea W.family.metric Phi)
      ((1 / 2 : ℝ) *
        (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (u.metricVariationDensity W.family.metric (_root_.Set.Icc a b) t₀) z) -
        u.boundaryFlux (W.family.metric t₀) (u.isotopyVelocity Phi (_root_.Set.Icc a b) t₀ hid))
      (_root_.Set.Icc a b) t₀) :
    let V := u.isotopyVelocity Phi (_root_.Set.Icc a b) t₀ hid
    let metricTerm := u.metricVariationDensity W.family.metric (_root_.Set.Icc a b) t₀
    let variation := (1 / 2 : ℝ) *
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension metricTerm z) -
        u.boundaryFlux (W.family.metric t₀) V
    _root_.MeasureTheory.IntegrableOn (diskExtension metricTerm) (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (u.boundaryFluxDensity (W.family.metric t₀) V) _root_.MeasureTheory.MeasureSpace.volume 0 1 ∧
      (∀ t ∈ _root_.Set.Icc a b,
        loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t ≤
          u.transportedArea W.family.metric Phi t) ∧
      loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀ =
        u.transportedArea W.family.metric Phi t₀ ∧
      HasDerivWithinAt (u.transportedArea W.family.metric Phi) variation (_root_.Set.Icc a b) t₀ ∧
      ∀ epsilon > 0, ∃ delta > 0, ∀ h ∈ _root_.Set.Ioo (0 : ℝ) delta, t₀ + h ≤ b →
        (loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) (t₀ + h) -
          loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀) / h ≤
            variation + epsilon := by
  let _ := hemb
  let _ := himm
  let _ := hconformal
  let _ := hharmonic
  let _ := hPhi
  dsimp only
  refine ⟨hintDensity, hintFlux, ?_, ?_, hderiv, ?_⟩
  · intro t ht
    exact loopFamilyLeastArea_transportedArea_le W t₀ gamma hgamma u sigma htrace Phi
      (fun t ht theta => hboundary t ht theta) t ht
  · exact transportedArea_at_base_eq_loopFamilyLeastArea_of_minimizingDiskCompetitor W t₀ ht₀
      gamma hgamma hctr u sigma htrace hmin Phi hid
  · refine slope_le_add_of_derivWithin_of_upper_contact ht₀ hderiv ?_ ?_
    · intro t ht
      exact loopFamilyLeastArea_transportedArea_le W t₀ gamma hgamma u sigma htrace Phi
        (fun t ht theta => hboundary t ht theta) t ht
    · exact transportedArea_at_base_eq_loopFamilyLeastArea_of_minimizingDiskCompetitor W t₀ ht₀
        gamma hgamma hctr u sigma htrace hmin Phi hid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_transportedAreaDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_transportedAreaDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_transportedAreaDeriv ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_transportedAreaDeriv

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
