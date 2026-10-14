import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonVariation
import Submission.DifferentialGeometry.Topology.StandardModel
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.NNReal
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem StandardModelCopy.compactSpace (c : StandardModelCopy I M F) [CompactSpace M] :
    CompactSpace c.Q :=
  c.equiv.toHomeomorph.compactSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.StandardModelCopy.compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.StandardModelCopy.compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.StandardModelCopy.compactSpace ``Submission.DifferentialGeometry.Geometry.Topology.StandardModelCopy.compactSpace

end DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem mfderivWithin_Icc_eq_mfderiv_of_mem_Ico {F : ℝ → Q} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ _root_.Set.Ico a b) (hd : MDifferentiableAt 𝓘(ℝ, ℝ) I F t₀) :
    mfderivWithin 𝓘(ℝ, ℝ) I F (_root_.Set.Icc a b) t₀ = mfderiv 𝓘(ℝ, ℝ) I F t₀ := by
  have hab : a < b := lt_of_le_of_lt ht₀.1 ht₀.2
  have ht₀Icc : t₀ ∈ _root_.Set.Icc a b := ⟨ht₀.1, ht₀.2.le⟩
  exact mfderivWithin_eq_mfderiv ((uniqueDiffOn_Icc hab) t₀ ht₀Icc).uniqueMDiffWithinAt hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mfderivWithin_Icc_eq_mfderiv_of_mem_Ico then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mfderivWithin_Icc_eq_mfderiv_of_mem_Ico"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mfderivWithin_Icc_eq_mfderiv_of_mem_Ico ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mfderivWithin_Icc_eq_mfderiv_of_mem_Ico

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem mfderivWithin_Icc_eq_mfderivWithin_of_isOpen {F : ℝ → Q} {a b t₀ : ℝ} {T : Set ℝ}
    (ht₀ : t₀ ∈ _root_.Set.Ico a b) (hd : MDifferentiableAt 𝓘(ℝ, ℝ) I F t₀)
    (hTopen : IsOpen T) (hT₀ : t₀ ∈ T) :
    mfderivWithin 𝓘(ℝ, ℝ) I F (_root_.Set.Icc a b) t₀ = mfderivWithin 𝓘(ℝ, ℝ) I F T t₀ :=
  (mfderivWithin_Icc_eq_mfderiv_of_mem_Ico ht₀ hd).trans
    (mfderivWithin_of_mem_nhds (hTopen.mem_nhds hT₀)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mfderivWithin_Icc_eq_mfderivWithin_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mfderivWithin_Icc_eq_mfderivWithin_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mfderivWithin_Icc_eq_mfderivWithin_of_isOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mfderivWithin_Icc_eq_mfderivWithin_of_isOpen

end Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [hT2 : T2Space Q] [hCompact : CompactSpace Q]
  [hBoundary : I.Boundaryless] [hSigma : SigmaCompactSpace Q]

theorem rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_of_openIsotopy
    (c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E) [CompactSpace c.Q]
    {D : RealTimeInterval} {a b : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
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
    (T : Set ℝ) (hTopen : IsOpen T) (hTsub : _root_.Set.Icc a b ⊆ T)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (_root_.Set.univ ×ˢ T))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ _root_.Set.Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta) :
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
  have ht₀Icc : t₀ ∈ _root_.Set.Icc a b := ⟨ht₀.1, ht₀.2.le⟩
  have ht₀T : t₀ ∈ T := hTsub ht₀Icc
  have hreg : D.regular ∈ 𝓝 t₀ :=
    D.regular_isOpen.mem_nhds (W.regular ⟨ht₀.1, ht₀.2.le⟩)
  obtain ⟨hIntT, hFluxT, hDerivT⟩ :=
    SmoothDisk.hasDerivAt_transportedArea_isotopy_flux c W.smooth hreg u hconformal hharmonic
      hTopen ht₀T Phi hPhi hid
  have hdiff₁ (z : Disk) : DifferentiableAt ℝ (fun t : ℝ =>
      (W.family.metric t).inner (u.map z) (u.differential z (1 : ℂ))
        (u.differential z (1 : ℂ))) t₀ :=
    ((W.smooth.coeff (u.map z) (u.differential z (1 : ℂ)) (u.differential z (1 : ℂ))).contDiffAt
      hreg).differentiableAt (by simp)
  have hdiff₂ (z : Disk) : DifferentiableAt ℝ (fun t : ℝ =>
      (W.family.metric t).inner (u.map z) (u.differential z Complex.I)
        (u.differential z Complex.I)) t₀ :=
    ((W.smooth.coeff (u.map z) (u.differential z Complex.I) (u.differential z Complex.I)).contDiffAt
      hreg).differentiableAt (by simp)
  have hdensInt : (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric T t₀) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric (_root_.Set.Icc a b) t₀) z := by
    refine _root_.MeasureTheory.setIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
    rw [show diskExtension (u.metricVariationDensity W.family.metric T t₀) z =
        u.metricVariationDensity W.family.metric T t₀ ⟨z, hz⟩ from dif_pos hz,
      show diskExtension (u.metricVariationDensity W.family.metric (_root_.Set.Icc a b) t₀) z =
        u.metricVariationDensity W.family.metric (_root_.Set.Icc a b) t₀ ⟨z, hz⟩ from dif_pos hz]
    simp only [SmoothDisk.metricVariationDensity]
    split_ifs with hpos
    · rw [derivWithin_of_mem_nhds (hTopen.mem_nhds ht₀T),
        derivWithin_of_mem_nhds (hTopen.mem_nhds ht₀T),
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀ (hdiff₁ ⟨z, hz⟩),
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀ (hdiff₂ ⟨z, hz⟩)]
    · rfl
  have hvel : u.isotopyVelocity Phi (_root_.Set.Icc a b) t₀ hid =
      u.isotopyVelocity Phi T t₀ hid := by
    funext z
    change mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) (_root_.Set.Icc a b) t₀ 1 =
      mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) T t₀ 1
    have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) t₀ := by
      have hbase : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
          (u.map z, t₀) :=
        hPhi.contMDiffAt ((isOpen_univ.prod hTopen).mem_nhds ⟨trivial, ht₀T⟩)
      exact (hbase.mdifferentiableAt (by simp)).comp t₀
        (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    exact congrArg (fun L => L 1)
      (mfderivWithin_Icc_eq_mfderivWithin_of_isOpen ht₀ hmdiff hTopen ht₀T)
  have hFluxIcc : IntervalIntegrable
      (u.boundaryFluxDensity (W.family.metric t₀)
        (u.isotopyVelocity Phi (_root_.Set.Icc a b) t₀ hid)) _root_.MeasureTheory.MeasureSpace.volume 0 1 := by
    rw [hvel]
    exact hFluxT
  have hderivIcc : HasDerivWithinAt (u.transportedArea W.family.metric Phi)
      ((1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric (_root_.Set.Icc a b) t₀) z) -
        u.boundaryFlux (W.family.metric t₀) (u.isotopyVelocity Phi (_root_.Set.Icc a b) t₀ hid))
      (_root_.Set.Icc a b) t₀ := by
    have hb : HasDerivWithinAt (u.transportedArea W.family.metric Phi)
        ((1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (u.metricVariationDensity W.family.metric T t₀) z) -
          u.boundaryFlux (W.family.metric t₀) (u.isotopyVelocity Phi T t₀ hid))
        (_root_.Set.Icc a b) t₀ :=
      hDerivT.hasDerivWithinAt (s := _root_.Set.Icc a b)
    convert hb using 1
    rw [hdensInt, hvel]
  exact rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_transportedAreaDeriv
    W t₀ ht₀ gamma hgamma hemb himm hctr u sigma htrace hconformal hharmonic hmin Phi
    (hPhi.mono (Set.prod_mono Subset.rfl hTsub)) hid hboundary
    (SmoothDisk.integrableOn_diskExtension_metricVariationDensity c W ht₀ u hconformal)
    hFluxIcc hderivIcc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_of_openIsotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_of_openIsotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_of_openIsotopy ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_of_openIsotopy

theorem rfs_plateau_upper_comparison_of_minimizingSmoothDisk_of_density
    {D : RealTimeInterval} {a b : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ _root_.Set.Ioo a b)
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
    (hmin : ∀ v : SmoothDisk (I := I) (Q := Q),
      (∀ theta, v.map (diskBoundary theta) = gamma t₀ theta) →
        diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.map)
    (hdensity : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
        (∀ j theta, (w j).map (diskBoundary theta) = gamma t₀ theta) ∧
          _root_.Filter.Tendsto (fun j => diskArea (W.family.metric t₀) (w j).map) _root_.Filter.atTop
            (𝓝 (diskArea (W.family.metric t₀) v.1.map)))
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (_root_.Set.univ ×ˢ _root_.Set.Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ _root_.Set.Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta) :
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
  let c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E :=
    DifferentialGeometry.Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q :=
    DifferentialGeometry.Geometry.Topology.StandardModelCopy.compactSpace c
  exact rfs_plateau_upper_comparison_of_minimizingDiskCompetitor c W t₀ ht₀ gamma hgamma
    hemb himm hctr u sigma htrace hconformal hharmonic
    (diskArea_le_of_minimizingSmoothDisk_of_density (W.family.metric t₀) (gamma t₀) u hmin
      hdensity)
    Phi hPhi hid hboundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingSmoothDisk_of_density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingSmoothDisk_of_density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingSmoothDisk_of_density ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingSmoothDisk_of_density

theorem rfs_plateau_upper_comparison_of_minimizingSmoothDisk_of_density_of_openIsotopy
    {D : RealTimeInterval} {a b : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
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
    (hmin : ∀ v : SmoothDisk (I := I) (Q := Q),
      (∀ theta, v.map (diskBoundary theta) = gamma t₀ theta) →
        diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.map)
    (hdensity : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
        (∀ j theta, (w j).map (diskBoundary theta) = gamma t₀ theta) ∧
          _root_.Filter.Tendsto (fun j => diskArea (W.family.metric t₀) (w j).map) _root_.Filter.atTop
            (𝓝 (diskArea (W.family.metric t₀) v.1.map)))
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (T : Set ℝ) (hTopen : IsOpen T) (hTsub : _root_.Set.Icc a b ⊆ T)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (_root_.Set.univ ×ˢ T))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ _root_.Set.Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta) :
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
  let c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E :=
    DifferentialGeometry.Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q :=
    DifferentialGeometry.Geometry.Topology.StandardModelCopy.compactSpace c
  exact rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_of_openIsotopy c W t₀ ht₀
    gamma hgamma hemb himm hctr u sigma htrace hconformal hharmonic
    (diskArea_le_of_minimizingSmoothDisk_of_density (W.family.metric t₀) (gamma t₀) u hmin
      hdensity)
    Phi T hTopen hTsub hPhi hid hboundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingSmoothDisk_of_density_of_openIsotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingSmoothDisk_of_density_of_openIsotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingSmoothDisk_of_density_of_openIsotopy ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingSmoothDisk_of_density_of_openIsotopy

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

end

section

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.NNReal
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

theorem rfs_plateau_upper_comparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [hBoundary : I.Boundaryless] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [SigmaCompactSpace Q] {D : RealTimeInterval} {a b : ℝ}
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
    (hmin : ∀ v : SmoothDisk (I := I) (Q := Q),
      (∀ theta, v.map (diskBoundary theta) = gamma t₀ theta) →
        diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.map)
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (_root_.Set.univ ×ˢ _root_.Set.Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ _root_.Set.Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta) :
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
  classical
  have ht₀Icc : t₀ ∈ _root_.Set.Icc a b := ⟨ht₀.1, ht₀.2.le⟩
  have hmin' : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.1.map := by
    intro v
    have hγtsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞
        (loopLift (gamma t₀).toContinuousLoop) := by
      have h := CurveMap.space_slice_contMDiffOn
        (curveOfLoopFamily (fun v => (gamma v).toContinuousLoop)) (_root_.Set.Icc a b) hgamma t₀ ht₀Icc
      rwa [contMDiffOn_univ] at h
    obtain ⟨vj, hvj, hlim⟩ := smooth_exact_disk_density
      (W.family.metric t₀) (regularLoopSlice (fun v => (gamma v).toContinuousLoop)
        hgamma t₀ ht₀Icc) hγtsmooth v
    exact ge_of_tendsto' hlim (fun j => hmin (vj j) (hvj j))
  let c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E :=
    DifferentialGeometry.Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q :=
    DifferentialGeometry.Geometry.Topology.StandardModelCopy.compactSpace c
  obtain ⟨hint, hflux, hderiv⟩ :=
    SmoothDisk.hasDerivWithinAt_transportedArea_isotopy_flux_on_Icc c W.smooth u
      hconformal hharmonic ht₀ W.regular Phi hPhi hid
  exact rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_transportedAreaDeriv
    W t₀ ht₀ gamma hgamma hemb himm hctr u sigma htrace hconformal hharmonic hmin'
    Phi hPhi hid hboundary hint hflux hderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison


end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

end

end
