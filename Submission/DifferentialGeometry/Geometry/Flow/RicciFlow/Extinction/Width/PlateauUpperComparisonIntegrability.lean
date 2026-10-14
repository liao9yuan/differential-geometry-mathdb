import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonAttainment
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskAreaMetricFirstVariation

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem derivWithin_Icc_eq_deriv_of_mem_Ico {F : ℝ → ℝ} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ _root_.Set.Ico a b) (hd : DifferentiableAt ℝ F t₀) :
    derivWithin F (_root_.Set.Icc a b) t₀ = deriv F t₀ := by
  have hset : _root_.Set.Icc a b = _root_.Set.Ici a ∩ _root_.Set.Iic b := by
    ext x
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [hset]
  rw [derivWithin_inter (s := Set.Ici a) (t := Set.Iic b) (Iic_mem_nhds ht₀.2)]
  by_cases h : a < t₀
  · exact derivWithin_of_mem_nhds (Ici_mem_nhds h)
  · have hta : t₀ = a := le_antisymm (not_lt.mp h) ht₀.1
    have hd' : DifferentiableAt ℝ F a := hta ▸ hd
    rw [hta]
    exact hd'.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.derivWithin_Icc_eq_deriv_of_mem_Ico then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.derivWithin_Icc_eq_deriv_of_mem_Ico"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.derivWithin_Icc_eq_deriv_of_mem_Ico ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.derivWithin_Icc_eq_deriv_of_mem_Ico

variable [hT2 : T2Space Q] [hCompact : CompactSpace Q] [hSigma : SigmaCompactSpace Q]
  [hBoundary : I.Boundaryless]

theorem SmoothDisk.integrableOn_diskExtension_metricVariationDensity
    (c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E) [CompactSpace c.Q]
    {D : RealTimeInterval} {a b t₀ : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (ht₀ : t₀ ∈ _root_.Set.Ico a b) (u : SmoothDisk (I := I) (Q := Q))
    (hconf : u.IsConformal (W.family.metric t₀)) :
    _root_.MeasureTheory.IntegrableOn (diskExtension (u.metricVariationDensity W.family.metric (_root_.Set.Icc a b) t₀))
      (Metric.closedBall (0 : ℂ) 1) := by
  have hreg : D.regular ∈ 𝓝 t₀ :=
    D.regular_isOpen.mem_nhds (W.regular ⟨ht₀.1, ht₀.2.le⟩)
  have hInt : _root_.MeasureTheory.IntegrableOn
      (diskExtension (u.metricVariationDensity W.family.metric D.regular t₀))
      (Metric.closedBall (0 : ℂ) 1) :=
    (SmoothDisk.hasDerivAt_diskArea_metricFamily (I := I) (Q := Q) (hG := W.smooth)
      c u W.family.metric D.regular hreg hreg hconf).1
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
  have hdens (z : Disk) : u.metricVariationDensity W.family.metric D.regular t₀ z =
      u.metricVariationDensity W.family.metric (_root_.Set.Icc a b) t₀ z := by
    simp only [SmoothDisk.metricVariationDensity]
    split_ifs with hpos
    · rw [derivWithin_of_mem_nhds hreg, derivWithin_of_mem_nhds hreg,
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀ (hdiff₁ z),
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀ (hdiff₂ z)]
    · rfl
  refine hInt.congr_fun ?_ measurableSet_closedBall
  intro z hz
  rw [show diskExtension (u.metricVariationDensity W.family.metric D.regular t₀) z =
      u.metricVariationDensity W.family.metric D.regular t₀ ⟨z, hz⟩ from dif_pos hz,
    show diskExtension (u.metricVariationDensity W.family.metric (_root_.Set.Icc a b) t₀) z =
      u.metricVariationDensity W.family.metric (_root_.Set.Icc a b) t₀ ⟨z, hz⟩ from dif_pos hz]
  exact hdens ⟨z, hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.integrableOn_diskExtension_metricVariationDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.integrableOn_diskExtension_metricVariationDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.integrableOn_diskExtension_metricVariationDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.integrableOn_diskExtension_metricVariationDensity

theorem rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_boundaryFlux
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
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (_root_.Set.univ ×ˢ _root_.Set.Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ _root_.Set.Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta)
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
            variation + epsilon :=
  rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_transportedAreaDeriv
    W t₀ ht₀ gamma hgamma hemb himm hctr u sigma htrace hconformal hharmonic hmin Phi hPhi hid
    hboundary (SmoothDisk.integrableOn_diskExtension_metricVariationDensity c W ht₀ u hconformal)
    hintFlux hderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_boundaryFlux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_boundaryFlux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_boundaryFlux ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_boundaryFlux

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
