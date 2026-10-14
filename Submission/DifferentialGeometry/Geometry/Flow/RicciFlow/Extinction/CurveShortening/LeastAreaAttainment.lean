import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.MinimalDiskAreaVariation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Plateau

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.NNReal _root_.ENNReal
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  {D : RealTimeInterval} {a b : ℝ}

theorem diskArea_eq_leastArea_of_minimizingSmoothDisk
    (g : SmoothRiemannianMetric I M) (γ : Width.RegularLoop I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (Width.loopLift γ.toContinuousLoop))
    (hctr : IsContractibleLoop γ.toContinuousLoop)
    (u : Width.SmoothDisk (I := I) (Q := M)) (σ : Width.SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ θ : Surgery.Topology.Circle,
      u.map (Width.diskBoundary θ) = γ.toContinuousLoop (σ.map θ))
    (hmin : ∀ v : Width.SmoothDisk (I := I) (Q := M),
      (∀ θ : Surgery.Topology.Circle, v.map (Width.diskBoundary θ) = γ.toContinuousLoop θ) →
        Width.diskArea g u.map ≤ Width.diskArea g v.map)
    (hdensity : ∀ v : Width.DiskCompetitor g γ.toContinuousLoop,
      ∃ w : ℕ → Width.SmoothDisk (I := I) (Q := M),
        (∀ j θ, (w j).map (Width.diskBoundary θ) = γ.toContinuousLoop θ) ∧
          _root_.Filter.Tendsto (fun j => Width.diskArea g (w j).map) _root_.Filter.atTop
            (𝓝 (Width.diskArea g v.1.map))) :
    Width.diskArea g u.map =
      Width.leastArea g γ.toContinuousLoop hctr (γ.isLipschitz g) := by
  apply le_antisymm
  · apply le_csInf (Width.competitorAreas_nonempty g γ.toContinuousLoop hctr (γ.isLipschitz g))
    rintro _ ⟨v, rfl⟩
    obtain ⟨w, htracew, hlim⟩ := hdensity v
    exact ge_of_tendsto' hlim (fun j => hmin (w j) (htracew j))
  · obtain ⟨ulip, hulip⟩ := u.exists_lipschitz g
    have htracelip : ∀ θ, ulip.map (Width.diskBoundary θ) =
        γ.toContinuousLoop (σ.map θ) := by
      simpa only [hulip] using htrace
    obtain ⟨v, hv⟩ := Width.zero_area_trace_annulus g γ hγ σ ulip htracelip
    have hle := Width.leastArea_le_competitor g γ.toContinuousLoop hctr (γ.isLipschitz g) v
    simpa only [hv, hulip] using hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.diskArea_eq_leastArea_of_minimizingSmoothDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.diskArea_eq_leastArea_of_minimizingSmoothDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.diskArea_eq_leastArea_of_minimizingSmoothDisk ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.diskArea_eq_leastArea_of_minimizingSmoothDisk

theorem exists_diskCompetitor_diskArea_eq_leastArea_of_minimizingSmoothDisk
    (g : SmoothRiemannianMetric I M) (γ : Width.RegularLoop I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (Width.loopLift γ.toContinuousLoop))
    (hctr : IsContractibleLoop γ.toContinuousLoop)
    (u : Width.SmoothDisk (I := I) (Q := M)) (σ : Width.SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ θ : Surgery.Topology.Circle,
      u.map (Width.diskBoundary θ) = γ.toContinuousLoop (σ.map θ))
    (hmin : ∀ v : Width.SmoothDisk (I := I) (Q := M),
      (∀ θ : Surgery.Topology.Circle, v.map (Width.diskBoundary θ) = γ.toContinuousLoop θ) →
        Width.diskArea g u.map ≤ Width.diskArea g v.map)
    (hdensity : ∀ v : Width.DiskCompetitor g γ.toContinuousLoop,
      ∃ w : ℕ → Width.SmoothDisk (I := I) (Q := M),
        (∀ j θ, (w j).map (Width.diskBoundary θ) = γ.toContinuousLoop θ) ∧
          _root_.Filter.Tendsto (fun j => Width.diskArea g (w j).map) _root_.Filter.atTop
            (𝓝 (Width.diskArea g v.1.map))) :
    ∃ w : Width.DiskCompetitor g γ.toContinuousLoop,
      Width.diskArea g w.1.map =
        Width.leastArea g γ.toContinuousLoop hctr (γ.isLipschitz g) := by
  have hA := diskArea_eq_leastArea_of_minimizingSmoothDisk g γ hγ hctr u σ htrace hmin hdensity
  obtain ⟨ulip, hulip⟩ := u.exists_lipschitz g
  have htracelip : ∀ θ, ulip.map (Width.diskBoundary θ) =
      γ.toContinuousLoop (σ.map θ) := by
    simpa only [hulip] using htrace
  obtain ⟨v, hv⟩ := Width.zero_area_trace_annulus g γ hγ σ ulip htracelip
  exact ⟨v, by rw [hv, hulip]; exact hA⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_diskCompetitor_diskArea_eq_leastArea_of_minimizingSmoothDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_diskCompetitor_diskArea_eq_leastArea_of_minimizingSmoothDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_diskCompetitor_diskArea_eq_leastArea_of_minimizingSmoothDisk ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_diskCompetitor_diskArea_eq_leastArea_of_minimizingSmoothDisk

theorem exists_diskCompetitor_diskArea_eq_loopFamilyLeastArea
    (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hctr : ∀ t ∈ _root_.Set.Icc a b, IsContractibleLoop (γ t))
    (hslice : ∀ t ∈ _root_.Set.Ico a b, ∃ (u : Width.SmoothDisk (I := I) (Q := M))
        (σ : Width.SmoothWeaklyMonotoneCircleMap),
      (∀ θ : Surgery.Topology.Circle, u.map (Width.diskBoundary θ) = γ t (σ.map θ)) ∧
      ∀ v : Width.SmoothDisk (I := I) (Q := M),
        (∀ θ : Surgery.Topology.Circle, v.map (Width.diskBoundary θ) = γ t θ) →
          Width.diskArea (B.family.metric t) u.map ≤
            Width.diskArea (B.family.metric t) v.map)
    (hdensity : ∀ t ∈ _root_.Set.Ico a b, ∀ v : Width.DiskCompetitor (B.family.metric t) (γ t),
      ∃ w : ℕ → Width.SmoothDisk (I := I) (Q := M),
        (∀ j θ, (w j).map (Width.diskBoundary θ) = γ t θ) ∧
          _root_.Filter.Tendsto (fun j => Width.diskArea (B.family.metric t) (w j).map) _root_.Filter.atTop
            (𝓝 (Width.diskArea (B.family.metric t) v.1.map))) :
    ∀ t ∈ _root_.Set.Ico a b, ∃ u : Width.DiskCompetitor (B.family.metric t) (γ t),
      Width.diskArea (B.family.metric t) u.1.map = loopFamilyLeastArea B.family.metric γ t := by
  intro t ht
  have htIcc : t ∈ _root_.Set.Icc a b := ⟨ht.1, ht.2.le⟩
  obtain ⟨u, σ, htrace, hmin⟩ := hslice t ht
  have hγt := (curveOfLoopFamily γ).smooth_slice hγ htIcc
  obtain ⟨w, hw⟩ := exists_diskCompetitor_diskArea_eq_leastArea_of_minimizingSmoothDisk
    (g := B.family.metric t) (γ := regularLoopSlice γ hγ t htIcc) hγt
    (hctr t htIcc) u σ htrace hmin (hdensity t ht)
  refine ⟨w, ?_⟩
  rw [loopFamilyLeastArea_eq_regularLeastAreaSlice B.family.metric γ hγ hctr t htIcc]
  exact hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_diskCompetitor_diskArea_eq_loopFamilyLeastArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_diskCompetitor_diskArea_eq_loopFamilyLeastArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_diskCompetitor_diskArea_eq_loopFamilyLeastArea ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_diskCompetitor_diskArea_eq_loopFamilyLeastArea

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
