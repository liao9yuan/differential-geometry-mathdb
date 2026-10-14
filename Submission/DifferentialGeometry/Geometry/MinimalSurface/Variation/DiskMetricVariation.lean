import Submission.DifferentialGeometry.Geometry.Measure.Area.ConformalMetricDerivative
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient
import Submission.DifferentialGeometry.Geometry.Metric.FamilySectionPairing
import Submission.DifferentialGeometry.Geometry.Metric.ParameterDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




def diskMapMetricVariationDensity (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (t : ℝ) (U : ℂ → M) (z : ℂ) : ℝ :=
  (deriv (fun r => (G r).inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1)) t +
    deriv (fun r => (G r).inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) t) / 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapMetricVariationDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapMetricVariationDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapMetricVariationDensity ``Submission.DifferentialGeometry.Geometry.diskMapMetricVariationDensity



theorem contDiffOn_metricFamilyDiskPairing
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {T : Set ℝ} (hT : IsOpen T) (hTD : T ⊆ D.regular)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) (v w : ℂ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℂ =>
      (G q.1).inner (U q.2) (diskMapPartial U q.2 v) (diskMapPartial U q.2 w)) (T ×ˢ s) := by
  intro q hq
  have hUz := (hU q.2 hq.2).contMDiffAt (hs.mem_nhds hq.2)
  have hV (a : ℂ) := ((contMDiffOn_source_partial hs hU (m := ∞) (by simp) a) q.2 hq.2).contMDiffAt
    (hs.mem_nhds hq.2)
  have h := contMDiffAt_metricFamilySectionPairing hG contMDiffAt_fst
    (hUz.comp q contMDiffAt_snd) (Filter.mem_of_superset (hT.mem_nhds hq.1) hTD)
    ((hV v).comp q contMDiffAt_snd) ((hV w).comp q contMDiffAt_snd)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffAt.contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contDiffOn_metricFamilyDiskPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contDiffOn_metricFamilyDiskPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contDiffOn_metricFamilyDiskPairing ``Submission.DifferentialGeometry.Geometry.contDiffOn_metricFamilyDiskPairing




theorem hasDerivAt_diskMapAreaDensity_metric
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {U : ℂ → M} {z : ℂ} (hconf : DiskMapConformalAt (G t) U z) :
    HasDerivAt (fun r => riemannianAreaDensity (G r) U z) (diskMapMetricVariationDensity G t U z) t := by
  have hpair (v w : TangentSpace 𝓘(ℝ, E) (U z)) :=
    (((hG.coeff (U z) v w).contDiffAt ht).differentiableAt (by simp)).hasDerivAt
  exact hasDerivAt_tangentTwoJacobian_at_conformal (hpair _ _) (hpair _ _) (hpair _ _) hconf.1 hconf.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasDerivAt_diskMapAreaDensity_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasDerivAt_diskMapAreaDensity_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasDerivAt_diskMapAreaDensity_metric ``Submission.DifferentialGeometry.Geometry.hasDerivAt_diskMapAreaDensity_metric



theorem contDiffOn_diskMapMetricVariationDensity
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) :
    ContDiffOn ℝ ∞ (diskMapMetricVariationDensity G t U) s := by
  intro z hz
  have hp (v w : ℂ) : ContDiffAt ℝ ∞
      (fun q : ℝ × ℂ => (G q.1).inner (U q.2) (diskMapPartial U q.2 v) (diskMapPartial U q.2 w)) (t, z) :=
    ((contDiffOn_metricFamilyDiskPairing hG D.regular_isOpen Subset.rfl hs hU v w)
      (t, z) ⟨mem_of_mem_nhds ht, hz⟩).contDiffAt
        ((D.regular_isOpen.prod hs).mem_nhds ⟨mem_of_mem_nhds ht, hz⟩)
  have hd (v w : ℂ) := (contDiffAt_deriv_fst (hp v w)).comp z
    (contDiffAt_const.prodMk contDiffAt_id)
  exact ((hd 1 1).add (hd Complex.I Complex.I)).div_const 2 |>.contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contDiffOn_diskMapMetricVariationDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contDiffOn_diskMapMetricVariationDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contDiffOn_diskMapMetricVariationDensity ``Submission.DifferentialGeometry.Geometry.contDiffOn_diskMapMetricVariationDensity

end DifferentialGeometry.Geometry

end

section

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def diskMapMetricVariationWithinDensity (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (T : Set ℝ) (t : ℝ) (U : ℂ → M) (z : ℂ) : ℝ :=
  (derivWithin (fun r => (G r).inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1)) T t +
    derivWithin (fun r => (G r).inner (U z) (diskMapPartial U z Complex.I)
      (diskMapPartial U z Complex.I)) T t) / 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapMetricVariationWithinDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapMetricVariationWithinDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapMetricVariationWithinDensity ``Submission.DifferentialGeometry.Geometry.diskMapMetricVariationWithinDensity

theorem contDiffOn_diskMapMetricVariationWithinDensity
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ _root_.Set.Icc a b)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => (G q.1).inner q.2.proj q.2.2 q.2.2)
      (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) :
    ContDiffOn ℝ ∞ (diskMapMetricVariationWithinDensity G (_root_.Set.Icc a b) t₀ U) s := by
  have hd := contMDiffOn_derivWithin_fst (uniqueDiffOn_Icc hab) hG
  have hpair (v : ℂ) : ContDiffOn ℝ ∞
      (fun z => derivWithin (fun r => (G r).inner (U z) (diskMapPartial U z v)
        (diskMapPartial U z v)) (_root_.Set.Icc a b) t₀) s := by
    have hm : ContMDiffOn 𝓘(ℝ, ℂ)
        (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) ∞
        (fun z : ℂ => (t₀, TotalSpace.mk' E (U z) (diskMapPartial U z v))) s :=
      contMDiffOn_const.prodMk (contMDiffOn_source_partial hs hU (m := ∞) (by simp) v)
    have h := hd.comp (f := fun z : ℂ => (t₀, TotalSpace.mk' E (U z) (diskMapPartial U z v)))
      hm (fun _ _ => ⟨ht₀, _root_.Set.mem_univ _⟩)
    exact h.contDiffOn
  exact ((hpair 1).add (hpair Complex.I)).div_const 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contDiffOn_diskMapMetricVariationWithinDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contDiffOn_diskMapMetricVariationWithinDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contDiffOn_diskMapMetricVariationWithinDensity ``Submission.DifferentialGeometry.Geometry.contDiffOn_diskMapMetricVariationWithinDensity


private theorem differentiableWithinAt_metric_inner_of_quadratic
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {T : Set ℝ} {t₀ : ℝ}
    {x : M} (hdiag : ∀ v : TangentSpace 𝓘(ℝ, E) x,
      DifferentiableWithinAt ℝ (fun t => (G t).inner x v v) T t₀)
    (v w : TangentSpace 𝓘(ℝ, E) x) :
    DifferentiableWithinAt ℝ (fun t => (G t).inner x v w) T t₀ := by
  have hpolar : (fun t => (G t).inner x v w) =
      (fun t => (1 / 4 : ℝ) *
        ((G t).inner x (v + w) (v + w) - (G t).inner x (v - w) (v - w))) := by
    funext t
    simp only [map_add, map_sub, add_apply, sub_apply,
      (G t).symm x w v]
    ring
  rw [hpolar]
  exact (hdiag (v + w)).sub (hdiag (v - w)) |>.const_mul (1 / 4 : ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.differentiableWithinAt_metric_inner_of_quadratic
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.differentiableWithinAt_metric_inner_of_quadratic target :: scope.openDecls } }


theorem hasDerivWithinAt_diskMapAreaDensity_metric_on_Icc
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ _root_.Set.Icc a b)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => (G q.1).inner q.2.proj q.2.2 q.2.2)
      (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    {U : ℂ → M} {z : ℂ} (hconf : DiskMapConformalAt (G t₀) U z) :
    HasDerivWithinAt (fun r => riemannianAreaDensity (G r) U z)
      (diskMapMetricVariationWithinDensity G (_root_.Set.Icc a b) t₀ U z) (_root_.Set.Icc a b) t₀ := by
  have hdiag (v : TangentSpace 𝓘(ℝ, E) (U z)) :
      DifferentiableWithinAt ℝ (fun t => (G t).inner (U z) v v) (_root_.Set.Icc a b) t₀ := by
    have hc := (hG (t₀, TotalSpace.mk' E (U z) v) ⟨ht₀, _root_.Set.mem_univ _⟩).comp
      (f := fun r : ℝ => (r, TotalSpace.mk' E (U z) v)) t₀
      (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const)
      (fun r hr => ⟨hr, _root_.Set.mem_univ _⟩)
    exact hc.contDiffWithinAt.differentiableWithinAt (by simp)
  have hpair (v w : TangentSpace 𝓘(ℝ, E) (U z)) :=
    (differentiableWithinAt_metric_inner_of_quadratic hdiag v w).hasDerivWithinAt
  exact hasDerivWithinAt_tangentTwoJacobian_at_conformal (uniqueDiffOn_Icc hab t₀ ht₀)
    (hpair _ _) (hpair _ _) (hpair _ _) hconf.1 hconf.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasDerivWithinAt_diskMapAreaDensity_metric_on_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasDerivWithinAt_diskMapAreaDensity_metric_on_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasDerivWithinAt_diskMapAreaDensity_metric_on_Icc ``Submission.DifferentialGeometry.Geometry.hasDerivWithinAt_diskMapAreaDensity_metric_on_Icc


end DifferentialGeometry.Geometry

end

end
