import Submission.DifferentialGeometry.Geometry.Measure.Area.ManifoldDensity
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission









noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Filter _root_.Set _root_.MeasureTheory
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem continuousOn_tangentTwoJacobian {X : Type*} [TopologicalSpace X]
    (g : SmoothRiemannianMetric I M) {b : X → M}
    {v w : ∀ x, TangentSpace I (b x)} {s : Set X}
    (hv : ContinuousOn (fun x => TotalSpace.mk' E (b x) (v x)) s)
    (hw : ContinuousOn (fun x => TotalSpace.mk' E (b x) (w x)) s) :
    ContinuousOn (fun x => tangentTwoJacobian g (v x) (w x)) s := by
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨cg.toRiemannianMetric⟩
  exact (((hv.inner_bundle hv).mul (hw.inner_bundle hw)).sub
    ((hv.inner_bundle hw).pow 2)).sqrt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.continuousOn_tangentTwoJacobian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.continuousOn_tangentTwoJacobian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.continuousOn_tangentTwoJacobian ``Submission.DifferentialGeometry.Geometry.continuousOn_tangentTwoJacobian

section Chart

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N]
  [IsManifold 𝓘(ℝ, E) ∞ N]

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_chart_derivative_apply (p : N) (v : ℂ) :
    ContinuousOn (fun q : E × (ℂ →L[ℝ] E) =>
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm q.1 (q.2 v) :
        _root_.Bundle.TotalSpace E (TangentSpace 𝓘(ℝ, E) : N → Type _)))
      (Prod.fst ⁻¹' (chartAt E p).target) := by
  have hs := (chartAt E p).open_target
  have ht := (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := p) (n := ∞)).continuousOn_tangentMapWithin
    (by simp) hs.uniqueMDiffOn
  have hv : Continuous (fun q : E × (ℂ →L[ℝ] E) =>
      (TotalSpace.mk' E q.1 (q.2 v) : TangentBundle 𝓘(ℝ, E) E)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm.continuous.comp
      (continuous_fst.prodMk (continuous_snd.clm_apply continuous_const))
  have hcomp := ht.comp hv.continuousOn (fun q hq => hq)
  apply hcomp.congr
  intro q hq
  dsimp only [Function.comp_apply, tangentMapWithin]
  rw [mfderivWithin_of_mem_nhds (hs.mem_nhds hq)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.continuousOn_chart_derivative_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.continuousOn_chart_derivative_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.continuousOn_chart_derivative_apply ``Submission.DifferentialGeometry.Geometry.continuousOn_chart_derivative_apply

theorem continuousOn_chartAreaDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    (p : N) : ContinuousOn (fun q : E × (ℂ →L[ℝ] E) => chartAreaDensity g p q.1 q.2)
      (Prod.fst ⁻¹' (chartAt E p).target) :=
  continuousOn_tangentTwoJacobian g (continuousOn_chart_derivative_apply p 1)
    (continuousOn_chart_derivative_apply p Complex.I)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.continuousOn_chartAreaDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.continuousOn_chartAreaDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.continuousOn_chartAreaDensity ``Submission.DifferentialGeometry.Geometry.continuousOn_chartAreaDensity

variable [FiniteDimensional ℝ E]

theorem measurable_riemannianAreaDensity_in_chart
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) N) {u : ℂ → N} (hu : Continuous u) (p : N) :
    Measurable (fun z : u ⁻¹' (chartAt E p).source => riemannianAreaDensity g u z) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  have hc : ContinuousOn ((chartAt E p) ∘ u) (u ⁻¹' (chartAt E p).source) :=
    (chartAt E p).continuousOn.comp hu.continuousOn (fun _ hz => hz)
  have hm : Measurable (fun z : u ⁻¹' (chartAt E p).source =>
      ((chartAt E p) (u z), fderiv ℝ ((chartAt E p) ∘ u) z)) :=
    (continuousOn_iff_continuous_domRestrict.mp hc).measurable.prodMk
      ((measurable_fderiv ℝ ((chartAt E p) ∘ u)).comp measurable_subtype_coe)
  have hmt := hm.subtype_mk
    (p := fun q : E × (ℂ →L[ℝ] E) => q.1 ∈ (chartAt E p).target)
    (h := fun z => (chartAt E p).map_source z.property)
  have hd := (continuousOn_iff_continuous_domRestrict.mp
    (continuousOn_chartAreaDensity g p)).measurable.comp hmt
  convert hd using 1
  funext z
  exact riemannianAreaDensity_eq_chart g p hu.continuousAt z.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.measurable_riemannianAreaDensity_in_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.measurable_riemannianAreaDensity_in_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.measurable_riemannianAreaDensity_in_chart ``Submission.DifferentialGeometry.Geometry.measurable_riemannianAreaDensity_in_chart




theorem measurable_riemannianAreaDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) N) {u : ℂ → N} (hu : Continuous u) :
    Measurable (riemannianAreaDensity g u) := by
  classical
  let U : ℂ → Set ℂ := fun z => u ⁻¹' (chartAt E (u z)).source
  have hU : ∀ z, IsOpen (U z) := fun z => (chartAt E (u z)).open_source.preimage hu
  have hcover : (_root_.Set.univ : Set ℂ) ⊆ ⋃ z, U z := by
    intro z _
    exact mem_iUnion.mpr ⟨z, mem_chart_source E (u z)⟩
  obtain ⟨r, hr, hrc⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  let : Countable r := hr.to_subtype
  have hrcover : ⋃ z : r, U z = univ := by
    apply _root_.Set.eq_univ_of_univ_subset
    intro z hz
    obtain ⟨w, hwr, hzw⟩ := mem_iUnion₂.mp (hrc hz)
    exact mem_iUnion.mpr ⟨⟨w, hwr⟩, hzw⟩
  let f : (z : r) → U z → ℝ := fun _ w => riemannianAreaDensity g u w
  have hf : ∀ z, Measurable (f z) := fun z =>
    measurable_riemannianAreaDensity_in_chart g hu (u z)
  have heq : ∀ (i j : r) (z : ℂ) (hi : z ∈ U i) (hj : z ∈ U j),
      f i ⟨z, hi⟩ = f j ⟨z, hj⟩ := fun _ _ _ _ _ => rfl
  have hm := measurable_liftCover (fun z : r => U z)
    (fun z => (hU z).measurableSet) f hf heq hrcover
  convert hm using 1
  funext z
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hrcover.symm ▸ _root_.Set.mem_univ z)
  exact (_root_.Set.liftCover_of_mem (S := fun z : r => U z) (f := f) hi).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.measurable_riemannianAreaDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.measurable_riemannianAreaDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.measurable_riemannianAreaDensity ``Submission.DifferentialGeometry.Geometry.measurable_riemannianAreaDensity

end Chart

end DifferentialGeometry.Geometry
