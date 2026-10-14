import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Curve.C1Gluing
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.Function _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

theorem curve_c1_join {gamma : Real → M} {a c b : Real}
    (hac : a < c) (hcb : c < b)
    (hl : ContMDiffOn 𝓘(Real, Real) I 1 gamma (_root_.Set.Icc a c))
    (hr : ContMDiffOn 𝓘(Real, Real) I 1 gamma (_root_.Set.Icc c b))
    (hder :
      derivWithin ((extChartAt I (gamma c)) ∘ gamma) (_root_.Set.Icc a c) c =
        derivWithin ((extChartAt I (gamma c)) ∘ gamma) (_root_.Set.Icc c b) c) :
    ContMDiffOn 𝓘(Real, Real) I 1 gamma (_root_.Set.Icc a b) := by
  let phi : Real → E := (extChartAt I (gamma c)) ∘ gamma
  have hpreL : gamma ⁻¹' (chartAt H (gamma c)).source ∈ 𝓝[_root_.Set.Icc a c] c :=
    (hl.continuousOn c ⟨hac.le, le_rfl⟩)
      ((chartAt H (gamma c)).open_source.mem_nhds
        (mem_chart_source H (gamma c)))
  rw [nhdsWithin_Icc_eq_nhdsLE hac] at hpreL
  have hinterL : gamma ⁻¹' (chartAt H (gamma c)).source ∩ _root_.Set.Icc a c ∈ 𝓝[≤] c :=
    _root_.Filter.inter_mem hpreL (Icc_mem_nhdsLE hac)
  obtain ⟨d, hdc, hdsub⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp hinterL
  have hsrcL : _root_.Set.MapsTo gamma (_root_.Set.Icc d c) (chartAt H (gamma c)).source :=
    fun x hx ↦ (hdsub hx).1
  have hsubL : _root_.Set.Icc d c ⊆ _root_.Set.Icc a c := fun x hx ↦ (hdsub hx).2
  have hpreR : gamma ⁻¹' (chartAt H (gamma c)).source ∈ 𝓝[_root_.Set.Icc c b] c :=
    (hr.continuousOn c ⟨le_rfl, hcb.le⟩)
      ((chartAt H (gamma c)).open_source.mem_nhds
        (mem_chart_source H (gamma c)))
  rw [nhdsWithin_Icc_eq_nhdsGE hcb] at hpreR
  have hinterR : gamma ⁻¹' (chartAt H (gamma c)).source ∩ _root_.Set.Icc c b ∈ 𝓝[≥] c :=
    _root_.Filter.inter_mem hpreR (Icc_mem_nhdsGE hcb)
  obtain ⟨e, hce, hesum⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hinterR
  have hsrcR : _root_.Set.MapsTo gamma (_root_.Set.Icc c e) (chartAt H (gamma c)).source :=
    fun x hx ↦ (hesum hx).1
  have hsubR : _root_.Set.Icc c e ⊆ _root_.Set.Icc c b := fun x hx ↦ (hesum hx).2
  have hphiL : ContDiffOn Real 1 phi (_root_.Set.Icc d c) := by
    have hchart :=
      ((contMDiffOn_iff_target.mp (hl.mono hsubL)).2 (gamma c)).mono
        (fun x hx ↦ ⟨hx, by
          rw [extChartAt_source]
          exact hsrcL hx⟩)
    exact (by simpa only [phi] using hchart.contDiffOn)
  have hphiR : ContDiffOn Real 1 phi (_root_.Set.Icc c e) := by
    have hchart :=
      ((contMDiffOn_iff_target.mp (hr.mono hsubR)).2 (gamma c)).mono
        (fun x hx ↦ ⟨hx, by
          rw [extChartAt_source]
          exact hsrcR hx⟩)
    exact (by simpa only [phi] using hchart.contDiffOn)
  have hsetL : _root_.Set.Icc d c =ᶠ[𝓝 c] _root_.Set.Icc a c := by
    filter_upwards [Ioi_mem_nhds hdc] with x hx
    apply propext
    constructor
    · intro h
      exact hsubL h
    · intro h
      exact ⟨hx.le, h.2⟩
  have hsetR : _root_.Set.Icc c e =ᶠ[𝓝 c] _root_.Set.Icc c b := by
    filter_upwards [Iio_mem_nhds hce] with x hx
    apply propext
    constructor
    · intro h
      exact hsubR h
    · intro h
      exact ⟨h.1, hx.le⟩
  have hder' : derivWithin phi (_root_.Set.Icc d c) c = derivWithin phi (_root_.Set.Icc c e) c := by
    rw [derivWithin_congr_set hsetL, derivWithin_congr_set hsetR]
    exact hder
  have hphi : ContDiffOn Real 1 phi (_root_.Set.Icc d e) :=
    contDiffOn_Icc_join hdc hce hphiL hphiR hder'
  have hcont : ContinuousOn gamma (_root_.Set.Icc a b) := by
    rw [← _root_.Set.Icc_union_Icc_eq_Icc hac.le hcb.le]
    exact hl.continuousOn.union_of_isClosed hr.continuousOn
      isClosed_Icc isClosed_Icc
  intro x hx
  rcases lt_trichotomy x c with hxc | hxc | hcx
  · apply (hl x ⟨hx.1, hxc.le⟩).mono_of_mem_nhdsWithin
    apply _root_.Filter.mem_of_superset (inter_mem_nhdsWithin (_root_.Set.Icc a b) (Iio_mem_nhds hxc))
    intro y hy
    exact ⟨hy.1.1, hy.2.le⟩
  · subst x
    apply contMDiffWithinAt_iff_target.mpr
    refine ⟨hcont c ⟨hac.le, hcb.le⟩, ?_⟩
    have hc : c ∈ _root_.Set.Icc d e := ⟨hdc.le, hce.le⟩
    have hsmall : ContMDiffWithinAt 𝓘(Real, Real) 𝓘(Real, E) 1 phi
        (_root_.Set.Icc d e) c := (hphi c hc).contMDiffWithinAt
    apply hsmall.mono_of_mem_nhdsWithin
    apply _root_.Filter.mem_of_superset (inter_mem_nhdsWithin (_root_.Set.Icc a b) (Ioo_mem_nhds hdc hce))
    intro y hy
    exact ⟨hy.2.1.le, hy.2.2.le⟩
  · apply (hr x ⟨hcx.le, hx.2⟩).mono_of_mem_nhdsWithin
    apply _root_.Filter.mem_of_superset (inter_mem_nhdsWithin (_root_.Set.Icc a b) (Ioi_mem_nhds hcx))
    intro y hy
    exact ⟨hy.2.le, hy.1.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_c1_join then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_c1_join"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_c1_join ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_c1_join

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry

end
