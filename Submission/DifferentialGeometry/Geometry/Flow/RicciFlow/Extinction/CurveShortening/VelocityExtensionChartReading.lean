import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.VelocityExtensionTraceCover
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.VelocityExtensionManifoldFrontier
import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem contMDiffOn_loopFamilyReading {a b : ℝ} {γ : ℝ → ContinuousFreeLoop M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b)) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) (_root_.Set.Icc a b ×ˢ _root_.Set.univ) := by
  have hswap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.2, p.1)) := contDiff_snd.prodMk contDiff_fst
  have hG : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun q : ℝ × ℝ => γ q.2 (q.1 : Surgery.Topology.Circle)) (_root_.Set.univ ×ˢ _root_.Set.Icc a b) := hγ
  have hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun p : ℝ × ℝ => (p.2, p.1)) (_root_.Set.Icc a b ×ˢ _root_.Set.univ) :=
    (contMDiffOn_univ.mpr hswap.contMDiff).mono (_root_.Set.subset_univ _)
  exact ContMDiffOn.comp hG hf fun p hp => ⟨trivial, hp.1⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.contMDiffOn_loopFamilyReading
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.contMDiffOn_loopFamilyReading target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem exists_ball_mem_chartAt {a b t₀ x₀ : ℝ} {γ : ℝ → ContinuousFreeLoop M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b)) (ht₀ : t₀ ∈ _root_.Set.Icc a b) :
    ∃ ε > 0, ∀ p : ℝ × ℝ, p ∈ _root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set ℝ) → _root_.Dist.dist p (t₀, x₀) < ε →
      γ p.1 (p.2 : Surgery.Topology.Circle)
        ∈ (chartAt H (γ t₀ (x₀ : Surgery.Topology.Circle))).source := by
  have hpre : (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) ⁻¹'
      (chartAt H (γ t₀ (x₀ : Surgery.Topology.Circle))).source
      ∈ 𝓝[_root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set ℝ)] (t₀, x₀) :=
    ((contMDiffOn_loopFamilyReading hγ).continuousOn.continuousWithinAt
        ⟨ht₀, trivial⟩).preimage_mem_nhdsWithin
      ((chartAt H (γ t₀ (x₀ : Surgery.Topology.Circle))).open_source.mem_nhds
        (mem_chart_source H _))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  exact ⟨ε, hε, fun p hp hd => hball ⟨by rwa [Metric.mem_ball], hp⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_ball_mem_chartAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_ball_mem_chartAt target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem chartReading_of_mem_Ioo {a b t₀ x₀ : ℝ}
    {γ : ℝ → ContinuousFreeLoop M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b)) (ht₀ : t₀ ∈ _root_.Set.Ioo a b) :
    LoopFamilyVelocityExtensionChartReading (I := I) γ a b t₀ x₀ := by
  set α : M := γ t₀ (x₀ : Surgery.Topology.Circle)
  have hF : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) (_root_.Set.Icc a b ×ˢ _root_.Set.univ) :=
    contMDiffOn_loopFamilyReading hγ
  have hInt : (t₀, x₀) ∈ interior (_root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set ℝ)) := by
    rw [interior_prod_eq, interior_Icc]
    exact ⟨ht₀, by simp⟩
  have hAt := hF.contMDiffAt (mem_interior_iff_mem_nhds.mp hInt)
  have hpre : (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) ⁻¹'
      (chartAt H α).source ∈ 𝓝 (t₀, x₀) :=
    hAt.continuousAt.preimage_mem_nhds
      ((chartAt H α).open_source.mem_nhds (mem_chart_source H α))
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.mp hpre
  refine ⟨fun t x => extChartAt I α (γ t (x : Surgery.Topology.Circle)),
    W ∩ (_root_.Set.Ioo a b ×ˢ _root_.Set.univ), ?_, ?_, ?_, ?_⟩
  · exact hWopen.inter (isOpen_Ioo.prod isOpen_univ)
  · exact ⟨hWmem, ht₀, trivial⟩
  · exact contDiffOn_chartReading_of_contMDiffOn (I := I)
      (hF.mono fun p hp => ⟨⟨hp.2.1.1.le, hp.2.1.2.le⟩, trivial⟩) (fun p hp => hWsub hp.1)
  · intro p hp _
    exact ⟨hWsub hp.1, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.chartReading_of_mem_Ioo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.chartReading_of_mem_Ioo target :: scope.openDecls } }

private theorem chartReading_of_leftEndpoint {a b x₀ : ℝ} {γ : ℝ → ContinuousFreeLoop M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b)) (hab : a < b) :
    LoopFamilyVelocityExtensionChartReading (I := I) γ a b a x₀ := by
  set α : M := γ a (x₀ : Surgery.Topology.Circle)
  have hF : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) (_root_.Set.Icc a b ×ˢ _root_.Set.univ) :=
    contMDiffOn_loopFamilyReading hγ
  obtain ⟨ε, hε, hbox⟩ := exists_ball_mem_chartAt (I := I) hγ ⟨le_rfl, hab.le⟩
  set ρ : ℝ := ε / 2
  set T : ℝ := _root_.Min.min (b - a) (ε / 2)
  have hρeq : ρ = ε / 2 := rfl
  have hTeq : T = _root_.Min.min (b - a) (ε / 2) := rfl
  have hρ : 0 < ρ := by rw [hρeq]; linarith
  have hT : 0 < T := by rw [hTeq]; exact lt_min (by linarith) (by linarith)
  have hTba : T ≤ b - a := by rw [hTeq]; exact min_le_left _ _
  have hTe : T ≤ ε / 2 := by rw [hTeq]; exact min_le_right _ _
  have hTb : a + T ≤ b := by linarith
  set K : Set ℝ := _root_.Set.Icc (x₀ - ρ) (x₀ + ρ)
  have hKeq : K = _root_.Set.Icc (x₀ - ρ) (x₀ + ρ) := rfl
  have hx₀K : x₀ ∈ interior K := by
    rw [hKeq, interior_Icc]
    exact ⟨by linarith, by linarith⟩
  have hsrcK : ∀ t ∈ _root_.Set.Icc a (a + T), ∀ x ∈ K,
      γ t (x : Surgery.Topology.Circle) ∈ (chartAt H α).source := by
    intro t ht x hx
    refine hbox (t, x) ⟨⟨ht.1, by linarith [ht.2, hTb]⟩, trivial⟩ ?_
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    rw [hKeq] at hx
    refine ⟨?_, ?_⟩
    · rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2, hTe]
    · rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2, hρeq]
  have hR : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => extChartAt I α (γ p.1 (p.2 : Surgery.Topology.Circle)))
      (_root_.Set.Icc a (a + T) ×ˢ K) :=
    contDiffOn_chartReading_of_contMDiffOn (I := I)
      (hF.mono fun p hp => ⟨⟨hp.1.1, by linarith [hp.1.2, hTb]⟩, trivial⟩)
      (fun p hp => hsrcK p.1 hp.1 p.2 hp.2)
  have hsh : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (a + p.1, p.2)) (_root_.Set.Icc 0 T ×ˢ K) :=
    ((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contDiffOn
  have hg : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => extChartAt I α (γ (a + p.1) (p.2 : Surgery.Topology.Circle)))
      (_root_.Set.Icc 0 T ×ˢ K) :=
    hR.comp hsh fun p hp => ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩
  obtain ⟨gext, V, hVmem, hgsm, hgeq⟩ :=
    DifferentialGeometry.Analysis.borel_interval_extend_param
      (g := fun (s : ℝ) (x : ℝ) => extChartAt I α (γ (a + s) (x : Surgery.Topology.Circle)))
      T hT K x₀ hx₀K hg
  set V₀ : Set ℝ := interior (V ∩ K)
  have hV₀eq : V₀ = interior (V ∩ K) := rfl
  have hV₀open : IsOpen V₀ := by rw [hV₀eq]; exact isOpen_interior
  have hx₀V₀ : x₀ ∈ V₀ := by
    rw [hV₀eq]
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.inter_mem hVmem (mem_interior_iff_mem_nhds.mp hx₀K))
  have hV₀V : V₀ ⊆ V := by rw [hV₀eq]; exact fun x hx => (interior_subset hx).1
  have hV₀K : V₀ ⊆ K := by rw [hV₀eq]; exact fun x hx => (interior_subset hx).2
  refine ⟨fun t x => gext (t - a) x, _root_.Set.Ioo (a - T) (a + T) ×ˢ V₀, ?_, ?_, ?_, ?_⟩
  · exact isOpen_Ioo.prod hV₀open
  · exact ⟨⟨by linarith, by linarith⟩, hx₀V₀⟩
  · have hsh' : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (p.1 - a, p.2))
        (_root_.Set.Ioo (a - T) (a + T) ×ˢ V₀) :=
      ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn
    exact hgsm.comp hsh' fun p hp => ⟨trivial, hV₀V hp.2⟩
  · intro p hp hpI
    have hp1T : p.1 < a + T := hp.1.2
    have hsub : p.1 - a ∈ _root_.Set.Icc 0 T := ⟨by linarith [hpI.1], by linarith [hp1T]⟩
    refine ⟨hsrcK p.1 ⟨hpI.1, le_of_lt hp1T⟩ p.2 (hV₀K hp.2), ?_⟩
    have heq := hgeq (p.1 - a) hsub p.2 (hV₀V hp.2)
    rw [show a + (p.1 - a) = p.1 from by ring] at heq
    exact heq

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.chartReading_of_leftEndpoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.chartReading_of_leftEndpoint target :: scope.openDecls } }

private theorem chartReading_of_rightEndpoint {a b x₀ : ℝ} {γ : ℝ → ContinuousFreeLoop M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b)) (hab : a < b) :
    LoopFamilyVelocityExtensionChartReading (I := I) γ a b b x₀ := by
  set α : M := γ b (x₀ : Surgery.Topology.Circle)
  have hF : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) (_root_.Set.Icc a b ×ˢ _root_.Set.univ) :=
    contMDiffOn_loopFamilyReading hγ
  obtain ⟨ε, hε, hbox⟩ := exists_ball_mem_chartAt (I := I) hγ ⟨hab.le, le_rfl⟩
  set ρ : ℝ := ε / 2
  set T : ℝ := _root_.Min.min (b - a) (ε / 2)
  have hρeq : ρ = ε / 2 := rfl
  have hTeq : T = _root_.Min.min (b - a) (ε / 2) := rfl
  have hρ : 0 < ρ := by rw [hρeq]; linarith
  have hT : 0 < T := by rw [hTeq]; exact lt_min (by linarith) (by linarith)
  have hTba : T ≤ b - a := by rw [hTeq]; exact min_le_left _ _
  have hTe : T ≤ ε / 2 := by rw [hTeq]; exact min_le_right _ _
  have hTa : a ≤ b - T := by linarith
  set K : Set ℝ := _root_.Set.Icc (x₀ - ρ) (x₀ + ρ)
  have hKeq : K = _root_.Set.Icc (x₀ - ρ) (x₀ + ρ) := rfl
  have hx₀K : x₀ ∈ interior K := by
    rw [hKeq, interior_Icc]
    exact ⟨by linarith, by linarith⟩
  have hsrcK : ∀ t ∈ _root_.Set.Icc (b - T) b, ∀ x ∈ K,
      γ t (x : Surgery.Topology.Circle) ∈ (chartAt H α).source := by
    intro t ht x hx
    refine hbox (t, x) ⟨⟨by linarith [ht.1, hTa], ht.2⟩, trivial⟩ ?_
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    rw [hKeq] at hx
    refine ⟨?_, ?_⟩
    · rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2, hTe]
    · rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2, hρeq]
  have hR : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => extChartAt I α (γ p.1 (p.2 : Surgery.Topology.Circle)))
      (_root_.Set.Icc (b - T) b ×ˢ K) :=
    contDiffOn_chartReading_of_contMDiffOn (I := I)
      (hF.mono fun p hp => ⟨⟨by linarith [hp.1.1, hTa], hp.1.2⟩, trivial⟩)
      (fun p hp => hsrcK p.1 hp.1 p.2 hp.2)
  have hsh : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (b - p.1, p.2)) (_root_.Set.Icc 0 T ×ˢ K) :=
    ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd).contDiffOn
  have hg : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => extChartAt I α (γ (b - p.1) (p.2 : Surgery.Topology.Circle)))
      (_root_.Set.Icc 0 T ×ˢ K) :=
    hR.comp hsh fun p hp => ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, hp.2⟩
  obtain ⟨gext, V, hVmem, hgsm, hgeq⟩ :=
    DifferentialGeometry.Analysis.borel_interval_extend_param
      (g := fun (s : ℝ) (x : ℝ) => extChartAt I α (γ (b - s) (x : Surgery.Topology.Circle)))
      T hT K x₀ hx₀K hg
  set V₀ : Set ℝ := interior (V ∩ K)
  have hV₀eq : V₀ = interior (V ∩ K) := rfl
  have hV₀open : IsOpen V₀ := by rw [hV₀eq]; exact isOpen_interior
  have hx₀V₀ : x₀ ∈ V₀ := by
    rw [hV₀eq]
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.inter_mem hVmem (mem_interior_iff_mem_nhds.mp hx₀K))
  have hV₀V : V₀ ⊆ V := by rw [hV₀eq]; exact fun x hx => (interior_subset hx).1
  have hV₀K : V₀ ⊆ K := by rw [hV₀eq]; exact fun x hx => (interior_subset hx).2
  refine ⟨fun t x => gext (b - t) x, _root_.Set.Ioo (b - T) (b + T) ×ˢ V₀, ?_, ?_, ?_, ?_⟩
  · exact isOpen_Ioo.prod hV₀open
  · exact ⟨⟨by linarith, by linarith⟩, hx₀V₀⟩
  · have hsh' : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (b - p.1, p.2))
        (_root_.Set.Ioo (b - T) (b + T) ×ˢ V₀) :=
      ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd).contDiffOn
    exact hgsm.comp hsh' fun p hp => ⟨trivial, hV₀V hp.2⟩
  · intro p hp hpI
    have hp1a : b - T < p.1 := hp.1.1
    have hsub : b - p.1 ∈ _root_.Set.Icc 0 T := ⟨by linarith [hpI.2], by linarith [hp1a]⟩
    refine ⟨hsrcK p.1 ⟨le_of_lt hp1a, hpI.2⟩ p.2 (hV₀K hp.2), ?_⟩
    have heq := hgeq (b - p.1) hsub p.2 (hV₀V hp.2)
    rw [show b - (b - p.1) = p.1 from by ring] at heq
    exact heq

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.chartReading_of_rightEndpoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.chartReading_of_rightEndpoint target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem chartReading_of_eq {a x₀ : ℝ} {γ : ℝ → ContinuousFreeLoop M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a a)) :
    LoopFamilyVelocityExtensionChartReading (I := I) γ a a a x₀ := by
  set α : M := γ a (x₀ : Surgery.Topology.Circle)
  have hslice : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x : ℝ => γ a (x : Surgery.Topology.Circle)) :=
    CurveMap.smooth_slice (curveOfLoopFamily γ) (I := I) hγ (t := a) ⟨le_rfl, le_rfl⟩
  have hpre : (fun x : ℝ => γ a (x : Surgery.Topology.Circle)) ⁻¹'
      (chartAt H α).source ∈ 𝓝 x₀ :=
    hslice.continuous.continuousAt.preimage_mem_nhds
      ((chartAt H α).open_source.mem_nhds (mem_chart_source H α))
  obtain ⟨V, hVsub, hVopen, hx₀V⟩ := mem_nhds_iff.mp hpre
  have hR : ContDiffOn ℝ ∞ (fun x : ℝ => extChartAt I α (γ a (x : Surgery.Topology.Circle)))
      V := by
    rw [← contMDiffOn_iff_contDiffOn]
    intro x hx
    refine (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
      (γ a (x : Surgery.Topology.Circle)) (hVsub hx)).comp x ?_ fun y hy => hVsub hy
    exact hslice.contMDiffAt.contMDiffWithinAt.mono (_root_.Set.subset_univ V)
  refine ⟨fun _ x => extChartAt I α (γ a (x : Surgery.Topology.Circle)),
    _root_.Set.univ ×ˢ V, ?_, ?_, ?_, ?_⟩
  · exact isOpen_univ.prod hVopen
  · exact ⟨trivial, hx₀V⟩
  · exact hR.comp contDiffOn_snd fun p hp => hp.2
  · intro p hp hpI
    have hp1 : p.1 = a := le_antisymm hpI.2 hpI.1
    refine ⟨?_, ?_⟩
    · rw [hp1]; exact hVsub hp.2
    · rw [hp1]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.chartReading_of_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.chartReading_of_eq target :: scope.openDecls } }

theorem loopFamilyVelocityExtensionChartReading_of_smoothOn {a b t₀ x₀ : ℝ}
    {γ : ℝ → ContinuousFreeLoop M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b)) (ht₀ : t₀ ∈ _root_.Set.Icc a b) :
    LoopFamilyVelocityExtensionChartReading (I := I) γ a b t₀ x₀ := by
  rcases lt_or_ge a b with hab | hba
  · rcases eq_or_lt_of_le ht₀.1 with h | h
    · rw [h.symm]
      exact chartReading_of_leftEndpoint (I := I) hγ hab
    · rcases eq_or_lt_of_le ht₀.2 with h2 | h2
      · rw [h2]
        exact chartReading_of_rightEndpoint (I := I) hγ hab
      · exact chartReading_of_mem_Ioo (I := I) hγ ⟨h, h2⟩
  · have hta : t₀ = a := le_antisymm (le_trans ht₀.2 hba) ht₀.1
    have hba' : b = a := le_antisymm hba (le_trans ht₀.1 ht₀.2)
    subst hba'
    subst hta
    exact chartReading_of_eq (I := I) hγ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionChartReading_of_smoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionChartReading_of_smoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionChartReading_of_smoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionChartReading_of_smoothOn

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem smoothOn_constLoopFamily (m : M) (a b : ℝ) :
    (curveOfLoopFamily (fun _ : ℝ => constantLoops m)).SmoothOn (I := I) (_root_.Set.Icc a b) :=
  contMDiffOn_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothOn_constLoopFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothOn_constLoopFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothOn_constLoopFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.smoothOn_constLoopFamily

variable [T2Space M]

theorem loopFamilyVelocityExtensionLocalCover_of_smoothOn {a b : ℝ}
    {γ : ℝ → ContinuousFreeLoop M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a b))
    (hemb : ∀ t ∈ _root_.Set.Icc a b, Topology.IsEmbedding (γ t)) :
    LoopFamilyVelocityExtensionLocalCover (I := I) γ a b :=
  loopFamilyVelocityExtensionLocalCover_of_chartReading (I := I) hγ hi hemb
    fun _ ht _ => loopFamilyVelocityExtensionChartReading_of_smoothOn (I := I) hγ ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionLocalCover_of_smoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionLocalCover_of_smoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionLocalCover_of_smoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionLocalCover_of_smoothOn

variable [SigmaCompactSpace M]

theorem loopFamilyVelocityExtension_of_smoothOn {a b : ℝ} {γ : ℝ → ContinuousFreeLoop M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a b))
    (hemb : ∀ t ∈ _root_.Set.Icc a b, Topology.IsEmbedding (γ t)) :
    LoopFamilyVelocityExtension (I := I) a b γ :=
  loopFamilyVelocityExtension_of_chartReading (I := I) hγ hi hemb
    fun _ ht _ => loopFamilyVelocityExtensionChartReading_of_smoothOn (I := I) hγ ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_of_smoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_of_smoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_of_smoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_of_smoothOn

variable [hBoundary : I.Boundaryless] [hCompact : CompactSpace M] [hNonempty : Nonempty M]

omit hBoundary hCompact hNonempty in
theorem loopFamilyVelocityExtensionProducer_holds (a b : ℝ) :
    LoopFamilyVelocityExtensionProducer (I := I) (M := M) a b :=
  fun _ hγ hi hemb => loopFamilyVelocityExtension_of_smoothOn (I := I) hγ hi hemb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionProducer_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionProducer_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionProducer_holds ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionProducer_holds

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
