import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.TwoPieceSplicing
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.Existence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.ActionContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Approximation.Ramp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Interval

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] in
private theorem rampUp_add {L : Real} (hL : 0 < L) (z w : E) :
    timeH1.rampUp L (z + w) = timeH1.rampUp L z + timeH1.rampUp L w := by
  apply timeH1.ext
  · rw [← timeH1.toFun_zero (timeH1.rampUp L (z + w)),
      timeH1.initial_add,
      ← timeH1.toFun_zero (timeH1.rampUp L z),
      ← timeH1.toFun_zero (timeH1.rampUp L w),
      timeH1.rampUp_zero hL, timeH1.rampUp_zero hL,
      timeH1.rampUp_zero hL, add_zero]
  · rw [timeH1.deriv_add]
    apply Lp.ext
    filter_upwards [timeH1.rampUp_deriv hL (z + w),
      timeH1.rampUp_deriv hL z, timeH1.rampUp_deriv hL w,
      Lp.coeFn_add (timeH1.rampUp L z).deriv
        (timeH1.rampUp L w).deriv] with s hzw hz hw hadd
    rw [hzw, hadd, Pi.add_apply, hz, hw, smul_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.rampUp_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.rampUp_add target :: scope.openDecls } }

private def rampUpLM (L : Real) (hL : 0 < L) :
    E →ₗ[Real] timeH1 E L where
  toFun := timeH1.rampUp L
  map_add' := rampUp_add hL
  map_smul' := timeH1.rampUp_smul hL

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.rampUpLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.rampUpLM target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] in
private theorem rampUp_tendsto {L : Real} (hL : 0 < L)
    {z : Nat → E} {z₀ : E} (hz : _root_.Filter.Tendsto z _root_.Filter.atTop (nhds z₀)) :
    _root_.Filter.Tendsto (fun n ↦ timeH1.rampUp L (z n)) _root_.Filter.atTop
      (nhds (timeH1.rampUp L z₀)) := by
  exact (LinearMap.continuous_of_finiteDimensional (rampUpLM L hL)).continuousAt.tendsto.comp hz

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.rampUp_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.rampUp_tendsto target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] in
omit [FiniteDimensional ℝ E] in
private theorem h1_uniform {L : Real}
    (v : Nat → timeH1 E L) (u : timeH1 E L)
    (hv : _root_.Filter.Tendsto v _root_.Filter.atTop (nhds u)) :
    TendstoUniformly
      (fun n (r : _root_.Set.Icc (0 : Real) L) ↦ (v n).toFun r.1)
      (fun r ↦ u.toFun r.1) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let C : Real := 1 + Real.sqrt L
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hsub : _root_.Filter.Tendsto (fun n ↦ u - v n) _root_.Filter.atTop (nhds 0) := by
    simpa only [sub_self] using (tendsto_const_nhds.sub hv :
      _root_.Filter.Tendsto (fun n ↦ u - v n) _root_.Filter.atTop (nhds (u - u)))
  have hnorm : _root_.Filter.Tendsto (fun n ↦ ‖u - v n‖) _root_.Filter.atTop (nhds 0) := by
    have hn := continuous_norm.tendsto (0 : timeH1 E L) |>.comp hsub
    convert hn using 1
    · rfl
    · simp only [norm_zero]
  have hsmall : ∀ᶠ n in _root_.Filter.atTop, ‖u - v n‖ < ε / C :=
    hnorm.eventually (Iio_mem_nhds (div_pos hε hC))
  filter_upwards [hsmall] with n hn
  intro r
  have hfun : (u - v n).toFun r.1 = u.toFun r.1 - (v n).toFun r.1 := by
    rw [sub_eq_add_neg, timeH1.toFun_add u (-v n) r.2]
    have hneg := timeH1.toFun_smul (-1 : Real) (v n) r.2
    simpa only [neg_one_smul, sub_eq_add_neg] using
      congrArg (u.toFun r.1 + ·) hneg
  rw [dist_eq_norm, ← hfun]
  calc
    ‖(u - v n).toFun r.1‖ ≤ C * ‖u - v n‖ :=
      (u - v n).norm_toFun_le_norm r.2
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hn hC
    _ = ε := by field_simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.h1_uniform
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.h1_uniform target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] in
omit [FiniteDimensional ℝ E] in
private theorem timeH1_toFun_cast {a b : Real} (h : a = b)
    (w : timeH1 E b) :
    (h.symm ▸ w : timeH1 E a).toFun = w.toFun := by
  subst b
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.timeH1_toFun_cast
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.timeH1_toFun_cast target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem timeH1_tendsto_cast {a b : Real} (h : a = b)
    (w : Nat → timeH1 E b) (w0 : timeH1 E b)
    (hw : _root_.Filter.Tendsto w _root_.Filter.atTop (nhds w0)) :
    Tendsto (fun n ↦ h.symm ▸ w n) _root_.Filter.atTop (nhds (h.symm ▸ w0)) := by
  subst b
  exact hw

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.timeH1_tendsto_cast
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.timeH1_tendsto_cast target :: scope.openDecls } }

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
private theorem eventually_mem_buf
    {A : Type*} (f : A → E) (v : Nat → A → E) (K : Set E)
    (hfc : IsCompact (_root_.Set.range f)) (hfK : ∀ r, f r ∈ interior K)
    (hv : TendstoUniformly v f _root_.Filter.atTop) :
    ∀ᶠ n in _root_.Filter.atTop, ∀ r, v n r ∈ K := by
  obtain ⟨δ, hδ, hthick⟩ :=
    hfc.exists_thickening_subset_open isOpen_interior (by
      rintro _ ⟨r, rfl⟩
      exact hfK r)
  have hclose := (Metric.tendstoUniformly_iff.mp hv) δ hδ
  filter_upwards [hclose] with n hn
  intro r
  apply interior_subset
  apply hthick
  exact Metric.mem_thickening_iff.mpr
    ⟨f r, _root_.Set.mem_range_self r, by simpa only [dist_comm] using hn r⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.eventually_mem_buf
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.eventually_mem_buf target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [T2Space M] in
omit [CompactSpace M] in
private theorem chart_tail_lim
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T c b : Real) (hcb : c < b) (p : M) (gamma : Real → M)
    (u0 : timeH1 E (b - c))
    (hsrc0 : _root_.Set.MapsTo gamma (_root_.Set.Icc c b) (chartAt H p).source)
    (hrep0 : _root_.Set.EqOn u0.toFun
      (fun r ↦ extChartAt I p (gamma (c + r))) (_root_.Set.Icc (0 : Real) (b - c)))
    (z : Nat → E) (hz : _root_.Filter.Tendsto z _root_.Filter.atTop (nhds 0))
    (K : Set E) (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I p).target)
    (hK : ∀ n (r : _root_.Set.Icc (0 : Real) (b - c)),
      (u0 + timeH1.rampUp (b - c) (z n)).toFun r.1 ∈ K)
    (hK0 : ∀ r : _root_.Set.Icc (0 : Real) (b - c), u0.toFun r.1 ∈ K)
    (hreg : ∀ s ∈ _root_.Set.Icc c b, T - s ^ 2 ∈ D.regular) :
    _root_.Filter.Tendsto
      (fun n ↦ lRegularizedAction S T
        (fun s ↦ (extChartAt I p).symm
          ((u0 + timeH1.rampUp (b - c) (z n)).toFun (s - c))) c b)
      atTop (nhds (lRegularizedAction S T gamma c b)) := by
  let v : Nat → timeH1 E (b - c) := fun n ↦
    u0 + timeH1.rampUp (b - c) (z n)
  let beta : Nat → Real → M := fun n s ↦
    (extChartAt I p).symm ((v n).toFun (s - c))
  let beta0 : Real → M := fun s ↦ (extChartAt I p).symm (u0.toFun (s - c))
  have hL : 0 < b - c := sub_pos.mpr hcb
  have hv : _root_.Filter.Tendsto v _root_.Filter.atTop (nhds u0) := by
    have hr := rampUp_tendsto (E := E) hL hz
    have hr0 : timeH1.rampUp (b - c) (0 : E) = 0 := by
      simpa only [zero_smul] using
        timeH1.rampUp_smul hL (0 : Real) (0 : E)
    simpa only [v, hr0, add_zero] using
      tendsto_const_nhds.add hr
  have hcoord := h1_uniform v u0 hv
  have hsymm : UniformContinuousOn (extChartAt I p).symm K :=
    hKc.uniformContinuousOn_of_continuous <|
      (continuousOn_extChartAt_symm p).mono (hKchart.trans interior_subset)
  have huniform : TendstoUniformly
      (fun n (s : _root_.Set.Icc c b) ↦ beta n s.1)
      (fun s ↦ beta0 s.1) atTop := by
    have hshift : _root_.Set.MapsTo (fun s : _root_.Set.Icc c b ↦ s.1 - c)
        univ (_root_.Set.Icc (0 : Real) (b - c)) := by
      intro s _
      exact ⟨sub_nonneg.mpr s.2.1, sub_le_sub_right s.2.2 c⟩
    have hc := hcoord.comp (fun s : _root_.Set.Icc c b ↦
      ⟨s.1 - c, hshift (_root_.Set.mem_univ s)⟩)
    apply UniformContinuousOn.comp_tendstoUniformly
      (s := K) (F := fun n (s : _root_.Set.Icc c b) ↦
        (v n).toFun (s.1 - c)) (f := fun s ↦ u0.toFun (s.1 - c))
    · exact fun n s ↦ hK n ⟨s.1 - c, hshift (_root_.Set.mem_univ s)⟩
    · exact fun s ↦ hK0 ⟨s.1 - c, hshift (_root_.Set.mem_univ s)⟩
    · exact hsymm
    · convert hc using 1 <;> rfl
  have hcont (n : Nat) : ContinuousOn (beta n) (_root_.Set.Icc c b) := by
    have hcoordCont : ContinuousOn (fun s ↦ (v n).toFun (s - c))
        (_root_.Set.Icc c b) :=
      (v n).continuousOn_toFun.comp (continuous_sub_right c).continuousOn
        (fun s hs ↦ ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩)
    exact (continuousOn_extChartAt_symm p).comp
      hcoordCont
      (fun s hs ↦ interior_subset (hKchart (hK n ⟨s - c,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩⟩)))
  have hsrc (n : Nat) : _root_.Set.MapsTo (beta n) (_root_.Set.Icc c b) (chartAt H p).source := by
    intro s hs
    rw [← extChartAt_source (I := I) p]
    exact (extChartAt I p).map_target
      (interior_subset (hKchart (hK n ⟨s - c,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩⟩)))
  have hrep (n : Nat) : _root_.Set.EqOn (v n).toFun
      (fun r ↦ extChartAt I p (beta n (c + r)))
      (_root_.Set.Icc (0 : Real) (b - c)) := by
    intro r hr
    simp only [beta, add_sub_cancel_left]
    exact ((extChartAt I p).right_inv
      (interior_subset (hKchart (hK n ⟨r, hr⟩)))).symm
  have hsrcLim : _root_.Set.MapsTo beta0 (_root_.Set.Icc c b) (chartAt H p).source := by
    intro s hs
    rw [← extChartAt_source (I := I) p]
    exact (extChartAt I p).map_target
      (interior_subset (hKchart (hK0 ⟨s - c,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩⟩)))
  have hrepLim : _root_.Set.EqOn u0.toFun
      (fun r ↦ extChartAt I p (beta0 (c + r)))
      (_root_.Set.Icc (0 : Real) (b - c)) := by
    intro r hr
    simp only [beta0, add_sub_cancel_left]
    exact ((extChartAt I p).right_inv
      (interior_subset (hKchart (hK0 ⟨r, hr⟩)))).symm
  let t : Fin 2 → Real :=
    Fin.cases c (Fin.cases b fun k ↦ Fin.elim0 k)
  have ht0 : t 0 = c := rfl
  have ht1 : t (Fin.last 1) = b := rfl
  have htLen : partitionIntervalLength t 0 = b - c := rfl
  have htmono : Monotone t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [t, hcb.le]
  let vt (n : Nat) : timeH1 E (partitionIntervalLength t 0) := htLen.symm ▸ v n
  let u0t : timeH1 E (partitionIntervalLength t 0) := htLen.symm ▸ u0
  let vtFin : (i : Fin 1) → Nat → timeH1 E (partitionIntervalLength t i) :=
    Fin.cases vt fun k ↦ Fin.elim0 k
  let u0Fin : (i : Fin 1) → timeH1 E (partitionIntervalLength t i) :=
    Fin.cases u0t fun k ↦ Fin.elim0 k
  have hlim := lAction_h1_lim (I := I) S hMet hSc T c b t htmono
    ht0 ht1 (fun _ ↦ p) beta beta0
    vtFin u0Fin
    (fun i n ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change _root_.Set.MapsTo (beta n) (_root_.Set.Icc c b) (chartAt H p).source
      exact hsrc n)
    (fun i n ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      intro r hr
      have hr' : r ∈ _root_.Set.Icc (0 : Real) (b - c) := by
        rw [← htLen]
        exact hr
      change (vt n).toFun r = extChartAt I p (beta n (t 0 + r))
      rw [timeH1_toFun_cast htLen (v n), ht0]
      exact hrep n hr')
    (fun i ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change _root_.Set.MapsTo beta0 (_root_.Set.Icc c b) (chartAt H p).source
      exact hsrcLim)
    (fun i ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      intro r hr
      have hr' : r ∈ _root_.Set.Icc (0 : Real) (b - c) := by
        rw [← htLen]
        exact hr
      change u0t.toFun r = extChartAt I p (beta0 (t 0 + r))
      rw [timeH1_toFun_cast htLen u0, ht0]
      exact hrepLim hr')
    (fun _ ↦ K) (fun _ ↦ hKc) (fun _ ↦ hKchart)
    (fun i n r ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hrmem : r.val ∈ _root_.Set.Icc (0 : Real) (b - c) := by
        rw [← htLen]
        exact r.property
      let r' : _root_.Set.Icc (0 : Real) (b - c) := ⟨r.val, hrmem⟩
      change (vt n).toFun r.1 ∈ K
      rw [timeH1_toFun_cast htLen (v n)]
      have hk := hK n r'
      change (v n).toFun r'.1 ∈ K at hk
      have hrval : (r' : Real) = (r : Real) := by
        rfl
      rw [hrval] at hk
      exact hk)
    (fun i r ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hrmem : r.val ∈ _root_.Set.Icc (0 : Real) (b - c) := by
        rw [← htLen]
        exact r.property
      let r' : _root_.Set.Icc (0 : Real) (b - c) := ⟨r.val, hrmem⟩
      change u0t.toFun r.1 ∈ K
      rw [timeH1_toFun_cast htLen u0]
      have hk := hK0 r'
      have hrval : (r' : Real) = (r : Real) := by
        rfl
      rw [hrval] at hk
      exact hk)
    (fun i ↦ by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change _root_.Filter.Tendsto vt _root_.Filter.atTop (nhds u0t)
      exact timeH1_tendsto_cast htLen v u0 hv)
    hcont huniform hreg
  have heq : _root_.Set.EqOn beta0 gamma (_root_.Set.Icc c b) := by
    intro s hs
    apply (extChartAt I p).injOn
    · simpa only [extChartAt_source] using hsrcLim hs
    · rw [extChartAt_source]
      exact hsrc0 hs
    · calc
        extChartAt I p (beta0 s) = u0.toFun (s - c) :=
          (extChartAt I p).right_inv (interior_subset (hKchart
            (hK0 ⟨s - c,
              ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩⟩)))
        _ = extChartAt I p (gamma (c + (s - c))) :=
          hrep0 ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩
        _ = extChartAt I p (gamma s) := by
          congr 2
          ring
  have heqAct : lRegularizedAction S T beta0 c b = lRegularizedAction S T gamma c b :=
    lRegularizedAction_congr (I := I) S T beta0 gamma c b
      (by
        have heq' : _root_.Set.EqOn beta0 gamma (_root_.Set.uIcc c b) := by
          simpa only [_root_.Set.uIcc_of_le hcb.le] using heq
        exact heq'.mono _root_.Set.uIoo_subset_uIcc_self)
  rw [heqAct] at hlim
  simpa only [beta, v] using hlim

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.chart_tail_lim
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.chart_tail_lim target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] in
theorem lCost_lt_event
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t0 t1 tau : Real) (htau : 0 < tau)
    (htime : _root_.Set.Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ _root_.Set.Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ _root_.Set.Icc t0 t1)
    (x y : M) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha)
    (h0 : alpha 0 = x) (hend : alpha (Real.sqrt tau) = y)
    (hreg : ∀ s ∈ _root_.Set.Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ D.regular)
    (A : Real) (hA : lRegularizedAction S T alpha 0 (Real.sqrt tau) < A)
    (q : Nat → M) (hq : _root_.Filter.Tendsto q _root_.Filter.atTop (nhds y)) :
    ∀ᶠ n in _root_.Filter.atTop, lCost S T x (q n) tau < A := by
  classical
  let b : Real := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hySource : y ∈ (chartAt H y).source := mem_chart_source H y
  have hpre : alpha ⁻¹' (chartAt H y).source ∈ 𝓝[≤] b := by
    apply mem_nhdsWithin_of_mem_nhds
    apply halpha.continuous.continuousAt.preimage_mem_nhds
    exact (chartAt H y).open_source.mem_nhds (by simpa only [b, hend] using hySource)
  obtain ⟨c0, hc0b, hc0src⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp hpre
  let c : Real := _root_.Max.max c0 (b / 2)
  have hc : 0 < c := lt_of_lt_of_le (half_pos hb) (le_max_right _ _)
  have hcb : c < b := by
    exact max_lt hc0b (half_lt_self hb)
  have hsrcTail : _root_.Set.MapsTo alpha (_root_.Set.Icc c b) (chartAt H y).source := by
    intro s hs
    exact hc0src ⟨(le_max_left _ _).trans hs.1, hs.2⟩
  let gamma : Real → M := fun r ↦ alpha (c + r)
  have hshift : _root_.Set.MapsTo (fun r : Real ↦ c + r) (_root_.Set.Icc (0 : Real) (b - c))
      (_root_.Set.Icc c b) := by
    intro r hr
    exact ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  have hgamma : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (_root_.Set.Icc (0 : Real) (b - c)) := by
    exact halpha.comp (contDiff_const.add contDiff_id).contMDiff |>.contMDiffOn
  have hgammaSource : _root_.Set.MapsTo gamma (_root_.Set.Icc (0 : Real) (b - c))
      (chartAt H y).source := fun r hr ↦ hsrcTail (hshift hr)
  let u0 : timeH1 E (b - c) :=
    chartTimeH1 I (sub_nonneg.mpr hcb.le) y gamma hgamma hgammaSource
  have hrep0 : _root_.Set.EqOn u0.toFun
      (fun r ↦ extChartAt I y (alpha (c + r)))
      (_root_.Set.Icc (0 : Real) (b - c)) := by
    intro r hr
    change u0.toFun r = ((extChartAt I y) ∘ gamma) r
    exact chartTimeH1_toFun I (sub_nonneg.mpr hcb.le) y gamma hgamma
      hgammaSource hr
  have htar0 (r : _root_.Set.Icc (0 : Real) (b - c)) :
      u0.toFun r.1 ∈ (extChartAt I y).target := by
    rw [hrep0 r.2]
    exact (extChartAt I y).map_source (by
      rw [extChartAt_source]
      exact hgammaSource r.2)
  obtain ⟨K, hKc, _hKclosed, hintoK, hKtar⟩ :=
    exists_compact_closed_between
      (isCompact_Icc.image_of_continuousOn u0.continuousOn_toFun)
      (isOpen_extChartAt_target (I := I) y)
      (by rintro _ ⟨r, hr, rfl⟩; exact htar0 ⟨r, hr⟩)
  have hKchart : K ⊆ interior (extChartAt I y).target := by
    simpa only [(isOpen_extChartAt_target (I := I) y).interior_eq] using hKtar
  have hK0 (r : _root_.Set.Icc (0 : Real) (b - c)) : u0.toFun r.1 ∈ K :=
    interior_subset (hintoK ⟨r.1, r.2, rfl⟩)
  have hqSource : ∀ᶠ n in _root_.Filter.atTop, q n ∈ (chartAt H y).source :=
    hq.eventually ((chartAt H y).open_source.mem_nhds hySource)
  let z : Nat → E := fun n ↦ extChartAt I y (q n) - extChartAt I y y
  have hz : _root_.Filter.Tendsto z _root_.Filter.atTop (nhds 0) := by
    have hcq := (continuousAt_extChartAt (I := I) y).tendsto.comp hq
    have hcst : _root_.Filter.Tendsto (fun _ : Nat ↦ extChartAt I y y) _root_.Filter.atTop
        (nhds (extChartAt I y y)) := tendsto_const_nhds
    simpa only [z, Function.comp_apply, sub_self] using hcq.sub hcst
  let v : Nat → timeH1 E (b - c) := fun n ↦
    u0 + timeH1.rampUp (b - c) (z n)
  have hv : _root_.Filter.Tendsto v _root_.Filter.atTop (nhds u0) := by
    have hr := rampUp_tendsto (E := E) (sub_pos.mpr hcb) hz
    have hr0 : timeH1.rampUp (b - c) (0 : E) = 0 := by
      simpa only [zero_smul] using
        timeH1.rampUp_smul (sub_pos.mpr hcb) (0 : Real) (0 : E)
    simpa only [v, hr0, add_zero] using tendsto_const_nhds.add hr
  have hcoord := h1_uniform v u0 hv
  have hu0Range : IsCompact
      (_root_.Set.range fun r : _root_.Set.Icc (0 : Real) (b - c) ↦ u0.toFun r.1) := by
    rw [← _root_.Set.image_univ]
    exact isCompact_univ.image_of_continuousOn
      (u0.continuousOn_toFun.comp continuous_subtype_val.continuousOn
        (fun _ _ ↦ Subtype.property _))
  have hvK : ∀ᶠ n in _root_.Filter.atTop, ∀ r : _root_.Set.Icc (0 : Real) (b - c),
      (v n).toFun r.1 ∈ K :=
    eventually_mem_buf (fun r : _root_.Set.Icc (0 : Real) (b - c) ↦ u0.toFun r.1)
      (fun n r ↦ (v n).toFun r.1) K
      hu0Range
      (fun r ↦ hintoK ⟨r.1, r.2, rfl⟩) hcoord
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (hqSource.and hvK))
  let q' : Nat → M := fun n ↦ q (n + N)
  let z' : Nat → E := fun n ↦ z (n + N)
  let v' : Nat → timeH1 E (b - c) := fun n ↦ v (n + N)
  have hq'Source (n : Nat) : q' n ∈ (chartAt H y).source := (hN _ (Nat.le_add_left N n)).1
  have hz' : _root_.Filter.Tendsto z' _root_.Filter.atTop (nhds 0) := hz.comp (_root_.Filter.tendsto_add_atTop_nat N)
  have hv' (n : Nat) : v' n = u0 + timeH1.rampUp (b - c) (z' n) := rfl
  have hv'K (n : Nat) (r : _root_.Set.Icc (0 : Real) (b - c)) :
      (u0 + timeH1.rampUp (b - c) (z' n)).toFun r.1 ∈ K := by
    simpa only [v', v, z'] using (hN _ (Nat.le_add_left N n)).2 r
  let beta : Nat → Real → M := fun n s ↦
    (extChartAt I y).symm
      ((u0 + timeH1.rampUp (b - c) (z' n)).toFun (s - c))
  have htailLim : _root_.Filter.Tendsto (fun n ↦ lRegularizedAction S T (beta n) c b) _root_.Filter.atTop
      (nhds (lRegularizedAction S T alpha c b)) := by
    apply chart_tail_lim (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩ T c b hcb y
      alpha u0 hsrcTail hrep0 z' hz' K hKc hKchart hv'K hK0
    intro s hs
    exact hreg s ⟨hc.le.trans hs.1, by simpa only [b] using hs.2⟩
  have hu0c1 : ContDiffOn Real 1 u0.toFun (_root_.Set.Icc (0 : Real) (b - c)) := by
    exact (chartCoord_contDiff I y gamma hgamma hgammaSource).congr
      (fun r hr ↦ by simpa only [gamma, Function.comp_apply] using hrep0 hr)
  have hbetaC1 (n : Nat) : ContMDiffOn
      (modelWithCornersSelf Real Real) I 1 (beta n) (_root_.Set.Icc c b) := by
    have hvC1 : ContDiffOn Real 1
        (u0 + timeH1.rampUp (b - c) (z' n)).toFun
        (_root_.Set.Icc (0 : Real) (b - c)) := by
      apply (hu0c1.add
        (((contDiff_id.div_const (b - c)).smul_const (z' n)).contDiffOn)).congr
      intro r hr
      rw [timeH1.toFun_add _ _ hr,
        timeH1.rampUp_apply (sub_nonneg.mpr hcb.le) (z' n) hr]
      simp only [id_eq]
    apply curve_c1_local I y (beta n)
      (u0 + timeH1.rampUp (b - c) (z' n))
    · intro s hs
      rw [← extChartAt_source (I := I) y]
      exact (extChartAt I y).map_target
        (interior_subset (hKchart (hv'K n ⟨s - c,
          ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩⟩)))
    · intro r hr
      simp only [beta, add_sub_cancel_left]
      exact ((extChartAt I y).right_inv
        (interior_subset (hKchart (hv'K n ⟨r, hr⟩)))).symm
    · exact hvC1
  have hbetaSource (n : Nat) : _root_.Set.MapsTo (beta n) (_root_.Set.Icc c b)
      (chartAt H y).source := by
    intro s hs
    rw [← extChartAt_source (I := I) y]
    exact (extChartAt I y).map_target
      (interior_subset (hKchart (hv'K n ⟨s - c,
        ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩⟩)))
  have hbetaC (n : Nat) : beta n c = alpha c := by
    apply (extChartAt I y).injOn
    · simpa only [extChartAt_source] using hbetaSource n ⟨le_rfl, hcb.le⟩
    · rw [extChartAt_source]
      exact hsrcTail ⟨le_rfl, hcb.le⟩
    · simp only [beta, sub_self]
      have hv0 : (u0 + timeH1.rampUp (b - c) (z' n)).toFun 0 =
          u0.toFun 0 := by
        rw [timeH1.toFun_add _ _ ⟨le_rfl, sub_nonneg.mpr hcb.le⟩,
          timeH1.rampUp_zero (sub_pos.mpr hcb), add_zero]
      have hright0 : extChartAt I y ((extChartAt I y).symm (u0.toFun 0)) =
          u0.toFun 0 := (extChartAt I y).right_inv
        (interior_subset (hKchart (hK0
          ⟨0, ⟨le_rfl, sub_nonneg.mpr hcb.le⟩⟩)))
      rw [hv0, hright0]
      calc
        u0.toFun 0 = extChartAt I y (alpha (c + 0)) :=
          hrep0 ⟨le_rfl, sub_nonneg.mpr hcb.le⟩
        _ = extChartAt I y (alpha c) := by rw [add_zero]
  have hbetaB (n : Nat) : beta n b = q' n := by
    apply (extChartAt I y).injOn
    · rw [extChartAt_source]
      rw [← extChartAt_source (I := I) y]
      exact (extChartAt I y).map_target
        (interior_subset (hKchart (hv'K n ⟨b - c,
          ⟨sub_nonneg.mpr hcb.le, le_rfl⟩⟩)))
    · rw [extChartAt_source]
      exact hq'Source n
    · have hrightB : extChartAt I y (beta n b) =
          (u0 + timeH1.rampUp (b - c) (z' n)).toFun (b - c) := by
        exact (extChartAt I y).right_inv
          (interior_subset (hKchart (hv'K n ⟨b - c,
            ⟨sub_nonneg.mpr hcb.le, le_rfl⟩⟩)))
      have hu0b : u0.toFun (b - c) = extChartAt I y y := by
        calc
          u0.toFun (b - c) = extChartAt I y (alpha (c + (b - c))) :=
            hrep0 ⟨sub_nonneg.mpr hcb.le, le_rfl⟩
          _ = extChartAt I y y := by
            rw [show c + (b - c) = b by ring,
              show b = Real.sqrt tau by rfl, hend]
      rw [hrightB, timeH1.toFun_add _ _
          ⟨sub_nonneg.mpr hcb.le, le_rfl⟩,
        timeH1.rampUp_end (sub_pos.mpr hcb), hu0b]
      simp only [z', z, q', add_sub_cancel]
  have hreg0c : ∀ s ∈ _root_.Set.Icc (0 : Real) c, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hs.1, hs.2.trans hcb.le⟩
  have hregcb : ∀ s ∈ _root_.Set.Icc c b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hc.le.trans hs.1, by simpa only [b] using hs.2⟩
  have hheadInt := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
    T 0 c hc.le alpha halpha.contMDiffOn hreg0c
  have htailInt := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
    T c b hcb.le alpha halpha.contMDiffOn hregcb
  have halphaAdd := lRegularizedAction_add (I := I) S T alpha 0 c b hheadInt htailInt
  have hpiece : _root_.Filter.Tendsto
      (fun n ↦ lRegularizedAction S T alpha 0 c + lRegularizedAction S T (beta n) c b)
      atTop (nhds (lRegularizedAction S T alpha 0 b)) := by
    have hsum : _root_.Filter.Tendsto
        (fun n ↦ lRegularizedAction S T alpha 0 c + lRegularizedAction S T (beta n) c b)
        _root_.Filter.atTop (nhds
          (lRegularizedAction S T alpha 0 c + lRegularizedAction S T alpha c b)) :=
      tendsto_const_nhds.add htailLim
    rw [halphaAdd] at hsum
    exact hsum
  have hsmall : ∀ᶠ n in _root_.Filter.atTop,
      lRegularizedAction S T alpha 0 c + lRegularizedAction S T (beta n) c b < A :=
    hpiece.eventually (Iio_mem_nhds (by simpa only [b] using hA))
  have hcost' : ∀ᶠ n in _root_.Filter.atTop, lCost S T x (q' n) tau < A := by
    filter_upwards [hsmall] with n hn
    obtain ⟨eta, m, t, p, w, heta0, heta1, htmono, ht0, htlast,
        _hcnode, hsrc, hrep⟩ :=
      exists_chartH1_join (I := I) 0 c b hc hcb alpha (beta n)
        halpha.contMDiffOn (hbetaC1 n) (hbetaC n).symm
    obtain ⟨delta, _u, hdelta, hdelta0, hdeltab, _hsrcDelta, _hrepDelta,
        _hu, _huniform, hdeltaAct⟩ :=
      lAction_c1_dense (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
        T 0 b t htmono ht0 htlast p eta w hsrc hrep
        (fun s hs ↦ hreg s (by simpa only [b] using hs))
    have hetaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
        (_root_.Set.Icc (0 : Real) c) := halpha.contMDiffOn.congr fun s hs ↦ heta0 hs
    have hetaTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
        (_root_.Set.Icc c b) := (hbetaC1 n).congr fun s hs ↦ heta1 hs
    have hetaHeadInt := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ T 0 c hc.le eta hetaHead hreg0c
    have hetaTailInt := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ T c b hcb.le eta hetaTail hregcb
    have hetaAdd := lRegularizedAction_add (I := I) S T eta 0 c b
      hetaHeadInt hetaTailInt
    have hetaHeadAct : lRegularizedAction S T eta 0 c = lRegularizedAction S T alpha 0 c :=
      lRegularizedAction_congr (I := I) S T eta alpha 0 c (by
        intro s hs
        have hs' : s ∈ _root_.Set.Ioo (0 : Real) c := by
          simpa only [_root_.Set.uIoo_of_le hc.le] using hs
        exact heta0 ⟨hs'.1.le, hs'.2.le⟩)
    have hetaTailAct : lRegularizedAction S T eta c b = lRegularizedAction S T (beta n) c b :=
      lRegularizedAction_congr (I := I) S T eta (beta n) c b (by
        intro s hs
        have hs' : s ∈ _root_.Set.Ioo c b := by
          simpa only [_root_.Set.uIoo_of_le hcb.le] using hs
        exact heta1 ⟨hs'.1.le, hs'.2.le⟩)
    have hetaLt : lRegularizedAction S T eta 0 b < A := by
      rw [← hetaAdd, hetaHeadAct, hetaTailAct]
      exact hn
    have hdeltaSmall : ∀ᶠ k in _root_.Filter.atTop, lRegularizedAction S T (delta k) 0 b < A :=
      hdeltaAct.eventually (Iio_mem_nhds hetaLt)
    obtain ⟨k, hk⟩ := hdeltaSmall.exists
    rw [lCost_eq_regularity (I := I) S T x (q' n) tau htau.le]
    exact lt_of_le_of_lt
      (lRegularizedCostC1_le (I := I) S hS T t0 t1 0 b hb.le
        htime (by simpa only [b] using hback) x (q' n) (delta k) (hdelta k)
        ((hdelta0 k).trans ((heta0 ⟨le_rfl, hc.le⟩).trans h0))
        ((hdeltab k).trans
          ((heta1 ⟨hcb.le, le_rfl⟩).trans (hbetaB n)))
        (by simpa only [b] using hreg)) hk
  rw [← _root_.Filter.map_add_atTop_eq_nat N]
  change ∀ᶠ n in _root_.Filter.atTop, lCost S T x (q (n + N)) tau < A
  exact hcost'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_lt_event then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_lt_event"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_lt_event ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_lt_event

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lCost_le_ray
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (b : Real)
    (hb0 : 0 < b) (hb : b ∈ lRegularizedDomain S T x Z) :
    lCost S T x (lRegularizedCurve S T x Z b) (b ^ 2) ≤
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 b := by
  obtain ⟨rho, hrho, hrho_id, _hrho_deriv, hrho_range⟩ :=
    exists_lRegularizedDomain_smoothClamp S T x Z hb0 hb
  let z : E := Z
  let gamma : Real → M := fun s ↦ lRegularizedCurve S T x Z (rho s)
  have hrhoM : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  have hpair : ContMDiff (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) ∞
      (fun s : Real ↦ (z, rho s)) :=
    contMDiff_const.prodMk hrhoM
  have hgammaInf : ContMDiff (modelWithCornersSelf Real Real) I ∞ gamma := by
    rw [← contMDiffOn_univ]
    change ContMDiffOn (modelWithCornersSelf Real Real) I ∞
      (fun s ↦ lRegularizedCurve S T x Z (rho s)) _root_.Set.univ
    exact (lRegularizedCurve_smoothOn S hS T x).comp hpair.contMDiffOn
      (fun s _hs ↦ by
        change rho s ∈ lRegularizedDomain S T x Z
        exact hrho_range s)
  have hgamma : ContMDiff (modelWithCornersSelf Real Real) I 1 gamma :=
    hgammaInf.of_le (by norm_num)
  have heq : Set.EqOn gamma (lRegularizedCurve S T x Z) (_root_.Set.Icc (0 : Real) b) := by
    intro s hs
    exact congrArg (lRegularizedCurve S T x Z) (hrho_id hs)
  have hreg : ∀ s ∈ _root_.Set.Icc (0 : Real) b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact lRegularizedDomain_regularity S T x Z
      (lRegularizedDomain_segment S T x Z hb hs.1 hs.2)
  have htime : _root_.Set.Icc (T - b ^ 2) T ⊆ D.carrier := by
    intro r hr
    have hnonneg : 0 ≤ T - r := by linarith [hr.2]
    have hle : T - r ≤ b ^ 2 := by linarith [hr.1]
    have hsqrt : Real.sqrt (T - r) ∈ _root_.Set.Icc (0 : Real) b := by
      refine ⟨Real.sqrt_nonneg _, ?_⟩
      calc
        Real.sqrt (T - r) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hle
        _ = b := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hb0]
    have hregR := hreg (Real.sqrt (T - r)) hsqrt
    have heqR : T - (Real.sqrt (T - r)) ^ 2 = r := by
      rw [Real.sq_sqrt hnonneg]
      ring
    exact D.regular_subset (by simpa only [heqR] using hregR)
  have hback : ∀ s ∈ _root_.Set.Icc (0 : Real) b,
      T - s ^ 2 ∈ _root_.Set.Icc (T - b ^ 2) T := by
    intro s hs
    have hsq : s ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hs.1 hb0.le).2 hs.2
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  have hact : lRegularizedAction S T gamma 0 b =
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 b := by
    apply lRegularizedAction_congr (I := I) S T gamma (lRegularizedCurve S T x Z) 0 b
    intro s hs
    apply heq
    have hs' : s ∈ _root_.Set.Ioo (0 : Real) b := by
      simpa only [_root_.Set.uIoo_of_le hb0.le] using hs
    exact ⟨hs'.1.le, hs'.2.le⟩
  have hrho0 : rho 0 = 0 := by
    simpa only [id_eq] using hrho_id ⟨le_rfl, hb0.le⟩
  have hrhob : rho b = b := by
    simpa only [id_eq] using hrho_id ⟨hb0.le, le_rfl⟩
  rw [lCost_eq_regularity (I := I) S T x (lRegularizedCurve S T x Z b)
      (b ^ 2) (sq_nonneg b), Real.sqrt_sq_eq_abs, abs_of_pos hb0]
  calc
    lRegularizedCostC1 S T 0 b x (lRegularizedCurve S T x Z b) ≤
        lRegularizedAction S T gamma 0 b :=
      lRegularizedCostC1_le (I := I) S hS T (T - b ^ 2) T 0 b hb0.le
        htime hback x (lRegularizedCurve S T x Z b) gamma hgamma
        (by simp only [gamma, hrho0, lRegularizedCurve_zero])
        (by simp only [gamma, hrhob]) hreg
    _ = lRegularizedAction S T (lRegularizedCurve S T x Z) 0 b := hact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_le_ray then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_le_ray"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_le_ray ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_le_ray

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lCost_ray_event
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : Nat → TangentSpace I x}
    {Z₀ : TangentSpace I x} {tau : Nat → Real} {tau₀ : Real}
    (htau₀ : 0 < tau₀)
    (hdom : Real.sqrt tau₀ ∈ lRegularizedDomain S T x Z₀)
    (hZ : _root_.Filter.Tendsto Z _root_.Filter.atTop (nhds Z₀))
    (htau : _root_.Filter.Tendsto tau _root_.Filter.atTop (nhds tau₀))
    (A : Real)
    (hA : lRegularizedAction S T (lRegularizedCurve S T x Z₀) 0
      (Real.sqrt tau₀) < A) :
    ∀ᶠ n in _root_.Filter.atTop, lCost S T x (lExp S T x (Z n) (tau n)) (tau n) < A := by
  have hsqrt : _root_.Filter.Tendsto (fun n ↦ Real.sqrt (tau n)) _root_.Filter.atTop
      (nhds (Real.sqrt tau₀)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp htau
  have hsqrt0 : 0 < Real.sqrt tau₀ := Real.sqrt_pos.2 htau₀
  have hjoint : _root_.Filter.Tendsto (fun n ↦ ((Z n : E), Real.sqrt (tau n))) _root_.Filter.atTop
      (nhds ((Z₀ : E), Real.sqrt tau₀)) := hZ.prodMk_nhds hsqrt
  have hmem : ∀ᶠ n in _root_.Filter.atTop,
      Real.sqrt (tau n) ∈ lRegularizedDomain S T x (Z n) := by
    exact hjoint.eventually
      ((lRegularizedJointDom_open S hS T x).mem_nhds (by
        change Real.sqrt tau₀ ∈ lRegularizedDomain S T x Z₀
        exact hdom))
  have hpos : ∀ᶠ n in _root_.Filter.atTop, 0 < tau n :=
    htau.eventually (Ioi_mem_nhds htau₀)
  have hact := (continuousAt_lRegularizedAction_lRegularizedCurve (I := I)
    S hS T x hsqrt0 hdom).tendsto.comp (hZ.prodMk_nhds hsqrt)
  have hactLt : ∀ᶠ n in _root_.Filter.atTop,
      lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0
        (Real.sqrt (tau n)) < A :=
    hact.eventually (Iio_mem_nhds hA)
  filter_upwards [hmem, hpos, hactLt] with n hnDom hnPos hnAct
  have hle := lCost_le_ray (I := I) S hS T x (Z n)
    (Real.sqrt (tau n)) (Real.sqrt_pos.2 hnPos) hnDom
  have hle' : lCost S T x (lExp S T x (Z n) (tau n)) (tau n) ≤
      lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0
        (Real.sqrt (tau n)) := by
    simpa only [lExp, Real.sq_sqrt hnPos.le] using hle
  exact hle'.trans_lt hnAct

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_ray_event then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_ray_event"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_ray_event ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_ray_event

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
