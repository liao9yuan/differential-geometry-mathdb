import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Compactness.Lindelof

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Analysis.Calculus

open _root_.Filter _root_.MeasureTheory _root_.Set _root_.Metric
open scoped _root_.Topology

variable {T E F : Type*}
  [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem exists_local_cutoff {U : Set E} (hU : IsOpen U) (x : U) :
    ∃ (V : Set E) (β : C(E, ℝ)), IsOpen V ∧ (x : E) ∈ V ∧
      EqOn β 1 V ∧ tsupport β ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds x.2)
  obtain ⟨β, hβ, _, hβU, _⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen (_root_.ProperSpace.isCompact_closedBall (x : E) r) hU hrU
  exact ⟨ball (x : E) r, β, _root_.Metric.isOpen_ball, _root_.Metric.mem_ball_self hr,
    hβ.mono _root_.Metric.ball_subset_closedBall, hβU⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Calculus.exists_local_cutoff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Calculus.exists_local_cutoff target :: scope.openDecls } }

omit [MeasurableSpace T] [OpensMeasurableSpace T] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] [CompleteSpace F] in
private theorem continuous_parametric_cutoff {U : Set E} {f : T → E → F}
    (hU : IsOpen U) (hf : ContinuousOn (Function.uncurry f) (_root_.Set.univ ×ˢ U))
    (β : C(E, ℝ)) (hβ : tsupport β ⊆ U) :
    Continuous (fun z : T × E => β z.2 • f z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z.2 ∈ tsupport β
  · have hzf : ContinuousAt (Function.uncurry f) z :=
      (hf z ⟨mem_univ _, hβ hz⟩).continuousAt
        ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _, hβ hz⟩)
    exact (β.continuous.comp continuous_snd).continuousAt.smul hzf
  · have hβzero : (fun w : T × E => β w.2) =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
      (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto continuous_snd.continuousAt
    have hzero : (fun w : T × E => β w.2 • f w.1 w.2) =ᶠ[𝓝 z] fun _ => (0 : F) := by
      filter_upwards [hβzero] with w hw
      rw [hw, zero_smul]
    exact continuousAt_const.congr hzero.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Calculus.continuous_parametric_cutoff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Calculus.continuous_parametric_cutoff target :: scope.openDecls } }

theorem measurable_fderiv_with_param_on_open
    {U : Set E} {f : T → E → F}
    (hU : IsOpen U) (hf : ContinuousOn (Function.uncurry f) (_root_.Set.univ ×ˢ U)) :
    Measurable (fun z : T × U => fderiv ℝ (f z.1) z.2) := by
  classical
  choose V β hV hxV hβone hβU using fun x : U => exists_local_cutoff hU x
  have hcover : U ⊆ ⋃ x : U, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨c, hc, hcU⟩ :=
    (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover V hV hcover
  let G : U → T → E → F := fun i t x => β i x • f t x
  have hG : ∀ i : U, Measurable (fun z : T × E => fderiv ℝ (G i z.1) z.2) := by
    intro i
    exact measurable_fderiv_with_param ℝ (continuous_parametric_cutoff hU hf (β i) (hβU i))
  have hG_eq : ∀ (i : U) (t : T) (x : E), x ∈ V i →
      fderiv ℝ (G i t) x = fderiv ℝ (f t) x := by
    intro i t x hx
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(hV i).mem_nhds hx] with y hy
    change β i y • f t y = f t y
    simp only [hβone i hy, Pi.one_apply, one_smul]
  let pull : T × U → T × E := fun z => (z.1, z.2)
  have hpull : Measurable pull :=
    measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
  intro K hK
  have hpre : (fun z : T × U => fderiv ℝ (f z.1) z.2) ⁻¹' K =
      ⋃ i ∈ c, {z : T × U | (z.2 : E) ∈ V i} ∩
        (fun z : T × U => fderiv ℝ (G i z.1) z.2) ⁻¹' K := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hic, hi⟩ := mem_iUnion₂.mp (hcU z.2.2)
      exact mem_iUnion₂.mpr ⟨i, hic, hi, by simpa only [_root_.Set.mem_preimage, hG_eq i z.1 z.2 hi] using hz⟩
    · intro hz
      obtain ⟨i, _, hi, hzK⟩ := mem_iUnion₂.mp hz
      simpa only [_root_.Set.mem_preimage, hG_eq i z.1 z.2 hi] using hzK
  rw [hpre]
  exact MeasurableSet.biUnion hc fun i _ =>
    ((measurable_subtype_coe.comp measurable_snd) (hV i).measurableSet).inter
      (((hG i).comp hpull) hK)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.measurable_fderiv_with_param_on_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.measurable_fderiv_with_param_on_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.measurable_fderiv_with_param_on_open ``Submission.DifferentialGeometry.Analysis.Calculus.measurable_fderiv_with_param_on_open

end DifferentialGeometry.Analysis.Calculus
