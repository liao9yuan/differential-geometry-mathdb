import Submission.DifferentialGeometry.Analysis.Integration.Lp.Product
import Mathlib.MeasureTheory.Measure.SeparableMeasure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Filter _root_.Set
open scoped _root_.ENNReal _root_.Topology
namespace MeasureTheory
open _root_.MeasureTheory
variable {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [NormedAddCommGroup E] {μ : Measure A} {ν : Measure B} [SFinite ν]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

open _root_.Classical in
open _root_.MeasureTheory in
private def slice (f : _root_.MeasureTheory.Lp E p (μ.prod ν)) (a : A) : _root_.MeasureTheory.Lp E p ν :=
  if h : _root_.MeasureTheory.MemLp (fun b => f (a, b)) p ν then h.toLp (fun b => f (a, b)) else 0

run_cmd do
  let target := ``Submission.MeasureTheory.slice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.slice target :: scope.openDecls } }

open _root_.MeasureTheory in
private theorem measurable_of_edist
    {X Y : Type*} [MeasurableSpace X] [PseudoEMetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    {f : X → Y} (hf : ∀ y, Measurable (fun x => _root_.EDist.edist (f x) y)) : Measurable f := by
  let S : Set (Set Y) := {s | ∃ y r, s = Metric.eball y r}
  have hS : TopologicalSpace.IsTopologicalBasis S := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨y, r, rfl⟩
      exact Metric.isOpen_eball
    · intro y s hy hs
      obtain ⟨r, hr, hrs⟩ := EMetric.isOpen_iff.mp hs y hy
      exact ⟨Metric.eball y r, ⟨y, r, rfl⟩, Metric.mem_eball_self hr, hrs⟩
  rw [‹BorelSpace Y›.measurable_eq, hS.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro _ ⟨y, r, rfl⟩
  exact measurableSet_lt (hf y) measurable_const

run_cmd do
  let target := ``Submission.MeasureTheory.measurable_of_edist
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.measurable_of_edist target :: scope.openDecls } }

open _root_.MeasureTheory in
private theorem measurable_eLpNorm_slice (hp : p ≠ ⊤) {F : A × B → E}
    (hF : _root_.MeasureTheory.StronglyMeasurable F) :
    Measurable (fun a => _root_.MeasureTheory.eLpNorm (fun b => F (a, b)) p ν) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  simp_rw [_root_.MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  exact (hF.enorm.pow_const p.toReal).lintegral_prod_right'.pow_const _

run_cmd do
  let target := ``Submission.MeasureTheory.measurable_eLpNorm_slice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.measurable_eLpNorm_slice target :: scope.openDecls } }

open _root_.MeasureTheory in
private theorem measurableSet_memLp_slice (hp : p ≠ ⊤) (f : _root_.MeasureTheory.Lp E p (μ.prod ν)) :
    MeasurableSet {a | _root_.MeasureTheory.MemLp (fun b => f (a, b)) p ν} := by
  have hsm (a : A) : _root_.MeasureTheory.StronglyMeasurable (fun b => f (a, b)) :=
    (Lp.stronglyMeasurable f).comp_measurable (measurable_const.prodMk measurable_id)
  have heq : {a | _root_.MeasureTheory.MemLp (fun b => f (a, b)) p ν} =
      {a | _root_.MeasureTheory.eLpNorm (fun b => f (a, b)) p ν < ⊤} := by
    ext a
    exact ⟨fun h => h.2, fun h => ⟨(hsm a).aestronglyMeasurable, h⟩⟩
  rw [heq]
  exact measurableSet_lt (measurable_eLpNorm_slice hp (Lp.stronglyMeasurable f)) measurable_const

run_cmd do
  let target := ``Submission.MeasureTheory.measurableSet_memLp_slice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.measurableSet_memLp_slice target :: scope.openDecls } }

omit [SFinite ν] [Fact (1 ≤ p)] in
open _root_.Classical in
open _root_.MeasureTheory in
private theorem edist_slice (f : _root_.MeasureTheory.Lp E p (μ.prod ν)) (g : _root_.MeasureTheory.Lp E p ν) (a : A) :
    _root_.EDist.edist (slice f a) g =
      if _root_.MeasureTheory.MemLp (fun b => f (a, b)) p ν then _root_.MeasureTheory.eLpNorm (fun b => f (a, b) - g b) p ν
      else _root_.EDist.edist (0 : _root_.MeasureTheory.Lp E p ν) g := by
  classical
  by_cases ha : _root_.MeasureTheory.MemLp (fun b => f (a, b)) p ν
  · simp only [slice, dif_pos ha, if_pos ha]
    have hg : (Lp.memLp g).toLp (fun b => g b) = g := Lp.toLp_coeFn g (Lp.memLp g)
    conv_lhs => rhs; rw [← hg]
    exact Lp.edist_toLp_toLp _ _ ha (Lp.memLp g)
  · simp only [slice, dif_neg ha, if_neg ha]

run_cmd do
  let target := ``Submission.MeasureTheory.edist_slice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.edist_slice target :: scope.openDecls } }

open _root_.MeasureTheory in
private theorem measurable_slice (hp : p ≠ ⊤) (f : _root_.MeasureTheory.Lp E p (μ.prod ν))
    [MeasurableSpace (_root_.MeasureTheory.Lp E p ν)] [BorelSpace (_root_.MeasureTheory.Lp E p ν)]
    [_root_.SecondCountableTopology (_root_.MeasureTheory.Lp E p ν)] : Measurable (slice f) := by
  classical
  apply measurable_of_edist
  intro g
  have hd : Measurable (fun a => _root_.MeasureTheory.eLpNorm (fun b => f (a, b) - g b) p ν) :=
    measurable_eLpNorm_slice (E := E) (F := fun z => f z - g z.2) hp
      ((Lp.stronglyMeasurable f).sub
        ((Lp.stronglyMeasurable g).comp_measurable measurable_snd))
  have heq : (fun a => _root_.EDist.edist (slice f a) g) = fun a =>
      if _root_.MeasureTheory.MemLp (fun b => f (a, b)) p ν then _root_.MeasureTheory.eLpNorm (fun b => f (a, b) - g b) p ν
      else _root_.EDist.edist (0 : _root_.MeasureTheory.Lp E p ν) g := by
    funext a
    exact edist_slice f g a
  rw [heq]
  exact Measurable.ite (measurableSet_memLp_slice hp f) hd measurable_const

run_cmd do
  let target := ``Submission.MeasureTheory.measurable_slice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.measurable_slice target :: scope.openDecls } }

omit [Fact (1 ≤ p)] in
open _root_.MeasureTheory in
private theorem slice_coeFn (hp : p ≠ ⊤) (f : _root_.MeasureTheory.Lp E p (μ.prod ν)) :
    ∀ᵐ a ∂μ, (slice f a : B → E) =ᵐ[ν] fun b => f (a, b) := by
  filter_upwards [(Lp.memLp f).prodMk_left hp] with a ha
  simpa only [slice, dif_pos ha] using ha.coeFn_toLp

run_cmd do
  let target := ``Submission.MeasureTheory.slice_coeFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.slice_coeFn target :: scope.openDecls } }

open _root_.MeasureTheory in
private theorem memLp_slice (hp : p ≠ ⊤) (f : _root_.MeasureTheory.Lp E p (μ.prod ν))
    (hf : _root_.MeasureTheory.AEStronglyMeasurable (slice f) μ) : _root_.MeasureTheory.MemLp (slice f) p μ := by
  refine ⟨hf, ?_⟩
  have heq : (fun a => ‖slice f a‖ₑ) =ᵐ[μ] fun a => _root_.MeasureTheory.eLpNorm (fun b => f (a, b)) p ν := by
    filter_upwards [(Lp.memLp f).prodMk_left hp] with a ha
    simp only [slice, dif_pos ha, Lp.enorm_toLp]
  rw [← _root_.MeasureTheory.eLpNorm_enorm]
  rw [_root_.MeasureTheory.eLpNorm_congr_ae heq, eLpNorm_eLpNorm hp (Lp.stronglyMeasurable f).enorm.aemeasurable]
  exact (Lp.memLp f).2

run_cmd do
  let target := ``Submission.MeasureTheory.memLp_slice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.memLp_slice target :: scope.openDecls } }

open _root_.MeasureTheory in
private theorem norm_curry (hp : p ≠ ⊤) (f : _root_.MeasureTheory.Lp E p (μ.prod ν))
    (hf : _root_.MeasureTheory.MemLp (slice f) p μ) : ‖hf.toLp (slice f)‖ = ‖f‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  congr 1
  have heq : (fun a => ‖slice f a‖ₑ) =ᵐ[μ] fun a => _root_.MeasureTheory.eLpNorm (fun b => f (a, b)) p ν := by
    filter_upwards [(Lp.memLp f).prodMk_left hp] with a ha
    simp only [slice, dif_pos ha, Lp.enorm_toLp]
  rw [← _root_.MeasureTheory.eLpNorm_enorm, _root_.MeasureTheory.eLpNorm_congr_ae heq,
    eLpNorm_eLpNorm hp (Lp.stronglyMeasurable f).enorm.aemeasurable]

run_cmd do
  let target := ``Submission.MeasureTheory.norm_curry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.norm_curry target :: scope.openDecls } }

variable [_root_.SecondCountableTopology (Lp E p ν)]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.exists_curry (hp : p ≠ ⊤) (f : _root_.MeasureTheory.Lp E p (μ.prod ν)) :
    ∃ g : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ,
      (∀ᵐ a ∂μ, (g a : B → E) =ᵐ[ν] fun b => f (a, b)) ∧ ‖g‖ = ‖f‖ := by
  let : MeasurableSpace (_root_.MeasureTheory.Lp E p ν) := borel (_root_.MeasureTheory.Lp E p ν)
  let : BorelSpace (_root_.MeasureTheory.Lp E p ν) := ⟨rfl⟩
  have hmem := memLp_slice hp f (measurable_slice hp f).stronglyMeasurable.aestronglyMeasurable
  refine ⟨hmem.toLp (slice f), ?_, norm_curry hp f hmem⟩
  filter_upwards [hmem.coeFn_toLp, slice_coeFn hp f] with a ha hs
  rw [ha]
  exact hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.exists_curry then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.exists_curry"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.exists_curry ``Submission.MeasureTheory.Lp.exists_curry

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.uncurry_surjective (hp : p ≠ ⊤) :
    Function.Surjective (Lp.uncurry (E := E) (μ := μ) (ν := ν) 𝕜 hp) := by
  intro f
  obtain ⟨g, hg, _⟩ := Lp.exists_curry hp f
  refine ⟨g, Lp.ext_curry ?_⟩
  filter_upwards [Lp.uncurry_coeFn (𝕜 := 𝕜) hp g, hg] with a ha hb
  exact ha.trans hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.uncurry_surjective then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.uncurry_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.uncurry_surjective ``Submission.MeasureTheory.Lp.uncurry_surjective

variable (𝕜) in
open _root_.MeasureTheory _root_.MeasureTheory.Lp in
def Lp.curry (hp : p ≠ ⊤) : _root_.MeasureTheory.Lp E p (μ.prod ν) ≃ₗᵢ[𝕜] _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ :=
  (LinearIsometryEquiv.ofSurjective (Lp.uncurry 𝕜 hp) (Lp.uncurry_surjective hp)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.curry then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.curry"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.curry ``Submission.MeasureTheory.Lp.curry

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
@[simp]
theorem Lp.uncurry_curry (hp : p ≠ ⊤) (f : _root_.MeasureTheory.Lp E p (μ.prod ν)) :
    Lp.uncurry 𝕜 hp (Lp.curry 𝕜 hp f) = f :=
  (LinearIsometryEquiv.ofSurjective (Lp.uncurry 𝕜 hp)
    (Lp.uncurry_surjective hp)).apply_symm_apply f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.uncurry_curry then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.uncurry_curry"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.uncurry_curry ``Submission.MeasureTheory.Lp.uncurry_curry

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
@[simp]
theorem Lp.curry_uncurry (hp : p ≠ ⊤) (f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) :
    Lp.curry 𝕜 hp (Lp.uncurry 𝕜 hp f) = f :=
  (LinearIsometryEquiv.ofSurjective (Lp.uncurry 𝕜 hp)
    (Lp.uncurry_surjective hp)).symm_apply_apply f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.curry_uncurry then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.curry_uncurry"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.curry_uncurry ``Submission.MeasureTheory.Lp.curry_uncurry

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.curry_coeFn (hp : p ≠ ⊤) (f : _root_.MeasureTheory.Lp E p (μ.prod ν)) :
    ∀ᵐ a ∂μ, (Lp.curry 𝕜 hp f a : B → E) =ᵐ[ν] fun b => f (a, b) := by
  have h := Lp.uncurry_coeFn (𝕜 := 𝕜) hp (Lp.curry 𝕜 hp f)
  rw [Lp.uncurry_curry] at h
  exact h.mono fun _ ha => ha.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.curry_coeFn then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.curry_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.curry_coeFn ``Submission.MeasureTheory.Lp.curry_coeFn

end MeasureTheory
