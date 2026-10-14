import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

def chartESectionRepr (α : M) (σ : Π x : M, TangentSpace I x) (x : M) : E :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x (σ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartESectionRepr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartESectionRepr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartESectionRepr ``Submission.DifferentialGeometry.Geometry.Connection.chartESectionRepr

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_def (α : M) (σ : Π x : M, TangentSpace I x) :
    chartESectionRepr (I := I) α σ =
      fun x : M =>
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x (σ x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartE_section_repr_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartE_section_repr_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartE_section_repr_def ``Submission.DifferentialGeometry.Geometry.Connection.chartE_section_repr_def

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_apply
    (α : M) (σ : Π x : M, TangentSpace I x) (x : M) :
    chartESectionRepr (I := I) α σ x =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x (σ x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartE_section_repr_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartE_section_repr_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartE_section_repr_apply ``Submission.DifferentialGeometry.Geometry.Connection.chartE_section_repr_apply

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_eq_trivialization_snd
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    chartESectionRepr (I := I) α σ x =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α ⟨x, σ x⟩).2 := by
  classical
  unfold chartESectionRepr
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    _root_.FiberBundle.trivializationAt E (TangentSpace I) α
  rw [T.apply_eq_prod_continuousLinearEquivAt ℝ x hx (σ x)]
  rw [show (x, (T.continuousLinearEquivAt ℝ x hx) (σ x)).2 =
        T.continuousLinearEquivAt ℝ x hx (σ x) from rfl]
  rw [show (T.continuousLinearEquivAt ℝ x hx (σ x) : E) =
          T.continuousLinearMapAt ℝ x (σ x) from
        congrFun (T.coe_continuousLinearEquivAt_eq (R := ℝ) hx) (σ x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartE_section_repr_eq_trivialization_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartE_section_repr_eq_trivialization_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartE_section_repr_eq_trivialization_snd ``Submission.DifferentialGeometry.Geometry.Connection.chartE_section_repr_eq_trivialization_snd

variable (I) in
omit [FiniteDimensional ℝ E] in
theorem mdifferentiableWithinAt_section_iff_chartE
    (α : M) (σ : Π x : M, TangentSpace I x) {u : Set M} {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    MDiffAt[u] (T% σ) x ↔ MDiffAt[u] (chartESectionRepr (I := I) α σ) x := by
  classical
  have hiff :=
    Bundle.Trivialization.mdifferentiableWithinAt_section_iff (𝕜 := ℝ) I (u := u)
      (e := _root_.FiberBundle.trivializationAt E (TangentSpace I) α) σ hx
  refine hiff.trans ?_
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine h.congr_of_eventuallyEq (f₁ := chartESectionRepr (I := I) α σ) ?_ ?_
    · filter_upwards
        [mem_nhdsWithin_of_mem_nhds
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)] with y hy
      exact chartE_section_repr_eq_trivialization_snd (I := I) α σ hy
    · exact chartE_section_repr_eq_trivialization_snd (I := I) α σ hx
  · refine h.congr_of_eventuallyEq
        (f₁ := fun y => (_root_.FiberBundle.trivializationAt E (TangentSpace I) α ⟨y, σ y⟩).2) ?_ ?_
    · filter_upwards
        [mem_nhdsWithin_of_mem_nhds
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)] with y hy
      exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hy).symm
    · exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hx).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mdifferentiableWithinAt_section_iff_chartE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mdifferentiableWithinAt_section_iff_chartE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mdifferentiableWithinAt_section_iff_chartE ``Submission.DifferentialGeometry.Geometry.Connection.mdifferentiableWithinAt_section_iff_chartE

variable (I) in
omit [FiniteDimensional ℝ E] in
theorem mdifferentiableAt_section_iff_chartE
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    MDiffAt (T% σ) x ↔ MDiffAt (chartESectionRepr (I := I) α σ) x := by
  classical
  rw [← mdifferentiableWithinAt_univ, ← mdifferentiableWithinAt_univ]
  exact mdifferentiableWithinAt_section_iff_chartE I α σ hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mdifferentiableAt_section_iff_chartE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mdifferentiableAt_section_iff_chartE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mdifferentiableAt_section_iff_chartE ``Submission.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_section_iff_chartE

omit [FiniteDimensional ℝ E] in
private lemma mdifferentiableAt_iff_pullback_of_mem_source
    (α : M) (f : M → E) {x : M} (hx : x ∈ (chartAt H α).source) :
    MDiffAt f x ↔
      MDiffAt[_root_.Set.range I] (f ∘ (extChartAt I α).symm) (extChartAt I α x) :=
  mdifferentiableAt_iff_source_of_mem_source (x := α) (x' := x) hx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_iff_pullback_of_mem_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.mdifferentiableAt_iff_pullback_of_mem_source target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private lemma mdifferentiableWithinAt_range_iff_differentiableAt_of_interior
    {α : M} {f : E → E} {y : E}
    (hy_int : y ∈ interior ((extChartAt I α).target : Set E)) :
    MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E) f (_root_.Set.range I) y ↔ DifferentiableAt ℝ f y := by
  classical
  have htgt : (extChartAt I α).target ⊆ _root_.Set.range I := extChartAt_target_subset_range α
  have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
  have hrange_nhds : _root_.Set.range I ∈ 𝓝 y :=
    Filter.mem_of_superset (hint_open.mem_nhds hy_int)
      (interior_subset.trans htgt)
  rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
  exact ⟨fun h => h.differentiableAt hrange_nhds, fun h => h.differentiableWithinAt⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.mdifferentiableWithinAt_range_iff_differentiableAt_of_interior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.mdifferentiableWithinAt_range_iff_differentiableAt_of_interior target :: scope.openDecls } }

variable (I) in
omit [FiniteDimensional ℝ E] in
theorem mdifferentiableAt_section_iff_chartE_fderiv
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx_source : x ∈ (chartAt H α).source)
    (hx_base : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E)) :
    MDiffAt (T% σ) x ↔
      DifferentiableAt ℝ
        (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
        (extChartAt I α x) := by
  classical
  rw [mdifferentiableAt_section_iff_chartE I α σ hx_base]
  rw [mdifferentiableAt_iff_pullback_of_mem_source α
      (chartESectionRepr (I := I) α σ) hx_source]
  exact mdifferentiableWithinAt_range_iff_differentiableAt_of_interior (α := α) hx_int

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mdifferentiableAt_section_iff_chartE_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mdifferentiableAt_section_iff_chartE_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mdifferentiableAt_section_iff_chartE_fderiv ``Submission.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_section_iff_chartE_fderiv

variable (I) in
omit [FiniteDimensional ℝ E] in
theorem contMDiffWithinAt_section_iff_chartE
    {k : ℕ∞} (α : M) (σ : Π x : M, TangentSpace I x) {u : Set M} {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) k (T% σ) u x ↔
      ContMDiffWithinAt I 𝓘(ℝ, E) k (chartESectionRepr (I := I) α σ) u x := by
  classical
  have hiff :=
    Bundle.Trivialization.contMDiffWithinAt_section (𝕜 := ℝ) (IB := I)
      (n := (k : WithTop ℕ∞)) (s := σ) (a := u)
      (e := _root_.FiberBundle.trivializationAt E (TangentSpace I) α) hx
  refine hiff.trans ?_
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine h.congr_of_eventuallyEq (f₁ := chartESectionRepr (I := I) α σ) ?_ ?_
    · filter_upwards
        [mem_nhdsWithin_of_mem_nhds
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)] with y hy
      exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hy)
    · exact chartE_section_repr_eq_trivialization_snd (I := I) α σ hx
  · refine h.congr_of_eventuallyEq
        (f₁ := fun y => (_root_.FiberBundle.trivializationAt E (TangentSpace I) α ⟨y, σ y⟩).2) ?_ ?_
    · filter_upwards
        [mem_nhdsWithin_of_mem_nhds
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)] with y hy
      exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hy).symm
    · exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hx).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.contMDiffWithinAt_section_iff_chartE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.contMDiffWithinAt_section_iff_chartE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.contMDiffWithinAt_section_iff_chartE ``Submission.DifferentialGeometry.Geometry.Connection.contMDiffWithinAt_section_iff_chartE

variable (I) in
omit [FiniteDimensional ℝ E] in
theorem contMDiffAt_section_iff_chartE
    {k : ℕ∞} (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) k (T% σ) x ↔
      ContMDiffAt I 𝓘(ℝ, E) k (chartESectionRepr (I := I) α σ) x := by
  classical
  rw [← contMDiffWithinAt_univ, ← contMDiffWithinAt_univ]
  exact contMDiffWithinAt_section_iff_chartE I α σ hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.contMDiffAt_section_iff_chartE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.contMDiffAt_section_iff_chartE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.contMDiffAt_section_iff_chartE ``Submission.DifferentialGeometry.Geometry.Connection.contMDiffAt_section_iff_chartE

variable (I) in
omit [FiniteDimensional ℝ E] in
theorem mfderiv_section_eq_chartE_fderiv
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx_source : x ∈ (chartAt H α).source)
    (hx_base : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E))
    (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ, E) (chartESectionRepr (I := I) α σ) x) v =
      fderiv ℝ (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
        (extChartAt I α x)
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v) := by
  classical
  set fE := chartESectionRepr (I := I) α σ
  set φ := extChartAt I α
  set y₀ : E := φ x
  set gE : E → E := fE ∘ φ.symm
  have hfE_eqOn : ∀ y, y ∈ φ.source → fE y = gE (φ y) := by
    intro y hy
    change fE y = fE (φ.symm (φ y))
    have : φ.symm (φ y) = y := φ.left_inv hy
    rw [this]
  have hsrc_extChart : x ∈ φ.source := by
    rw [extChartAt_source]; exact hx_source
  have hsrc_nhds : φ.source ∈ 𝓝 x := extChartAt_source_mem_nhds' (I := I) hsrc_extChart
  have hev : fE =ᶠ[𝓝 x] gE ∘ φ := by
    filter_upwards [hsrc_nhds] with y hy
    exact hfE_eqOn y hy
  have hmfderiv_eq :
      mfderiv I 𝓘(ℝ, E) fE x = mfderiv I 𝓘(ℝ, E) (gE ∘ φ) x :=
    Filter.EventuallyEq.mfderiv_eq hev
  have hφ_mdiff : MDiffAt φ x := mdifferentiableAt_extChartAt (I := I) (x := α) hx_source
  have hgE_diff : DifferentiableAt ℝ gE y₀ :=
    (mdifferentiableAt_section_iff_chartE_fderiv (I := I) α σ hx_source hx_base hx_int).mp hσ
  have hgE_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) gE y₀ :=
    hgE_diff.mdifferentiableAt
  have hchain :
      mfderiv I 𝓘(ℝ, E) (gE ∘ φ) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) gE (φ x)).comp (mfderiv I 𝓘(ℝ, E) φ x) :=
    mfderiv_comp x hgE_mdiff hφ_mdiff
  have hmf_to_fderiv :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) gE (φ x) = fderiv ℝ gE (φ x) :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (E := E) (E' := E) (f := gE) (x := φ x)
  have htriv_eq :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x =
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx_source).symm
  rw [hmfderiv_eq, hchain, hmf_to_fderiv]
  change (fderiv ℝ gE (φ x))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) v) =
      fderiv ℝ gE y₀
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v)
  rw [htriv_eq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mfderiv_section_eq_chartE_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mfderiv_section_eq_chartE_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mfderiv_section_eq_chartE_fderiv ``Submission.DifferentialGeometry.Geometry.Connection.mfderiv_section_eq_chartE_fderiv

variable (I) in
omit [FiniteDimensional ℝ E] in
theorem contDiffOn_chartE_pullback_of_contMDiff_section
    {k : ℕ∞} (α : M) (σ : Π x : M, TangentSpace I x)
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) k (T% σ)) :
    ContDiffOn ℝ k
      (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
      ((extChartAt I α) ''
        ((chartAt H α).source ∩ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) ∩
        (extChartAt I α).target) := by
  classical
  intro y hy
  obtain ⟨⟨x, ⟨hx_source, hx_base⟩, hx_eq⟩, hy_target⟩ := hy
  subst hx_eq
  set fE := chartESectionRepr (I := I) α σ
  set φ := extChartAt I α
  have hfE_at : ContMDiffAt I 𝓘(ℝ, E) k fE x :=
    (contMDiffAt_section_iff_chartE I α σ hx_base).mp (hσ x)
  have hxφ_source : x ∈ φ.source := by rw [extChartAt_source]; exact hx_source
  have hxφ_target : φ x ∈ φ.target := φ.map_source hxφ_source
  have hxφ_inv : φ.symm (φ x) = x := φ.left_inv hxφ_source
  have hsymm_at : ContMDiffWithinAt 𝓘(ℝ, E) I (k : WithTop ℕ∞) φ.symm φ.target (φ x) := by
    have hsymm_on_inf : ContMDiffOn 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm φ.target :=
      contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
    have hsymm_on : ContMDiffOn 𝓘(ℝ, E) I (k : WithTop ℕ∞) φ.symm φ.target :=
      hsymm_on_inf.of_le (by exact_mod_cast le_top)
    exact hsymm_on (φ x) hxφ_target
  have hcomp_at : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E) k (fE ∘ φ.symm) φ.target (φ x) := by
    have hfE_at' : ContMDiffAt I 𝓘(ℝ, E) k fE (φ.symm (φ x)) := by
      rw [hxφ_inv]; exact hfE_at
    exact hfE_at'.comp_contMDiffWithinAt (φ x) hsymm_at
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hcomp_at
  refine hcomp_at.mono ?_
  exact _root_.Set.inter_subset_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.contDiffOn_chartE_pullback_of_contMDiff_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.contDiffOn_chartE_pullback_of_contMDiff_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.contDiffOn_chartE_pullback_of_contMDiff_section ``Submission.DifferentialGeometry.Geometry.Connection.contDiffOn_chartE_pullback_of_contMDiff_section

variable (I) in
abbrev trivToE (α x : M) : TangentSpace I x →L[ℝ] E :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.trivToE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.trivToE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.trivToE ``Submission.DifferentialGeometry.Geometry.Connection.trivToE

variable (I) in
abbrev trivFromE (α x : M) : E →L[ℝ] TangentSpace I x :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.trivFromE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.trivFromE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.trivFromE ``Submission.DifferentialGeometry.Geometry.Connection.trivFromE

variable (I) in
omit [FiniteDimensional ℝ E] in
lemma trivFromE_trivToE
    (α : M) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (v : TangentSpace I x) :
    trivFromE (I := I) α x (trivToE (I := I) α x v) = v :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hx v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.trivFromE_trivToE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.trivFromE_trivToE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.trivFromE_trivToE ``Submission.DifferentialGeometry.Geometry.Connection.trivFromE_trivToE

variable (I) in
omit [FiniteDimensional ℝ E] in
lemma trivToE_trivFromE
    (α : M) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (w : E) :
    trivToE (I := I) α x (trivFromE (I := I) α x w) = w :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt_symmL (R := ℝ) hx w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.trivToE_trivFromE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.trivToE_trivFromE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.trivToE_trivFromE ``Submission.DifferentialGeometry.Geometry.Connection.trivToE_trivFromE

omit [FiniteDimensional ℝ E] in
@[simp] lemma chartE_section_repr_eq_trivToE
    (α : M) (σ : Π x : M, TangentSpace I x) (x : M) :
    chartESectionRepr (I := I) α σ x = trivToE (I := I) α x (σ x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartE_section_repr_eq_trivToE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartE_section_repr_eq_trivToE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartE_section_repr_eq_trivToE ``Submission.DifferentialGeometry.Geometry.Connection.chartE_section_repr_eq_trivToE

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_add
    (α : M) (σ τ : Π x : M, TangentSpace I x) (x : M) :
    chartESectionRepr (I := I) α (σ + τ) x =
      chartESectionRepr (I := I) α σ x + chartESectionRepr (I := I) α τ x := by
  classical
  unfold chartESectionRepr
  rw [Pi.add_apply, map_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartE_section_repr_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartE_section_repr_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartE_section_repr_add ``Submission.DifferentialGeometry.Geometry.Connection.chartE_section_repr_add

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_smul
    (α : M) (c : ℝ) (σ : Π x : M, TangentSpace I x) (x : M) :
    chartESectionRepr (I := I) α (c • σ) x = c • chartESectionRepr (I := I) α σ x := by
  classical
  unfold chartESectionRepr
  rw [Pi.smul_apply, map_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartE_section_repr_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartE_section_repr_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartE_section_repr_smul ``Submission.DifferentialGeometry.Geometry.Connection.chartE_section_repr_smul

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_smul_function
    (α : M) (f : M → ℝ) (σ : Π x : M, TangentSpace I x) (x : M) :
    chartESectionRepr (I := I) α (fun y => f y • σ y) x =
      f x • chartESectionRepr (I := I) α σ x := by
  classical
  unfold chartESectionRepr
  rw [map_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartE_section_repr_smul_function then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartE_section_repr_smul_function"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartE_section_repr_smul_function ``Submission.DifferentialGeometry.Geometry.Connection.chartE_section_repr_smul_function

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_zero (α : M) (x : M) :
    chartESectionRepr (I := I) α (fun _ => (0 : TangentSpace I _)) x = 0 := by
  classical
  unfold chartESectionRepr
  rw [map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartE_section_repr_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartE_section_repr_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartE_section_repr_zero ``Submission.DifferentialGeometry.Geometry.Connection.chartE_section_repr_zero

variable (I) in
omit [FiniteDimensional ℝ E] in
theorem mfderiv_scalar_eq_chart_fderiv
    (α : M) (f : M → ℝ) {x : M}
    (hx_source : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E))
    (hf : MDiffAt f x)
    (v : TangentSpace I x) :
    mvfderiv (I := I) f x v =
      fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)
        (trivToE (I := I) α x v) := by
  classical
  rw [mvfderiv, ContinuousLinearMap.comp_apply]
  set φ := extChartAt I α
  set g : E → ℝ := f ∘ φ.symm
  have hf_eqOn : ∀ y, y ∈ φ.source → f y = g (φ y) := by
    intro y hy
    change f y = f (φ.symm (φ y))
    rw [φ.left_inv hy]
  have hsrc_extChart : x ∈ φ.source := by
    rw [extChartAt_source]; exact hx_source
  have hsrc_nhds : φ.source ∈ 𝓝 x := extChartAt_source_mem_nhds' (I := I) hsrc_extChart
  have hev : f =ᶠ[𝓝 x] g ∘ φ := by
    filter_upwards [hsrc_nhds] with y hy
    exact hf_eqOn y hy
  have hmfderiv_eq :
      mfderiv I 𝓘(ℝ) f x = mfderiv I 𝓘(ℝ) (g ∘ φ) x :=
    Filter.EventuallyEq.mfderiv_eq hev
  have hφ_mdiff : MDiffAt φ x := mdifferentiableAt_extChartAt (I := I) (x := α) hx_source
  have hxφ_target : φ x ∈ φ.target := φ.map_source hsrc_extChart
  have hxφ_inv : φ.symm (φ x) = x := φ.left_inv hsrc_extChart
  have hsymm_within :
      MDifferentiableWithinAt 𝓘(ℝ, E) I φ.symm (_root_.Set.range I) (φ x) :=
    mdifferentiableWithinAt_extChartAt_symm (I := I) (x := α) hxφ_target
  have hrange_nhds : _root_.Set.range I ∈ 𝓝 (φ x) := by
    have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
    exact Filter.mem_of_superset
      (Filter.mem_of_superset (hint_open.mem_nhds hx_int) interior_subset)
      (extChartAt_target_subset_range α)
  have hg_within :
      MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ) g (_root_.Set.range I) (φ x) :=
    MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq
      (I' := I) (I'' := 𝓘(ℝ)) (g := f) (f := φ.symm)
      (s := _root_.Set.range I) (x := φ x) (y := x)
      hf hsymm_within hxφ_inv
  have hg_at : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) g (φ x) :=
    hg_within.mdifferentiableAt hrange_nhds
  have hchain :
      mfderiv I 𝓘(ℝ) (g ∘ φ) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g (φ x)).comp (mfderiv I 𝓘(ℝ, E) φ x) :=
    mfderiv_comp x hg_at hφ_mdiff
  have hg_diff : DifferentiableAt ℝ g (φ x) :=
    hg_at.differentiableAt
  have hmf_to_fderiv :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g (φ x) = fderiv ℝ g (φ x) :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (E := E) (E' := ℝ) (f := g) (x := φ x)
  have htriv_eq :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x =
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx_source).symm
  rw [hmfderiv_eq, hchain, hmf_to_fderiv]
  change (fderiv ℝ g (φ x))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) v) =
      fderiv ℝ g (φ x)
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v)
  rw [htriv_eq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mfderiv_scalar_eq_chart_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mfderiv_scalar_eq_chart_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mfderiv_scalar_eq_chart_fderiv ``Submission.DifferentialGeometry.Geometry.Connection.mfderiv_scalar_eq_chart_fderiv

end Connection
end Geometry
end DifferentialGeometry
