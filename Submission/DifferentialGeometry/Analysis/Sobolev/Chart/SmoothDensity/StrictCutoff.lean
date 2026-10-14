import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Set _root_.Topology _root_.Bundle _root_.Manifold _root_.Filter
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M] [I.Boundaryless]

open _root_.Submission.DifferentialGeometry.Integral.Measure

omit [T2Space M] [CompactSpace M] in
private lemma isClosed_compl_chartAt_source (α : M) :
    IsClosed ((chartAt H α).sourceᶜ) :=
  (chartAt H α).open_source.isClosed_compl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.isClosed_compl_chartAt_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.isClosed_compl_chartAt_source target :: scope.openDecls } }

omit [I.Boundaryless] in
private lemma isClosed_tsupport_chartAtlasPOU (α : M) :
    IsClosed (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  isClosed_tsupport _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.isClosed_tsupport_chartAtlasPOU
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.isClosed_tsupport_chartAtlasPOU target :: scope.openDecls } }

omit [I.Boundaryless] in
private lemma tsupport_chartAtlasPOU_subset (α : M) :
    tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
      (chartAt H α).source :=
  (chartAtlasPOU_isSubordinate I M) α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartAtlasPOU_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartAtlasPOU_subset target :: scope.openDecls } }

omit [I.Boundaryless] in
private lemma disjoint_complSource_tsupport_chartAtlasPOU (α : M) :
    Disjoint ((chartAt H α).sourceᶜ)
      (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  Set.disjoint_compl_left_iff_subset.mpr
    (tsupport_chartAtlasPOU_subset (I := I) α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.disjoint_complSource_tsupport_chartAtlasPOU
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.disjoint_complSource_tsupport_chartAtlasPOU target :: scope.openDecls } }

private def chartStrictCutoffBundled (α : M) : C^∞⟮I, M; ℝ⟯ :=
  ((Classical.choose
    (exists_contMDiffMap_zero_one_nhds_of_isClosed (I := I) (M := M)
      (n := (⊤ : ℕ∞))
      (isClosed_compl_chartAt_source (M := M) α)
      (isClosed_tsupport_chartAtlasPOU (I := I) α)
      (disjoint_complSource_tsupport_chartAtlasPOU (I := I) α))) :
        C^∞⟮I, M; ℝ⟯)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoffBundled
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoffBundled target :: scope.openDecls } }

omit [I.Boundaryless] in
private lemma chartStrictCutoffBundled_spec (α : M) :
    (∀ᶠ x in 𝓝ˢ ((chartAt H α).sourceᶜ),
      ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) ∧
    (∀ᶠ x in 𝓝ˢ (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
      ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1) ∧
    ∀ x, ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ∈
        Set.Icc (0 : ℝ) 1 :=
  Classical.choose_spec
    (exists_contMDiffMap_zero_one_nhds_of_isClosed (I := I) (M := M)
      (n := (⊤ : ℕ∞))
      (isClosed_compl_chartAt_source (M := M) α)
      (isClosed_tsupport_chartAtlasPOU (I := I) α)
      (disjoint_complSource_tsupport_chartAtlasPOU (I := I) α))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoffBundled_spec
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoffBundled_spec target :: scope.openDecls } }

def chartStrictCutoff (α : M) : M → ℝ :=
  ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff

omit [I.Boundaryless] in
private lemma chartStrictCutoff_eq_bundled (α : M) :
    chartStrictCutoff (I := I) α =
      ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eq_bundled
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eq_bundled target :: scope.openDecls } }

omit [I.Boundaryless] in
theorem chartStrictCutoff_contMDiff (α : M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (chartStrictCutoff (I := I) α) :=
  (chartStrictCutoffBundled (I := I) α).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_contMDiff

omit [I.Boundaryless] in
theorem chartStrictCutoff_nonneg (α : M) (x : M) :
    0 ≤ chartStrictCutoff (I := I) α x :=
  ((chartStrictCutoffBundled_spec (I := I) α).2.2 x).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_nonneg

omit [I.Boundaryless] in
theorem chartStrictCutoff_le_one (α : M) (x : M) :
    chartStrictCutoff (I := I) α x ≤ 1 :=
  ((chartStrictCutoffBundled_spec (I := I) α).2.2 x).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_le_one ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_le_one

omit [I.Boundaryless] in
theorem chartStrictCutoff_eventually_zero_nhdsSet_compl_source (α : M) :
    ∀ᶠ x in 𝓝ˢ ((chartAt H α).sourceᶜ), chartStrictCutoff (I := I) α x = 0 :=
  (chartStrictCutoffBundled_spec (I := I) α).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eventually_zero_nhdsSet_compl_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eventually_zero_nhdsSet_compl_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eventually_zero_nhdsSet_compl_source ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eventually_zero_nhdsSet_compl_source

omit [I.Boundaryless] in
theorem chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU (α : M) :
    ∀ᶠ x in 𝓝ˢ (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
      chartStrictCutoff (I := I) α x = 1 :=
  (chartStrictCutoffBundled_spec (I := I) α).2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU

omit [I.Boundaryless] in
theorem chartStrictCutoff_eq_one_on_tsupport_chartAtlasPOU (α : M) {x : M}
    (hx : x ∈ tsupport
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    chartStrictCutoff (I := I) α x = 1 :=
  (chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU
    (I := I) α).self_of_nhdsSet _ hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eq_one_on_tsupport_chartAtlasPOU then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eq_one_on_tsupport_chartAtlasPOU"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eq_one_on_tsupport_chartAtlasPOU ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eq_one_on_tsupport_chartAtlasPOU

omit [I.Boundaryless] in
theorem chartStrictCutoff_eq_zero_of_notMem_chartAt_source (α : M) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    chartStrictCutoff (I := I) α x = 0 := by
  have hmem : x ∈ ((chartAt H α).sourceᶜ) := hx
  exact (chartStrictCutoff_eventually_zero_nhdsSet_compl_source
    (I := I) α).self_of_nhdsSet _ hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eq_zero_of_notMem_chartAt_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eq_zero_of_notMem_chartAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eq_zero_of_notMem_chartAt_source ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_eq_zero_of_notMem_chartAt_source

omit [I.Boundaryless] in
theorem chartStrictCutoff_tsupport_subset (α : M) :
    tsupport (chartStrictCutoff (I := I) α) ⊆ (chartAt H α).source := by
  classical
  have hev : ∀ᶠ x in 𝓝ˢ ((chartAt H α).sourceᶜ),
      chartStrictCutoff (I := I) α x = 0 :=
    chartStrictCutoff_eventually_zero_nhdsSet_compl_source (I := I) α
  rw [eventually_nhdsSet_iff_exists] at hev
  obtain ⟨U, hUopen, hUsub, hUzero⟩ := hev
  have hUcomp : IsClosed (Uᶜ) := hUopen.isClosed_compl
  have hsupp_sub : Function.support (chartStrictCutoff (I := I) α) ⊆ Uᶜ := by
    intro x hx
    by_contra hxU
    have hxU' : x ∈ U := by
      simpa using hxU
    exact hx (hUzero x hxU')
  have htsupp_sub : tsupport (chartStrictCutoff (I := I) α) ⊆ Uᶜ :=
    closure_minimal hsupp_sub hUcomp
  have hUcomp_sub : Uᶜ ⊆ (chartAt H α).source := by
    intro x hx
    by_contra hx_not
    have : x ∈ U := hUsub hx_not
    exact hx this
  exact htsupp_sub.trans hUcomp_sub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_tsupport_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_tsupport_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartStrictCutoff_tsupport_subset

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
