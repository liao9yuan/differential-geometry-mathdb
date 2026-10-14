import Submission.DifferentialGeometry.Topology.Manifold.RegularZero.Coordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Manifold.RegularZero
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {g : A → B} {S : Set A} {n : ℕ∞ω}

private def coordinates (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :=
  (exists_coordinates_finrank hn hs hg x.property.1 (hr x x.property.1 x.property.2)).choose

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.RegularZero.coordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.RegularZero.coordinates target :: scope.openDecls } }

private theorem coordinates_spec (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    x.val ∈ (coordinates hn hs hg hr x).source ∧
      (coordinates hn hs hg hr x).source ⊆ S ∧
      (∀ y, (coordinates hn hs hg hr x y).1 = g y) ∧
      (coordinates hn hs hg hr x x.val).2 = 0 :=
  (exists_coordinates_finrank hn hs hg x.property.1 (hr x x.property.1 x.property.2)).choose_spec

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.RegularZero.coordinates_spec
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.RegularZero.coordinates_spec target :: scope.openDecls } }


def chart (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    OpenPartialHomeomorph {y : A // y ∈ S ∧ g y = 0}
      (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) :=
  fiberChart g (coordinates hn hs hg hr x)
    (coordinates_spec hn hs hg hr x).2.2.1 (coordinates_spec hn hs hg hr x).2.1 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.RegularZero.chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.RegularZero.chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.RegularZero.chart ``Submission.DifferentialGeometry.Manifold.RegularZero.chart


theorem mem_chart_source (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    x ∈ (chart hn hs hg hr x).source := (coordinates_spec hn hs hg hr x).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.RegularZero.mem_chart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.RegularZero.mem_chart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.RegularZero.mem_chart_source ``Submission.DifferentialGeometry.Manifold.RegularZero.mem_chart_source


theorem chart_center (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    chart hn hs hg hr x x = 0 := (coordinates_spec hn hs hg hr x).2.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.RegularZero.chart_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.RegularZero.chart_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.RegularZero.chart_center ``Submission.DifferentialGeometry.Manifold.RegularZero.chart_center


theorem contDiffOn_chart_symm (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    ContDiffOn ℝ n (fun z => ((chart hn hs hg hr x).symm z).val)
      (chart hn hs hg hr x).target := by
  apply contDiffOn_fiberChart_symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.RegularZero.contDiffOn_chart_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.RegularZero.contDiffOn_chart_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.RegularZero.contDiffOn_chart_symm ``Submission.DifferentialGeometry.Manifold.RegularZero.contDiffOn_chart_symm


theorem contDiffOn_chart_transition (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x))
    (x y : {z : A // z ∈ S ∧ g z = 0}) :
    ContDiffOn ℝ n ((chart hn hs hg hr y) ∘ (chart hn hs hg hr x).symm)
      ((chart hn hs hg hr x).target ∩
        (chart hn hs hg hr x).symm ⁻¹' (chart hn hs hg hr y).source) :=
  by apply contDiffOn_fiberChart_transition

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.RegularZero.contDiffOn_chart_transition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.RegularZero.contDiffOn_chart_transition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.RegularZero.contDiffOn_chart_transition ``Submission.DifferentialGeometry.Manifold.RegularZero.contDiffOn_chart_transition


@[reducible]
def chartedSpace (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) :
    ChartedSpace (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ)
      {y : A // y ∈ S ∧ g y = 0} where
  atlas := _root_.Set.range (chart hn hs hg hr)
  chartAt := chart hn hs hg hr
  mem_chart_source := mem_chart_source hn hs hg hr
  chart_mem_atlas x := ⟨x,rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.RegularZero.chartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.RegularZero.chartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.RegularZero.chartedSpace ``Submission.DifferentialGeometry.Manifold.RegularZero.chartedSpace


theorem isManifold (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) :
    let _ := chartedSpace hn hs hg hr
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) n
      {y : A // y ∈ S ∧ g y = 0} := by
  let _ := chartedSpace hn hs hg hr
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x,rfl⟩ ⟨y,rfl⟩
  simpa using contDiffOn_chart_transition hn hs hg hr x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.RegularZero.isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.RegularZero.isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.RegularZero.isManifold ``Submission.DifferentialGeometry.Manifold.RegularZero.isManifold


theorem contMDiff_inclusion (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) :
    let _ := chartedSpace hn hs hg hr
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A) n
      (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) := by
  let _ := chartedSpace hn hs hg hr
  let _ := isManifold hn hs hg hr
  change ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A) n
    (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A)
  intro x
  let C := Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ
  let c := chart hn hs hg hr x
  have hx : x ∈ c.source := mem_chart_source hn hs hg hr x
  have hc : ContDiffAt ℝ n (fun z => (c.symm z).val) (c x) :=
    (contDiffOn_chart_symm hn hs hg hr x).contDiffAt
      (c.open_target.mem_nhds (c.map_source hx))
  have hh := hc.contMDiffAt.comp x (contMDiffAt_extChartAt (I := 𝓘(ℝ, C)) (n := n) (x := x))
  apply hh.congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds C x] with y hy
  change y.val = (c.symm (c y)).val
  exact (congrArg Subtype.val (c.left_inv hy)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.RegularZero.contMDiff_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.RegularZero.contMDiff_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.RegularZero.contMDiff_inclusion ``Submission.DifferentialGeometry.Manifold.RegularZero.contMDiff_inclusion

end DifferentialGeometry.Manifold.RegularZero
