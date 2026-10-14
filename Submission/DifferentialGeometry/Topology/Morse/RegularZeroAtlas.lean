import Submission.DifferentialGeometry.Topology.Morse.RegularZeroCoordinates
import Submission.DifferentialGeometry.Topology.Manifold.RegularZero.Atlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Morse
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {g : A → B} {S : Set A}


def regularZeroChart (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    OpenPartialHomeomorph {y : A // y ∈ S ∧ g y = 0}
      (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) :=
  DifferentialGeometry.Manifold.RegularZero.chart one_ne_zero hs hg hr x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.regularZeroChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.regularZeroChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.regularZeroChart ``Submission.DifferentialGeometry.Morse.regularZeroChart


theorem mem_regularZeroChart_source (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    x ∈ (regularZeroChart hs hg hr x).source :=
  DifferentialGeometry.Manifold.RegularZero.mem_chart_source one_ne_zero hs hg hr x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.mem_regularZeroChart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.mem_regularZeroChart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.mem_regularZeroChart_source ``Submission.DifferentialGeometry.Morse.mem_regularZeroChart_source


theorem regularZeroChart_center (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    regularZeroChart hs hg hr x x = 0 :=
  DifferentialGeometry.Manifold.RegularZero.chart_center one_ne_zero hs hg hr x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.regularZeroChart_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.regularZeroChart_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.regularZeroChart_center ``Submission.DifferentialGeometry.Morse.regularZeroChart_center


theorem contDiffOn_regularZeroChart_symm (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    ContDiffOn ℝ 1 (fun z => ((regularZeroChart hs hg hr x).symm z).val)
      (regularZeroChart hs hg hr x).target :=
  DifferentialGeometry.Manifold.RegularZero.contDiffOn_chart_symm one_ne_zero hs hg hr x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.contDiffOn_regularZeroChart_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.contDiffOn_regularZeroChart_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.contDiffOn_regularZeroChart_symm ``Submission.DifferentialGeometry.Morse.contDiffOn_regularZeroChart_symm


theorem contDiffOn_regularZeroChart_transition (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x))
    (x y : {z : A // z ∈ S ∧ g z = 0}) :
    ContDiffOn ℝ 1 ((regularZeroChart hs hg hr y) ∘ (regularZeroChart hs hg hr x).symm)
      ((regularZeroChart hs hg hr x).target ∩
        (regularZeroChart hs hg hr x).symm ⁻¹' (regularZeroChart hs hg hr y).source) :=
  DifferentialGeometry.Manifold.RegularZero.contDiffOn_chart_transition one_ne_zero hs hg hr x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.contDiffOn_regularZeroChart_transition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.contDiffOn_regularZeroChart_transition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.contDiffOn_regularZeroChart_transition ``Submission.DifferentialGeometry.Morse.contDiffOn_regularZeroChart_transition


@[reducible]
def regularZeroChartedSpace (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) :
    ChartedSpace (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ)
      {y : A // y ∈ S ∧ g y = 0} :=
  DifferentialGeometry.Manifold.RegularZero.chartedSpace one_ne_zero hs hg hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.regularZeroChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.regularZeroChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.regularZeroChartedSpace ``Submission.DifferentialGeometry.Morse.regularZeroChartedSpace


theorem regularZeroIsManifold (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) :
    let _ := regularZeroChartedSpace hs hg hr
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 1
      {y : A // y ∈ S ∧ g y = 0} :=
  DifferentialGeometry.Manifold.RegularZero.isManifold one_ne_zero hs hg hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.regularZeroIsManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.regularZeroIsManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.regularZeroIsManifold ``Submission.DifferentialGeometry.Morse.regularZeroIsManifold


theorem contMDiff_regularZero_inclusion (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) :
    let _ := regularZeroChartedSpace hs hg hr
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A) 1
      (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) :=
  DifferentialGeometry.Manifold.RegularZero.contMDiff_inclusion one_ne_zero hs hg hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.contMDiff_regularZero_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.contMDiff_regularZero_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.contMDiff_regularZero_inclusion ``Submission.DifferentialGeometry.Morse.contMDiff_regularZero_inclusion

end DifferentialGeometry.Morse
