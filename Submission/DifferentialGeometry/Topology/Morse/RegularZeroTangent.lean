import Submission.DifferentialGeometry.Topology.Morse.RegularZeroAtlas
import Submission.DifferentialGeometry.Topology.Manifold.RegularZero.Tangent

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
variable {A B C : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]
  {S : Set A}


theorem injective_fderiv_zeroFiberChart_symm (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) 1)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΦS : Φ.source ⊆ S)
    (a : {y : A // y ∈ S ∧ g y = 0}) {z : C}
    (hz : z ∈ (zeroFiberChart g Φ hΦ hΦS a).target) :
    Injective (fderiv ℝ (fun u => ((zeroFiberChart g Φ hΦ hΦS a).symm u).val) z) :=
  DifferentialGeometry.Manifold.RegularZero.injective_fderiv_fiberChart_symm one_ne_zero g Φ hΦ hΦS a hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.injective_fderiv_zeroFiberChart_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.injective_fderiv_zeroFiberChart_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.injective_fderiv_zeroFiberChart_symm ``Submission.DifferentialGeometry.Morse.injective_fderiv_zeroFiberChart_symm

section FiniteDimension
variable [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] {g : A → B}


theorem mfderiv_regularZero_inclusion (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    let _ := regularZeroChartedSpace hs hg hr
    (show (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) →L[ℝ] A from
      mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A)
        (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) x) =
      fderiv ℝ (fun u => ((regularZeroChart hs hg hr x).symm u).val)
        (regularZeroChart hs hg hr x x) :=
  DifferentialGeometry.Manifold.RegularZero.mfderiv_inclusion one_ne_zero hs hg hr x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.mfderiv_regularZero_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.mfderiv_regularZero_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.mfderiv_regularZero_inclusion ``Submission.DifferentialGeometry.Morse.mfderiv_regularZero_inclusion


theorem injective_mfderiv_regularZero_inclusion (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    let _ := regularZeroChartedSpace hs hg hr
    _root_.Function.Injective (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A)
      (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) x) :=
  DifferentialGeometry.Manifold.RegularZero.injective_mfderiv_inclusion one_ne_zero hs hg hr x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.injective_mfderiv_regularZero_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.injective_mfderiv_regularZero_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.injective_mfderiv_regularZero_inclusion ``Submission.DifferentialGeometry.Morse.injective_mfderiv_regularZero_inclusion


theorem range_mfderiv_regularZero_inclusion (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → _root_.Function.Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    let _ := regularZeroChartedSpace hs hg hr
    LinearMap.range (show (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) →ₗ[ℝ] A from
      (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A)
        (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) x).toLinearMap) =
      (fderiv ℝ g x.val).ker :=
  DifferentialGeometry.Manifold.RegularZero.range_mfderiv_inclusion one_ne_zero hs hg hr x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.range_mfderiv_regularZero_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.range_mfderiv_regularZero_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.range_mfderiv_regularZero_inclusion ``Submission.DifferentialGeometry.Morse.range_mfderiv_regularZero_inclusion

end FiniteDimension
end DifferentialGeometry.Morse
