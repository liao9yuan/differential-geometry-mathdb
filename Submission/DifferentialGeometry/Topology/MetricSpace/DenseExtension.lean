import Mathlib.Topology.Instances.ENNReal.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.NNReal _root_.ENNReal

open _root_.DenseRange in
theorem DenseRange.exists_lipschitz_extension
    {A X Y : Type*} [PseudoEMetricSpace X] [EMetricSpace Y] [CompleteSpace Y]
    {i : A → X} (hi : DenseRange i) (f : A → Y) {K : ℝ≥0}
    (hf : ∀ a b, _root_.EDist.edist (f a) (f b) ≤ K * _root_.EDist.edist (i a) (i b)) :
    ∃ g : X → Y, LipschitzWith K g ∧ ∀ a, g (i a) = f a := by
  let : PseudoEMetricSpace A := PseudoEMetricSpace.induced i inferInstance
  have hiso : Isometry i := fun _ _ => rfl
  have hfl : LipschitzWith K f := hf
  let g := (hiso.isUniformInducing.isDenseInducing hi).extend f
  have hg : Continuous g :=
    (uniformContinuous_uniformly_extend hiso.isUniformInducing hi
      hfl.uniformContinuous).continuous
  have heq : ∀ a, g (i a) = f a :=
    uniformly_extend_of_ind hiso.isUniformInducing hi hfl.uniformContinuous
  refine ⟨g, ?_, heq⟩
  intro x y
  apply hi.induction_on₂ (p := fun x y => _root_.EDist.edist (g x) (g y) ≤ K * _root_.EDist.edist x y) ?_ ?_ x y
  · exact isClosed_le (by fun_prop)
      ((ENNReal.continuous_const_mul (by simp)).comp (by fun_prop))
  · intro a b
    rw [heq, heq]
    exact hf a b

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DenseRange
  let env ← Lean.getEnv
  if env.contains `DenseRange.exists_lipschitz_extension then
    throwError "Refusing to shadow existing declaration DenseRange.exists_lipschitz_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DenseRange.exists_lipschitz_extension ``Submission.DenseRange.exists_lipschitz_extension

open _root_.DenseRange in
theorem DenseRange.restrictPreimage_of_isOpen
    {A X : Type*} [TopologicalSpace X] {i : A → X} (hi : DenseRange i)
    {U : Set X} (hU : IsOpen U) : DenseRange (U.restrictPreimage i) := by
  rw [denseRange_iff_closure_range, Set.range_restrictPreimage,
    ← hU.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val, hi.closure_range]
  exact Set.preimage_univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DenseRange.restrictPreimage_of_isOpen then
    throwError "Refusing to shadow existing declaration DenseRange.restrictPreimage_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DenseRange.restrictPreimage_of_isOpen ``Submission.DenseRange.restrictPreimage_of_isOpen
