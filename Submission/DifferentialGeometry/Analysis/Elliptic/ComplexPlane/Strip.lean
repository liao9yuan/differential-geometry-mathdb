import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Analysis


def unitStrip : Set ℂ := {z | z.re ∈ _root_.Set.Icc (0 : ℝ) 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.unitStrip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.unitStrip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.unitStrip ``Submission.DifferentialGeometry.Analysis.unitStrip


def unitSquare : Set ℂ := {z | z.re ∈ _root_.Set.Icc (0 : ℝ) 1 ∧ z.im ∈ _root_.Set.Icc (0 : ℝ) 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.unitSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.unitSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.unitSquare ``Submission.DifferentialGeometry.Analysis.unitSquare


def stripClamp (z : ℂ) : ℂ :=
  Complex.equivRealProdCLM.symm (_root_.Set.projIcc 0 1 zero_le_one z.re, z.im)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.stripClamp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.stripClamp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.stripClamp ``Submission.DifferentialGeometry.Analysis.stripClamp

theorem stripClamp_mem (z : ℂ) : stripClamp z ∈ unitStrip := by
  exact (_root_.Set.projIcc 0 1 zero_le_one z.re).property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.stripClamp_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.stripClamp_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.stripClamp_mem ``Submission.DifferentialGeometry.Analysis.stripClamp_mem

theorem stripClamp_eq_self {z : ℂ} (hz : z ∈ unitStrip) : stripClamp z = z := by
  change Complex.equivRealProdCLM.symm ((_root_.Set.projIcc 0 1 zero_le_one z.re : ℝ), z.im) = z
  rw [_root_.Set.projIcc_of_mem zero_le_one hz]
  exact Complex.equivRealProdCLM.symm_apply_apply z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.stripClamp_eq_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.stripClamp_eq_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.stripClamp_eq_self ``Submission.DifferentialGeometry.Analysis.stripClamp_eq_self

theorem stripClamp_eventually_eq_id {z : ℂ} (hz : z.re ∈ _root_.Set.Ioo (0 : ℝ) 1) :
    stripClamp =ᶠ[𝓝 z] id := by
  filter_upwards [(isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hz] with w hw
  exact stripClamp_eq_self (_root_.Set.Ioo_subset_Icc_self hw)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.stripClamp_eventually_eq_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.stripClamp_eventually_eq_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.stripClamp_eventually_eq_id ``Submission.DifferentialGeometry.Analysis.stripClamp_eventually_eq_id

theorem exists_lipschitz_stripClamp : ∃ C : ℝ≥0, LipschitzWith C stripClamp := by
  have ht := ((LipschitzWith.subtype_val (_root_.Set.Icc (0 : ℝ) 1)).comp
    (LipschitzWith.projIcc (zero_le_one : (0 : ℝ) ≤ 1))).comp
    Complex.reCLM.lipschitz
  exact ⟨_, Complex.equivRealProdCLM.symm.lipschitz.comp (ht.prodMk Complex.imCLM.lipschitz)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_lipschitz_stripClamp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_lipschitz_stripClamp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_lipschitz_stripClamp ``Submission.DifferentialGeometry.Analysis.exists_lipschitz_stripClamp

theorem isCompact_unitSquare : IsCompact unitSquare :=
  Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod _root_.CompactIccSpace.isCompact_Icc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.isCompact_unitSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.isCompact_unitSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.isCompact_unitSquare ``Submission.DifferentialGeometry.Analysis.isCompact_unitSquare

end DifferentialGeometry.Analysis
