import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.BlockAlgebra

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped _root_.BigOperators

variable {Idx : Type*} [Fintype Idx]

def hamiltonBlockHeatProduct
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (LK : Idx -> Idx -> Idx -> Idx -> Real)
    (LP : Idx -> Idx -> Idx -> Real)
    (LM : Idx -> Idx -> Real)
    (DK : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (DP : Idx -> Idx -> Idx -> Idx -> Real)
    (DM : Idx -> Idx -> Idx -> Real)
    (DU : Idx -> Idx -> Idx -> Real)
    (DW : Idx -> Real)
    (LU : Idx -> Idx -> Real)
    (LW : Idx -> Real)
    (U : Idx -> Idx -> Real)
    (W : Idx -> Real) : Real :=
  (∑ a, ∑ b, ∑ c, ∑ d, LK a b c d * U a b * U c d) +
    2 * (∑ a, ∑ b, ∑ c, ∑ d, K a b c d * LU a b * U c d) -
    4 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
      DK e a b c d * DU e a b * U c d) -
    2 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
      K a b c d * DU e a b * DU e c d) +
    2 * (∑ a, ∑ b, ∑ c, LP a b c * U a b * W c) +
    2 * (∑ a, ∑ b, ∑ c, P a b c * LU a b * W c) +
    2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * LW c) -
    4 * (∑ e, ∑ a, ∑ b, ∑ c,
      DP e a b c * DU e a b * W c) -
    4 * (∑ e, ∑ a, ∑ b, ∑ c,
      DP e a b c * U a b * DW e) -
    4 * (∑ e, ∑ a, ∑ b, ∑ c,
      P a b c * DU e a b * DW e) +
    (∑ a, ∑ b, LM a b * W a * W b) +
    (∑ a, ∑ b, M a b * LW a * W b) +
    (∑ a, ∑ b, M a b * W a * LW b) -
    2 * (∑ e, ∑ a, ∑ b, DM e a b * DW e * W b) -
    2 * (∑ e, ∑ a, ∑ b, M a b * DW e * DW e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockHeatProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockHeatProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockHeatProduct ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockHeatProduct

def hamiltonBlockRawProduct
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (LK : Idx -> Idx -> Idx -> Idx -> Real)
    (LP : Idx -> Idx -> Idx -> Real)
    (LM : Idx -> Idx -> Real)
    (DK : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (DP : Idx -> Idx -> Idx -> Idx -> Real)
    (DU : Idx -> Idx -> Idx -> Real)
    (LW : Idx -> Real)
    (U : Idx -> Idx -> Real)
    (W : Idx -> Real) : Real :=
  (∑ a, ∑ b, ∑ c, ∑ d,
      LK a b c d * U a b * U c d) +
    2 * (∑ a, ∑ b, ∑ c,
      LP a b c * U a b * W c) +
    2 * (∑ a, ∑ b, ∑ c,
      P a b c * U a b * LW c) -
    4 * (∑ e, ∑ a, ∑ b, ∑ c,
      DP e a b c * DU e a b * W c) +
    (∑ a, ∑ b, LM a b * W a * W b) +
      2 * (∑ a, ∑ b, M a b * LW a * W b) -
    4 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
      DK e a b c d * DU e a b * U c d) -
    2 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
      K a b c d * DU e a b * DU e c d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawProduct ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawProduct

def hamiltonBlockRawKProduct
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (LK : Idx -> Idx -> Idx -> Idx -> Real)
    (DK : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (DU : Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) : Real :=
  (∑ a, ∑ b, ∑ c, ∑ d,
      LK a b c d * U a b * U c d) -
    4 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
      DK e a b c d * DU e a b * U c d) -
    2 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
      K a b c d * DU e a b * DU e c d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawKProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawKProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawKProduct ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawKProduct

def hamiltonBlockRawPProduct
    (P : Idx -> Idx -> Idx -> Real)
    (LP : Idx -> Idx -> Idx -> Real)
    (DP : Idx -> Idx -> Idx -> Idx -> Real)
    (DU : Idx -> Idx -> Idx -> Real)
    (LW : Idx -> Real)
    (U : Idx -> Idx -> Real)
    (W : Idx -> Real) : Real :=
  2 * (∑ a, ∑ b, ∑ c,
    LP a b c * U a b * W c) +
  2 * (∑ a, ∑ b, ∑ c,
    P a b c * U a b * LW c) -
  4 * (∑ e, ∑ a, ∑ b, ∑ c,
    DP e a b c * DU e a b * W c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawPProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawPProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawPProduct ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawPProduct

def hamiltonBlockRawMProduct
    (M : Idx -> Idx -> Real)
    (LM : Idx -> Idx -> Real)
    (LW : Idx -> Real)
    (W : Idx -> Real) : Real :=
  (∑ a, ∑ b, LM a b * W a * W b) +
    2 * (∑ a, ∑ b, M a b * LW a * W b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawMProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawMProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawMProduct ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawMProduct

theorem hamiltonBlockRawProduct_eq_split
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (LK : Idx -> Idx -> Idx -> Idx -> Real)
    (LP : Idx -> Idx -> Idx -> Real)
    (LM : Idx -> Idx -> Real)
    (DK : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (DP : Idx -> Idx -> Idx -> Idx -> Real)
    (DU : Idx -> Idx -> Idx -> Real)
    (LW : Idx -> Real)
    (U : Idx -> Idx -> Real)
    (W : Idx -> Real) :
    hamiltonBlockRawProduct K P M LK LP LM DK DP DU LW U W =
      hamiltonBlockRawKProduct K LK DK DU U +
        hamiltonBlockRawPProduct P LP DP DU LW U W +
        hamiltonBlockRawMProduct M LM LW W := by
  unfold hamiltonBlockRawProduct hamiltonBlockRawKProduct
    hamiltonBlockRawPProduct hamiltonBlockRawMProduct
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawProduct_eq_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawProduct_eq_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawProduct_eq_split ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockRawProduct_eq_split

theorem hamiltonBlock_heat_product_eq_raw
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (LK : Idx -> Idx -> Idx -> Idx -> Real)
    (LP : Idx -> Idx -> Idx -> Real)
    (LM : Idx -> Idx -> Real)
    (DK : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (DP : Idx -> Idx -> Idx -> Idx -> Real)
    (DM : Idx -> Idx -> Idx -> Real)
    (DU : Idx -> Idx -> Idx -> Real)
    (DW : Idx -> Real)
    (LU : Idx -> Idx -> Real)
    (LW : Idx -> Real)
    (U : Idx -> Idx -> Real)
    (W : Idx -> Real)
    (hDW : ∀ e, DW e = 0)
    (hLU : ∀ a b, LU a b = 0)
    (hM : ∀ a b, M a b = M b a) :
    hamiltonBlockHeatProduct K P M LK LP LM DK DP DM DU DW LU LW U W =
      hamiltonBlockRawProduct K P M LK LP LM DK DP DU LW U W := by
  simp only [hamiltonBlockHeatProduct, hamiltonBlockRawProduct, hDW, hLU,
    _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
  have hswap :
      (∑ a, ∑ b, M a b * W a * LW b) =
        ∑ a, ∑ b, M a b * LW a * W b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hM]
    ring
  rw [hswap]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_heat_product_eq_raw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_heat_product_eq_raw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_heat_product_eq_raw ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_heat_product_eq_raw

theorem hamiltonBlock_heat_product_eq_split
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (LK : Idx -> Idx -> Idx -> Idx -> Real)
    (LP : Idx -> Idx -> Idx -> Real)
    (LM : Idx -> Idx -> Real)
    (DK : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (DP : Idx -> Idx -> Idx -> Idx -> Real)
    (DM : Idx -> Idx -> Idx -> Real)
    (DU : Idx -> Idx -> Idx -> Real)
    (DW : Idx -> Real)
    (LU : Idx -> Idx -> Real)
    (LW : Idx -> Real)
    (U : Idx -> Idx -> Real)
    (W : Idx -> Real)
    (hDW : ∀ e, DW e = 0)
    (hLU : ∀ a b, LU a b = 0)
    (hM : ∀ a b, M a b = M b a) :
    hamiltonBlockHeatProduct K P M LK LP LM DK DP DM DU DW LU LW U W =
      hamiltonBlockRawKProduct K LK DK DU U +
        hamiltonBlockRawPProduct P LP DP DU LW U W +
        hamiltonBlockRawMProduct M LM LW W := by
  rw [hamiltonBlock_heat_product_eq_raw K P M LK LP LM DK DP DM DU DW LU LW U W
    hDW hLU hM, hamiltonBlockRawProduct_eq_split]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_heat_product_eq_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_heat_product_eq_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_heat_product_eq_split ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_heat_product_eq_split

def hamiltonBlockSigmaSquare
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) : Real :=
  ∑ a, ∑ b, (hamiltonBlockSigma K P U W a b) ^ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockSigmaSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockSigmaSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockSigmaSquare ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockSigmaSquare

def hamiltonBlockSigmaSquareExpanded
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) : Real :=
  ∑ a, ∑ b,
    ((∑ c, P a b c * W c) ^ 2 +
      2 * (∑ c, P a b c * W c) * (∑ d, ∑ e, K a b d e * U d e) +
      (∑ c, ∑ d, K a b c d * U c d) ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockSigmaSquareExpanded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlockSigmaSquareExpanded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlockSigmaSquareExpanded ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlockSigmaSquareExpanded

theorem hamiltonBlock_sigma_square_expand
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) :
    hamiltonBlockSigmaSquare K P U W =
      hamiltonBlockSigmaSquareExpanded K P U W := by
  unfold hamiltonBlockSigmaSquare hamiltonBlockSigma
    hamiltonBlockSigmaSquareExpanded
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_sigma_square_expand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_sigma_square_expand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_sigma_square_expand ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonBlock_sigma_square_expand

end DifferentialGeometry.PDE.RicciFlow
