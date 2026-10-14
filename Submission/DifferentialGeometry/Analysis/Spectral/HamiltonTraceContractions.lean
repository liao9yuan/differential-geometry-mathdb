import Submission.DifferentialGeometry.Analysis.Spectral.HamiltonGram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Spectral

open scoped _root_.BigOperators

def hamiltonTraceWeight {ι : Type*} [DecidableEq ι] (r a : ι) : Real :=
  if a = r then 1 else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonTraceWeight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonTraceWeight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonTraceWeight ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonTraceWeight

def hamiltonTraceWedge {ι : Type*} [DecidableEq ι]
    (v : ι → Real) (r a b : ι) : Real :=
  (1 / 2 : Real) *
    (v a * hamiltonTraceWeight r b - v b * hamiltonTraceWeight r a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonTraceWedge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonTraceWedge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonTraceWedge ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonTraceWedge

def hamiltonRicciContraction {ι : Type*} [Fintype ι]
    (R : ι → ι → ι → ι → Real) (a b : ι) : Real :=
  ∑ r, R r a b r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonRicciContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonRicciContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonRicciContraction ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonRicciContraction

private theorem sum_reorder_rpq
    {ι : Type*} [Fintype ι] (f : ι → ι → ι → Real) :
    (∑ r, ∑ p, ∑ q, f r p q) = ∑ p, ∑ q, ∑ r, f r p q := by
  calc
    (∑ r, ∑ p, ∑ q, f r p q) = ∑ p, ∑ r, ∑ q, f r p q := by
      rw [Finset.sum_comm]
    _ = ∑ p, ∑ q, ∑ r, f r p q := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.sum_reorder_rpq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.sum_reorder_rpq target :: scope.openDecls } }

theorem hamilton_trace_M_contraction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → Real) :
    (∑ r, ∑ a, ∑ b, M a b * hamiltonTraceWeight r a * hamiltonTraceWeight r b) =
      ∑ a, M a a := by
  classical
  simp [hamiltonTraceWeight]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamilton_trace_M_contraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamilton_trace_M_contraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamilton_trace_M_contraction ``Submission.DifferentialGeometry.Analysis.Spectral.hamilton_trace_M_contraction

theorem hamilton_trace_P_contraction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → ι → ι → Real) (v dR : ι → Real)
    (hFirst : ∀ a, (∑ c, P c a c) = -(1 / 2 : Real) * dR a)
    (hSecond : ∀ a, (∑ c, P a c c) = (1 / 2 : Real) * dR a) :
    (∑ r, ∑ p, ∑ i, ∑ j,
        2 * P p i j * hamiltonTraceWedge v r p i * hamiltonTraceWeight r j) =
      ∑ a, dR a * v a := by
  classical
  simp [hamiltonTraceWedge, hamiltonTraceWeight, mul_sub,
    Finset.sum_sub_distrib, mul_ite]
  ring_nf
  calc
    (∑ x, ∑ x_1, P x_1 x x * v x_1) -
        ∑ x, ∑ x_1, P x x_1 x * v x_1 =
      (∑ x_1, (∑ x, P x_1 x x) * v x_1) -
        ∑ x_1, (∑ x, P x x_1 x) * v x_1 := by
          congr 1
          · calc
              (∑ x, ∑ x_1, P x_1 x x * v x_1) =
                  ∑ x_1, ∑ x, P x_1 x x * v x_1 := Finset.sum_comm
              _ = ∑ x_1, (∑ x, P x_1 x x) * v x_1 := by
                refine Finset.sum_congr rfl fun x_1 _ => ?_
                rw [Finset.sum_mul]
          · calc
              (∑ x, ∑ x_1, P x x_1 x * v x_1) =
                  ∑ x_1, ∑ x, P x x_1 x * v x_1 := Finset.sum_comm
              _ = ∑ x_1, (∑ x, P x x_1 x) * v x_1 := by
                refine Finset.sum_congr rfl fun x_1 _ => ?_
                rw [Finset.sum_mul]
    _ = ∑ x, dR x * v x := by
      simp_rw [hSecond, hFirst]
      have hsum (c : Real) :
          (∑ x, c * dR x * v x) = c * (∑ x, dR x * v x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      have hsum' (c : Real) :
          (∑ x, c * dR x * v x) = c * (∑ x, dR x * v x) := hsum c
      rw [hsum' (1 / 2 : Real), hsum' (-(1 / 2 : Real))]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamilton_trace_P_contraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamilton_trace_P_contraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamilton_trace_P_contraction ``Submission.DifferentialGeometry.Analysis.Spectral.hamilton_trace_P_contraction

theorem hamilton_trace_curvature_contraction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → ι → ι → ι → Real) (v : ι → Real)
    (hFirst : ∀ a b c d, R a b c d = -R b a c d)
    (hLast : ∀ a b c d, R a b c d = -R a b d c)
    (hPair : ∀ a b c d, R a b c d = R c d a b) :
    (∑ r, ∑ p, ∑ i, ∑ q, ∑ j,
        R p i j q * hamiltonTraceWedge v r p i * hamiltonTraceWedge v r q j) =
      ∑ a, ∑ b, hamiltonRicciContraction R a b * v a * v b := by
  classical
  simp [hamiltonTraceWedge, hamiltonTraceWeight, hamiltonRicciContraction,
    mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, ite_mul]
  ring_nf
  have hRicSymm (a b : ι) :
      (∑ r, R r a b r) = ∑ r, R r b a r := by
    calc
      (∑ r, R r a b r) = ∑ r, R b r r a := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hPair]
      _ = ∑ r, R r b a r := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hLast, hFirst]
        ring
  have hpack (f : ι → ι → ι → Real) :
      (∑ r, ∑ p, ∑ q, f r p q * v p * v q) =
        ∑ p, ∑ q, (∑ r, f r p q) * v p * v q := by
    rw [sum_reorder_rpq]
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    calc
      (∑ r, f r p q * v p * v q) =
          (∑ r, f r p q * v p) * v q := by rw [Finset.sum_mul]
      _ = ((∑ r, f r p q) * v p) * v q := by rw [← Finset.sum_mul]
      _ = (∑ r, f r p q) * v p * v q := by ring
  have hA :
      (∑ r, ∑ p, ∑ q, R p r r q * v p * v q) =
        ∑ p, ∑ q, (∑ r, R r p q r) * v p * v q := by
    rw [hpack]
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    have hsumR : (∑ r, R p r r q) = ∑ r, R r p q r := by
      calc
        (∑ r, R p r r q) = ∑ r, (-R p r q r) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [hLast]
        _ = ∑ r, R r q p r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [hPair, hFirst]
          ring
        _ = ∑ r, R r p q r := hRicSymm q p
    rw [hsumR]
  have hB :
      (∑ r, ∑ p, ∑ q, R r p r q * v p * v q) =
        -(∑ p, ∑ q, (∑ r, R r p q r) * v p * v q) := by
    calc
      (∑ r, ∑ p, ∑ q, R r p r q * v p * v q) =
          ∑ r, ∑ p, ∑ q, (-R r p q r) * v p * v q := by
            refine Finset.sum_congr rfl fun r _ => ?_
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [hLast]
      _ = -(∑ r, ∑ p, ∑ q, R r p q r * v p * v q) := by
            simp
      _ = -(∑ p, ∑ q, (∑ r, R r p q r) * v p * v q) := by
            rw [hpack]
  have hC :
      (∑ r, ∑ p, ∑ q, R p r q r * v p * v q) =
        -(∑ p, ∑ q, (∑ r, R r p q r) * v p * v q) := by
    calc
      (∑ r, ∑ p, ∑ q, R p r q r * v p * v q) =
          ∑ p, ∑ q, (∑ r, R p r q r) * v p * v q :=
        hpack (fun r p q => R p r q r)
      _ = ∑ p, ∑ q, (-(∑ r, R r q p r)) * v p * v q := by
        refine Finset.sum_congr rfl fun p _ => ?_
        refine Finset.sum_congr rfl fun q _ => ?_
        have hsumR : (∑ r, R p r q r) = -(∑ r, R r q p r) := by
          calc
            (∑ r, R p r q r) = ∑ r, (-R r q p r) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              calc
                R p r q r = R q r p r := hPair p r q r
                _ = -R r q p r := hFirst q r p r
            _ = -(∑ r, R r q p r) := by simp
        rw [hsumR]
      _ = -(∑ p, ∑ q, (∑ r, R r p q r) * v p * v q) := by
        simp only [neg_mul, Finset.sum_neg_distrib]
        have hswap :
            (∑ p : ι, ∑ q : ι, (∑ r : ι, R r q p r) * v p * v q) =
              ∑ p : ι, ∑ q : ι, (∑ r : ι, R r p q r) * v p * v q := by
          calc
            (∑ p : ι, ∑ q : ι, (∑ r : ι, R r q p r) * v p * v q) =
                ∑ q : ι, ∑ p : ι, (∑ r : ι, R r q p r) * v p * v q := by
                  rw [Finset.sum_comm]
            _ = ∑ q : ι, ∑ p : ι, (∑ r : ι, R r p q r) * v p * v q := by
                  refine Finset.sum_congr rfl fun q _ => ?_
                  refine Finset.sum_congr rfl fun p _ => ?_
                  rw [hRicSymm]
            _ = ∑ p : ι, ∑ q : ι, (∑ r : ι, R r p q r) * v p * v q := by
                  rw [Finset.sum_comm]
        exact congrArg Neg.neg hswap
  have hD :
      (∑ r, ∑ p, ∑ q, R r p q r * v p * v q) =
        ∑ p, ∑ q, (∑ r, R r p q r) * v p * v q :=
    hpack (fun r p q => R r p q r)
  have hquarter (f : ι → ι → ι → Real) :
      (∑ r, ∑ p, ∑ q, f r p q * v p * v q * (1 / 4 : Real)) =
        (∑ r, ∑ p, ∑ q, f r p q * v p * v q) * (1 / 4 : Real) := by
    calc
      (∑ r, ∑ p, ∑ q, f r p q * v p * v q * (1 / 4 : Real)) =
          ∑ r, ∑ p, (∑ q, f r p q * v p * v q) * (1 / 4 : Real) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.sum_mul]
      _ = ∑ r, (∑ p, ∑ q, f r p q * v p * v q) * (1 / 4 : Real) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.sum_mul]
      _ = (∑ r, ∑ p, ∑ q, f r p q * v p * v q) * (1 / 4 : Real) := by
            rw [Finset.sum_mul]
  rw [hquarter, hquarter, hquarter, hquarter, hA, hB, hC, hD]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamilton_trace_curvature_contraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamilton_trace_curvature_contraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamilton_trace_curvature_contraction ``Submission.DifferentialGeometry.Analysis.Spectral.hamilton_trace_curvature_contraction

end DifferentialGeometry.Analysis.Spectral
