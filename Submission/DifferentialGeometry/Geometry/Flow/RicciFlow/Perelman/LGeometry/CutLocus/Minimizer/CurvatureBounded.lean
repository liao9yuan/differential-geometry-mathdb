import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] in
omit [SigmaCompactSpace M] in
theorem lMinimizingVector_min_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (hmin : (Z, tau) ∈ lMinDomain S T x)
    (hreg : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ _root_.Set.Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (delta : Real → M)
    (hdelta : ContMDiff (modelWithCornersSelf Real Real) I 1 delta)
    (hd0 : delta 0 = lRegularizedCurve S T x Z 0)
    (hdt : delta (Real.sqrt tau) =
      lRegularizedCurve S T x Z (Real.sqrt tau)) :
    lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) ≤
      lRegularizedAction S T delta 0 (Real.sqrt tau) := by
  have hvec := (mem_lMinDomain S T x Z tau).1 hmin
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hmin
  have hsqrt : 0 ≤ Real.sqrt tau := Real.sqrt_nonneg tau
  have hsq : (Real.sqrt tau) ^ 2 = tau := Real.sq_sqrt htau.le
  have hregSq : _root_.Set.Icc (T - (Real.sqrt tau) ^ 2) T ⊆ D.regular := by
    simpa only [hsq] using hreg
  have hRmSq : ∀ q ∈ _root_.Set.Icc (T - (Real.sqrt tau) ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
    simpa only [hsq] using hRm
  have hcost : lRegularizedAction S T (lRegularizedCurve S T x Z) 0
      (Real.sqrt tau) = lRegularizedCostC1 S T 0 (Real.sqrt tau) x
        (lRegularizedCurve S T x Z (Real.sqrt tau)) := by
    calc
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) =
          lLength S T (fun r : Real ↦ lExp S T x Z r) 0 tau := by
        change _ = lLength S T
          (fun r : Real ↦ lRegularizedCurve S T x Z (Real.sqrt r)) 0 tau
        rw [show (fun r : Real ↦ lRegularizedCurve S T x Z (Real.sqrt r)) =
          squareRootReparametrization (lRegularizedCurve S T x Z) by rfl]
        exact (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T (lRegularizedCurve S T x Z) tau
          htau.le).symm
      _ = lCost S T x (lExp S T x Z tau) tau := hvec.2
      _ = lRegularizedCostC1 S T 0 (Real.sqrt tau) x
          (lExp S T x Z tau) :=
        lCost_eq_regularity (I := I) S T x (lExp S T x Z tau) tau htau.le
      _ = lRegularizedCostC1 S T 0 (Real.sqrt tau) x
          (lRegularizedCurve S T x Z (Real.sqrt tau)) := by rfl
  have hbdd := lRegularizedCosts_bdd_rm (I := I) S hS K T 0
    (Real.sqrt tau) (by norm_num) hsqrt hregSq hRmSq x
    (lRegularizedCurve S T x Z (Real.sqrt tau))
  rw [hcost]
  exact lRegularizedCostC1_le_bdd (I := I) S T 0 (Real.sqrt tau) x
    (lRegularizedCurve S T x Z (Real.sqrt tau)) hbdd delta hdelta
    (hd0.trans (by simp only [lRegularizedCurve_zero])) hdt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinimizingVector_min_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lMinimizingVector_min_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinimizingVector_min_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lMinimizingVector_min_rm

end DifferentialGeometry.PDE.RicciFlow.Perelman
