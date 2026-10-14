import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.RegularizedExistence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs

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

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
theorem lCost_eq_regularity
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x y : M) (tau : Real) (htau : 0 ≤ tau) :
    lCost S T x y tau =
      lRegularizedCostC1 S T 0 (Real.sqrt tau) x y := by
  unfold lCost lRegularizedCostC1
  apply congrArg _root_.InfSet.sInf
  ext r
  constructor
  · rintro ⟨alpha, halpha, h0, ht, hr⟩
    refine ⟨alpha, halpha, h0, ht, ?_⟩
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T alpha tau htau] at hr
    exact hr
  · rintro ⟨alpha, halpha, h0, ht, hr⟩
    refine ⟨alpha, halpha, h0, ht, ?_⟩
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T alpha tau htau]
    exact hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_eq_regularity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_eq_regularity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_eq_regularity ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_eq_regularity

theorem exists_lMinimizer
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t0 t1 tau : Real) (htau : 0 < tau)
    (htime : _root_.Set.Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ _root_.Set.Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ _root_.Set.Icc t0 t1)
    (x y : M) (alpha0 : Real → M)
    (halpha0 : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha0)
    (h00 : alpha0 0 = x) (h0t : alpha0 (Real.sqrt tau) = y)
    (hreg : ∀ s ∈ _root_.Set.Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ D.regular) :
    ∃ (alpha : Real → M) (Z : TangentSpace I x),
      IsLRegularizedCurveOn S T alpha (_root_.Set.Icc (0 : Real) (Real.sqrt tau)) x Z ∧
        Set.EqOn (lRegularizedCurve S T x Z) alpha
            (_root_.Set.Icc (0 : Real) (Real.sqrt tau)) ∧
          (Z, tau) ∈ lExpPosDom S T x ∧
            lExp S T x Z tau = y ∧
              alpha (Real.sqrt tau) = y ∧
              lLength S T (squareRootReparametrization alpha) 0 tau = lCost S T x y tau ∧
              ∀ delta : Real → M,
                ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
                delta 0 = x → delta (Real.sqrt tau) = y →
                lLength S T (squareRootReparametrization alpha) 0 tau ≤
                  lLength S T (squareRootReparametrization delta) 0 tau := by
  have hsqrt : 0 < Real.sqrt tau := Real.sqrt_pos.2 htau
  obtain ⟨alpha, Z, hcurve, hbDom, hmax, hend, hcost, hmin⟩ :=
    exists_lRegularizedMinOn (I := I) S hS T t0 t1 (Real.sqrt tau) hsqrt
      htime hback x y alpha0 halpha0 h00 h0t hreg
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    (mem_lExpPosDom S T x Z tau).2 ⟨htau, htau.le, hbDom⟩
  have hExp : lExp S T x Z tau = y := by
    have heq := hmax ⟨Real.sqrt_nonneg tau, le_rfl⟩
    have heq' : lExp S T x Z tau = alpha (Real.sqrt tau) := by
      simpa only [lExp] using heq
    exact heq'.trans hend
  refine ⟨alpha, Z, hcurve, hmax, hdom, hExp, hend, ?_, ?_⟩
  · calc
      lLength S T (squareRootReparametrization alpha) 0 tau =
          lRegularizedAction S T alpha 0 (Real.sqrt tau) :=
        lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T alpha tau htau.le
      _ = lRegularizedCostC1 S T 0 (Real.sqrt tau) x y := hcost
      _ = lCost S T x y tau :=
        (lCost_eq_regularity (I := I) S T x y tau htau.le).symm
  · intro delta hdelta hd0 hdt
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T alpha tau htau.le,
      lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T delta tau htau.le]
    exact hmin delta hdelta hd0 hdt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lMinimizer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lMinimizer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lMinimizer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lMinimizer

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
