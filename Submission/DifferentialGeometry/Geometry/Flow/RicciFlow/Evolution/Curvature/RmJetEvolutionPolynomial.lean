import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.JetPolynomials
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Tensor

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Filter _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.BigOperators

variable {n : ℕ}

def curvatureJetTraceSlots (i j : Fin n) (slots : Fin 4 → Fin n) :
    Fin (4 + 2) → Fin n :=
  Fin.cases i (Fin.cases j slots)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetTraceSlots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetTraceSlots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetTraceSlots ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetTraceSlots

def curvatureJetRmVar (N : ℕ) (slots : Fin 4 → Fin n) :
    CurvatureJetPolynomialVariable n N :=
  Sum.inr ⟨⟨0, Nat.succ_pos N⟩, slots⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRmVar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRmVar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRmVar ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRmVar

def curvatureJetNabla2Var (slots : Fin (4 + 2) → Fin n) :
    CurvatureJetPolynomialVariable n 2 :=
  Sum.inr ⟨⟨2, by decide⟩, slots⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetNabla2Var then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetNabla2Var"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetNabla2Var ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetNabla2Var

def curvatureJetRicciPoly (N : ℕ) (i j : Fin n) :
    MvPolynomial (CurvatureJetPolynomialVariable n N) ℝ :=
  ∑ a : Fin n, ∑ c : Fin n,
    MvPolynomial.X (Sum.inl (a, c)) *
      MvPolynomial.X (curvatureJetRmVar (n := n) N (slots4 a i j c))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRicciPoly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRicciPoly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRicciPoly ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRicciPoly

def curvatureJetRoughLapPoly (slots : Fin 4 → Fin n) :
    MvPolynomial (CurvatureJetPolynomialVariable n 2) ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    MvPolynomial.X (Sum.inl (i, j)) *
      MvPolynomial.X (curvatureJetNabla2Var (n := n)
        (curvatureJetTraceSlots (n := n) i j slots))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRoughLapPoly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRoughLapPoly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRoughLapPoly ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRoughLapPoly

def curvatureJetQuadraticPoly (slots : Fin 4 → Fin n) :
    MvPolynomial (CurvatureJetPolynomialVariable n 2) ℝ :=
  (∑ f : Fin n, ∑ r : Fin n, ∑ e : Fin n, ∑ q : Fin n,
      MvPolynomial.X (Sum.inl (f, r)) * MvPolynomial.X (Sum.inl (e, q)) *
        MvPolynomial.X (curvatureJetRmVar (n := n) 2 ![slots 0, e, slots 1, f]) *
        MvPolynomial.X (curvatureJetRmVar (n := n) 2 ![slots 2, q, slots 3, r])) -
    (∑ f : Fin n, ∑ r : Fin n, ∑ e : Fin n, ∑ q : Fin n,
      MvPolynomial.X (Sum.inl (f, r)) * MvPolynomial.X (Sum.inl (e, q)) *
        MvPolynomial.X (curvatureJetRmVar (n := n) 2 ![slots 0, e, slots 1, f]) *
        MvPolynomial.X (curvatureJetRmVar (n := n) 2 ![slots 3, q, slots 2, r])) +
    (∑ f : Fin n, ∑ r : Fin n, ∑ e : Fin n, ∑ q : Fin n,
      MvPolynomial.X (Sum.inl (f, r)) * MvPolynomial.X (Sum.inl (e, q)) *
        MvPolynomial.X (curvatureJetRmVar (n := n) 2 ![slots 0, e, slots 2, f]) *
        MvPolynomial.X (curvatureJetRmVar (n := n) 2 ![slots 1, q, slots 3, r])) -
    (∑ f : Fin n, ∑ r : Fin n, ∑ e : Fin n, ∑ q : Fin n,
      MvPolynomial.X (Sum.inl (f, r)) * MvPolynomial.X (Sum.inl (e, q)) *
        MvPolynomial.X (curvatureJetRmVar (n := n) 2 ![slots 0, e, slots 3, f]) *
        MvPolynomial.X (curvatureJetRmVar (n := n) 2 ![slots 1, q, slots 2, r]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetQuadraticPoly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetQuadraticPoly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetQuadraticPoly ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetQuadraticPoly

def curvatureJetDriftPoly (slots : Fin 4 → Fin n) :
    MvPolynomial (CurvatureJetPolynomialVariable n 2) ℝ :=
  (∑ p : Fin n, (∑ a : Fin n,
        MvPolynomial.X (Sum.inl (p, a)) * curvatureJetRicciPoly (n := n) 2 (slots 0) a) *
      MvPolynomial.X (curvatureJetRmVar (n := n) 2 (Function.update slots 0 p))) +
  (∑ p : Fin n, (∑ a : Fin n,
        MvPolynomial.X (Sum.inl (p, a)) * curvatureJetRicciPoly (n := n) 2 (slots 1) a) *
      MvPolynomial.X (curvatureJetRmVar (n := n) 2 (Function.update slots 1 p))) +
  (∑ p : Fin n, (∑ a : Fin n,
        MvPolynomial.X (Sum.inl (p, a)) * curvatureJetRicciPoly (n := n) 2 (slots 2) a) *
      MvPolynomial.X (curvatureJetRmVar (n := n) 2 (Function.update slots 2 p))) +
  (∑ p : Fin n, (∑ a : Fin n,
        MvPolynomial.X (Sum.inl (p, a)) * curvatureJetRicciPoly (n := n) 2 (slots 3) a) *
      MvPolynomial.X (curvatureJetRmVar (n := n) 2 (Function.update slots 3 p)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetDriftPoly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetDriftPoly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetDriftPoly ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetDriftPoly

def curvatureJetRmEvolutionPoly (slots : Fin 4 → Fin n) :
    MvPolynomial (CurvatureJetPolynomialVariable n 2) ℝ :=
  curvatureJetRoughLapPoly (n := n) slots -
    MvPolynomial.C 2 * curvatureJetQuadraticPoly (n := n) slots -
      curvatureJetDriftPoly (n := n) slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRmEvolutionPoly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRmEvolutionPoly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRmEvolutionPoly ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureJetRmEvolutionPoly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem eval_curvatureJetRicciPoly (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    {x : M} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (i j : Fin n) :
    MvPolynomial.eval (curvatureJetPolynomialValues (I := I) (M := M) S 2 t basis)
        (curvatureJetRicciPoly (n := n) 2 i j) =
      metricRicciAt (S.base.metric t) x (vec2 (basis i) (basis j)) := by
  classical
  have hrm04 : (S.base.rm04 t) x =
      metricRm04At (I := I) (M := M) (S.base.metric t) x :=
    metricRm04_apply (I := I) (M := M) (S.base.metric t) x
  have hbridge : ∀ a c : Fin n,
      component0S (I := I) basis (nablaKRm04Field (I := I) S t 0 x) (slots4 a i j c) =
        component0S (I := I) basis
          (metricRm04At (I := I) (M := M) (S.base.metric t) x) (slots4 a i j c) := by
    intro a c
    rw [nablaKRm04Field_zero, hrm04]
  let K := metricCurvatureSections (I := I) (M := M) (S.base.metric t)
  have hLower := rm04LowersRm13At_of_realizes (I := I) (S.base.metric t)
    (metricCov (S.base.metric t))
    (metricRm13 (S.base.metric t)) (metricRm04 (S.base.metric t))
    K.rm13Realizes K.rm04Realizes x
  have hTrace := ricciFirstTraceAt_of_rm13_section (I := I) (S.base.metric t) basis
    (basisInvMetric (I := I) (S.base.metric t) x basis)
    (basisInvMetric_isInverse (I := I) (S.base.metric t) x basis)
    (metricRicci (S.base.metric t)) (metricRm13 (S.base.metric t))
    (metricRm04 (S.base.metric t)) K.ricciRealizes hLower i j
  simpa only [curvatureJetRicciPoly, curvatureJetRmVar, map_sum, map_mul,
    MvPolynomial.eval_X, curvatureJetPolynomialValues, hbridge,
    ← rm04CompAt_apply, rm04CompAt,
    metricRicci_apply, metricRm04_apply] using hTrace.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetRicciPoly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetRicciPoly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetRicciPoly ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetRicciPoly

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem eval_curvatureJetRoughLapPoly (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    {x : M} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (slots : Fin 4 → Fin n) :
    roughLap0SField (I := I) (S.base.metric t) (S.base.rm04 t) x
        (fun q => basis (slots q)) =
      MvPolynomial.eval (curvatureJetPolynomialValues (I := I) (M := M) S 2 t basis)
        (curvatureJetRoughLapPoly (n := n) slots) := by
  have hT : metricNabla0S (I := I) (S.base.metric t)
        (metricNabla0S (I := I) (S.base.metric t) (S.base.rm04 t)) x =
      nablaKRm04Field (I := I) S t 2 x := by
    simp only [metricNabla0S_apply, totalNabla0S_apply, nablaKRm04Field_succ,
      nablaKRm04Field_zero]
    rfl
  rw [roughLap0SField_apply, roughLap0STensor_apply]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) (S.base.metric t) basis
    (basisInvMetric (I := I) (S.base.metric t) x basis)
    (basisInvMetric_isInverse (I := I) (S.base.metric t) x basis)]
  rw [metricTrace0S2InBasis, hT]
  simp only [curvatureJetRoughLapPoly, map_sum, map_mul, MvPolynomial.eval_X,
    curvatureJetPolynomialValues, component0S_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  congr 1
  funext q
  fin_cases q <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetRoughLapPoly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetRoughLapPoly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetRoughLapPoly ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetRoughLapPoly

omit [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M] in
theorem eval_curvatureJetQuadraticPoly (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    {x : M} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (slots : Fin 4 → Fin n) :
    component0S (I := I) basis
        (curvatureQuadraticCombination (I := I) (S.base.metric t) (S.base.rm04 t) x) slots =
      MvPolynomial.eval (curvatureJetPolynomialValues (I := I) (M := M) S 2 t basis)
        (curvatureJetQuadraticPoly (n := n) slots) := by
  rw [curvatureQuadraticCombination_component (I := I) (S.base.metric t) basis
    (basisInvMetric (I := I) (S.base.metric t) x basis)
    (basisInvMetric_isInverse (I := I) (S.base.metric t) x basis) (S.base.rm04 t) slots]
  simp only [curvatureJetQuadraticPoly, curvatureJetRmVar, MvPolynomial.eval_sub,
    MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_sum,
    MvPolynomial.eval_X, curvatureJetPolynomialValues, component0S_apply,
    nablaKRm04Field_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetQuadraticPoly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetQuadraticPoly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetQuadraticPoly ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetQuadraticPoly

omit [SigmaCompactSpace M] in
theorem eval_curvatureJetDriftPoly (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    {x : M} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (slots : Fin 4 → Fin n) :
    component0S (I := I) basis
        (ricciDrift04 (I := I) (S.base.metric t) x) slots =
      MvPolynomial.eval (curvatureJetPolynomialValues (I := I) (M := M) S 2 t basis)
        (curvatureJetDriftPoly (n := n) slots) := by
  have hrm04 : (S.base.rm04 t) x = metricRm04At (I := I) (M := M) (S.base.metric t) x :=
    metricRm04_apply (I := I) (M := M) (S.base.metric t) x
  have hvec : (fun q : Fin 4 => basis (slots q)) =
      vec4 (I := I) (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) (basis (slots 3)) := by
    funext q
    fin_cases q <;> simp [vec4]
  have h0 : ∀ p : Fin n,
      (fun q : Fin 4 => basis (Function.update slots 0 p q)) =
        vec4 (I := I) (basis p) (basis (slots 1)) (basis (slots 2)) (basis (slots 3)) := by
    intro p
    funext q
    fin_cases q <;> simp [vec4]
  have h1 : ∀ p : Fin n,
      (fun q : Fin 4 => basis (Function.update slots 1 p q)) =
        vec4 (I := I) (basis (slots 0)) (basis p) (basis (slots 2)) (basis (slots 3)) := by
    intro p
    funext q
    fin_cases q <;> simp [vec4]
  have h2 : ∀ p : Fin n,
      (fun q : Fin 4 => basis (Function.update slots 2 p q)) =
        vec4 (I := I) (basis (slots 0)) (basis (slots 1)) (basis p) (basis (slots 3)) := by
    intro p
    funext q
    fin_cases q <;> simp [vec4]
  have h3 : ∀ p : Fin n,
      (fun q : Fin 4 => basis (Function.update slots 3 p q)) =
        vec4 (I := I) (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) (basis p) := by
    intro p
    funext q
    fin_cases q <;> simp [vec4]
  rw [component0S_apply, hvec]
  change Tensor0SSpace.eval (ricciDrift04 (I := I) (S.base.metric t) x)
      (vec4 (I := I) (basis (slots 0)) (basis (slots 1)) (basis (slots 2))
        (basis (slots 3))) = _
  rw [ricciDrift_comp (I := I) (S.base.metric t) basis
    (basisInvMetric (I := I) (S.base.metric t) x basis)
    (basisInvMetric_isInverse (I := I) (S.base.metric t) x basis)
    (slots 0) (slots 1) (slots 2) (slots 3)]
  simp only [curvatureJetDriftPoly, curvatureJetRmVar, MvPolynomial.eval_add,
    MvPolynomial.eval_mul, MvPolynomial.eval_sum, MvPolynomial.eval_X,
    curvatureJetPolynomialValues, component0S_apply,
    nablaKRm04Field_zero, hrm04, h0, h1, h2, h3, eval_curvatureJetRicciPoly]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetDriftPoly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetDriftPoly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetDriftPoly ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eval_curvatureJetDriftPoly

theorem exists_curvatureJetRm_evolution_polynomial (n : ℕ) :
    ∃ Q : (Fin 4 → Fin n) → MvPolynomial (CurvatureJetPolynomialVariable n 2) ℝ,
      ∀ {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [CompleteSpace E]
        {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
        [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D),
        IsSolutionOn S → ∀ t ∈ D.regular, ∀ x : M,
        ∀ basis : Module.Basis (Fin n) ℝ (TangentSpace I x),
        ∀ slots : Fin 4 → Fin n,
          HasDerivWithinAt
            (fun s => component0S (I := I) basis (nablaKRm04Field S s 0 x) slots)
            (MvPolynomial.eval (curvatureJetPolynomialValues (I := I) (M := M) S 2 t basis)
              (Q slots))
            D.carrier t := by
  classical
  refine ⟨curvatureJetRmEvolutionPoly (n := n), ?_⟩
  intro E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ D S hS t ht x basis slots
  have hderiv := (riemann_hasDerivAt_of_solution (I := I) (M := M) S hS ⟨t, ht⟩ x
    (fun q => basis (slots q))).hasDerivWithinAt (s := D.carrier)
  have hfun :
      (fun s => component0S (I := I) basis (nablaKRm04Field (I := I) S s 0 x) slots) =
        fun s => S.base.rm04 s x (fun q => basis (slots q)) := by
    funext s
    simp only [nablaKRm04Field_zero, component0S_apply]
  rw [hfun]
  refine hderiv.congr_deriv ?_
  have h1 := eval_curvatureJetRoughLapPoly (I := I) (M := M) S t basis slots
  have h2 := eval_curvatureJetQuadraticPoly (I := I) (M := M) S t basis slots
  have h3 := eval_curvatureJetDriftPoly (I := I) (M := M) S t basis slots
  simp only [component0S_apply] at h2 h3
  rw [curvatureJetRmEvolutionPoly, MvPolynomial.eval_sub, MvPolynomial.eval_sub,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, ← h1, ← h2, ← h3]
  simp only [SolutionOn.family_metric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_curvatureJetRm_evolution_polynomial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_curvatureJetRm_evolution_polynomial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_curvatureJetRm_evolution_polynomial ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_curvatureJetRm_evolution_polynomial

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
