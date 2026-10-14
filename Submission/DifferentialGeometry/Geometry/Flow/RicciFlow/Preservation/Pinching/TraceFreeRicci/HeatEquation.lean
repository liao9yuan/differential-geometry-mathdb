import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Definitions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]

def scalarCurvatureSqLaplacian
    (scalar scalarLap gradScalarNormSq : Real -> M -> Real) :
    Real -> M -> Real :=
  fun t x => 2 * scalar t x * scalarLap t x + 2 * gradScalarNormSq t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarCurvatureSqLaplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarCurvatureSqLaplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarCurvatureSqLaplacian ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarCurvatureSqLaplacian

omit [Module.Finite ℝ E] in
theorem scalar_curvature_sq_laplacian_apply
    [FiniteDimensional Real E]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (t : Real) {f : M -> Real} {x : M}
    (hf_all : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hf_x : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) f y) x)
    (hfg : MDiffAt (T% (f • fun y : M =>
      DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) f y)) x) :
    DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) G t (fun y : M => f y ^ 2) x =
      2 * f x * DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) G t f x +
        2 * (G.metric t).inner x
          (DifferentialGeometry.Geometry.Curvature.gradientAt (I := I) G t f x)
          (DifferentialGeometry.Geometry.Curvature.gradientAt (I := I) G t f x) := by
  have hhalf :=
    DifferentialGeometry.Geometry.Operator.half_laplacian_mul_self
      (I := I) (G.connection t) (G.metric t) (f := f) (x := x)
      hf_all hf_x hgrad hfg
  unfold DifferentialGeometry.Geometry.Curvature.laplacianAt
    DifferentialGeometry.Geometry.Curvature.gradientAt
  have hpow :
      (fun y : M => f y ^ 2) = fun y : M => f y * f y := by
    funext y
    ring
  rw [hpow]
  have hmain :
      DifferentialGeometry.Geometry.Operator.laplacian (I := I) (G.connection t) (G.metric t)
          (fun y : M => f y * f y) x =
        2 * (f x * DifferentialGeometry.Geometry.Operator.laplacian (I := I) (G.connection t)
          (G.metric t) f x +
          (G.metric t).inner x
            (DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) f x)
            (DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) f x)) := by
    linarith
  rw [hmain]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalar_curvature_sq_laplacian_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalar_curvature_sq_laplacian_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalar_curvature_sq_laplacian_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.scalar_curvature_sq_laplacian_apply

omit [Module.Finite ℝ E] in
theorem scalar_curvature_sq_laplacian_realizes
    [FiniteDimensional Real E]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (scalar scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarLap : ScalarLaplacianRealizesHeatOperatorOn
      (I := I) G T scalar scalarLap)
    (hgradNorm : forall t x,
      gradScalarNormSq t x =
        (G.metric t).inner x
          (DifferentialGeometry.Geometry.Curvature.gradientAt (I := I) G t (scalar t) x)
          (DifferentialGeometry.Geometry.Curvature.gradientAt (I := I) G t (scalar t) x))
    (hdf : forall t y,
      MDifferentiableAt I 𝓘(Real, Real) (scalar t) y)
    (hgrad : forall t x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (scalar t) y) x)
    (hfg : forall t x,
      MDiffAt (T% ((scalar t) • fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (scalar t) y))
          x) :
    ScalarLaplacianRealizesHeatOperatorOn
      (I := I) G T
      (fun t x => scalar t x ^ 2)
      (scalarCurvatureSqLaplacian scalar scalarLap gradScalarNormSq) := by
  intro t ht x
  have hlap :
      scalarLap t x = DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) G t (scalar t)
        x := by
    simpa [DifferentialGeometry.Geometry.Curvature.heatOperator] using hscalarLap t ht x
  have hsq :=
    scalar_curvature_sq_laplacian_apply (I := I) G t (f := scalar t) (x := x)
      (hdf t) (hdf t x) (hgrad t x) (hfg t x)
  calc
    scalarCurvatureSqLaplacian scalar scalarLap gradScalarNormSq t x =
        2 * scalar t x * DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) G t
          (scalar t) x +
          2 * (G.metric t).inner x
            (DifferentialGeometry.Geometry.Curvature.gradientAt (I := I) G t (scalar t) x)
            (DifferentialGeometry.Geometry.Curvature.gradientAt (I := I) G t (scalar t) x) := by
          simp [scalarCurvatureSqLaplacian, hlap, hgradNorm t x]
    _ = DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) G t
          (fun y : M => scalar t y ^ 2) x := by
          rw [hsq]
    _ = DifferentialGeometry.Geometry.Curvature.heatOperator (I := I) G t
          (fun y : M => scalar t y ^ 2) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalar_curvature_sq_laplacian_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalar_curvature_sq_laplacian_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalar_curvature_sq_laplacian_realizes ``Submission.DifferentialGeometry.PDE.RicciFlow.scalar_curvature_sq_laplacian_realizes

def traceFreeRicciNormSqLaplacian
    (scalar scalarLap gradScalarNormSq ricciNormLap : Real -> M -> Real) :
    Real -> M -> Real :=
  fun t x => ricciNormLap t x -
    scalarCurvatureSqLaplacian scalar scalarLap gradScalarNormSq t x / 3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqLaplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqLaplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqLaplacian ``Submission.DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqLaplacian

def ScalarCurvatureSqHeatEquationOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (scalar scalarCurvatureSqLaplacian gradScalarNormSq ricciNormSq : Real -> M -> Real) :
    Prop :=
  ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => scalar s x ^ 2)
      (scalarCurvatureSqLaplacian (t : Real) x +
        (-2 * gradScalarNormSq (t : Real) x +
          4 * scalar (t : Real) x * ricciNormSq (t : Real) x))
      D.carrier
      (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ScalarCurvatureSqHeatEquationOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ScalarCurvatureSqHeatEquationOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ScalarCurvatureSqHeatEquationOn ``Submission.DifferentialGeometry.PDE.RicciFlow.ScalarCurvatureSqHeatEquationOn

omit [TopologicalSpace M] in
theorem scalar_curvature_sq_heat_equation
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (scalar scalarLap gradScalarNormSq ricciNormSq : Real -> M -> Real)
    (hscalar : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap ricciNormSq) :
    ScalarCurvatureSqHeatEquationOn
      (D := D) scalar (scalarCurvatureSqLaplacian scalar scalarLap gradScalarNormSq)
      gradScalarNormSq ricciNormSq := by
  intro t x
  have h := hscalar t x
  have hmul := h.mul h
  have hpow := hmul.congr
    (fun s _ => pow_two (scalar s x)) (pow_two (scalar (t : Real) x))
  refine hpow.congr_deriv ?_
  unfold scalarCurvatureSqLaplacian
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalar_curvature_sq_heat_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalar_curvature_sq_heat_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalar_curvature_sq_heat_equation ``Submission.DifferentialGeometry.PDE.RicciFlow.scalar_curvature_sq_heat_equation

def TraceFreeRicciNormSqHeatEquationOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (tfNormSq traceFreeRicciNormSqLaplacian nablaRicNormSq gradScalarNormSq
      scalar ricciNormSq Q : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
    scalar (t : Real) x ≠ 0 ->
    HasDerivWithinAt
      (fun s : Real => tfNormSq s x)
      (traceFreeRicciNormSqLaplacian (t : Real) x +
        (-2 * nablaRicNormSq (t : Real) x +
          ((2 : Real) / 3) * gradScalarNormSq (t : Real) x +
          (4 * ricciNormSq (t : Real) x * tfNormSq (t : Real) x -
            2 * Q (t : Real) x) / scalar (t : Real) x))
      D.carrier
      (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TraceFreeRicciNormSqHeatEquationOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TraceFreeRicciNormSqHeatEquationOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TraceFreeRicciNormSqHeatEquationOn ``Submission.DifferentialGeometry.PDE.RicciFlow.TraceFreeRicciNormSqHeatEquationOn

omit [TopologicalSpace M] in
theorem trace_free_ricci_norm_sq_heat_equation_of_reaction_relation
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (scalar ricciNormSq ricciNormLap scalarCurvatureSqLaplacian traceFreeRicciNormSqLaplacian
      nablaRicNormSq gradScalarNormSq Q reaction : Real -> M -> Real)
    (hRic : RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq reaction)
    (hSq : ScalarCurvatureSqHeatEquationOn
      (D := D) scalar scalarCurvatureSqLaplacian gradScalarNormSq ricciNormSq)
    (hLap : ∀ t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D, ∀ x,
      traceFreeRicciNormSqLaplacian (t : Real) x = ricciNormLap (t : Real) x -
        scalarCurvatureSqLaplacian (t : Real) x / 3)
    (hRel : TraceFreeRicciReactionRelation
      scalar ricciNormSq (traceFreeRicciNormSq scalar ricciNormSq) Q reaction) :
    TraceFreeRicciNormSqHeatEquationOn
      (D := D)
      (traceFreeRicciNormSq scalar ricciNormSq)
      traceFreeRicciNormSqLaplacian nablaRicNormSq gradScalarNormSq scalar ricciNormSq Q := by
  intro t x hR
  have hRic' := hRic t x
  have hSq' := hSq t x
  have hDeriv0 :
      HasDerivWithinAt
        (fun s : Real => ricciNormSq s x - ((1 : Real) / 3) * scalar s x ^ 2)
        ((ricciNormLap (t : Real) x +
            (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x)) -
          ((1 : Real) / 3) *
            (scalarCurvatureSqLaplacian (t : Real) x +
              (-2 * gradScalarNormSq (t : Real) x +
                4 * scalar (t : Real) x * ricciNormSq (t : Real) x)))
        D.carrier
        (t : Real) := by
    have hsub := hRic'.sub (hSq'.const_mul ((1 : Real) / 3))
    have hfun :
        ((fun s : Real => ricciNormSq s x) -
          fun s : Real => ((1 : Real) / 3) * scalar s x ^ 2) =
          fun s : Real => ricciNormSq s x - ((1 : Real) / 3) * scalar s x ^ 2 := by
      rfl
    rw [← hfun]
    exact hsub
  have hDeriv :
      HasDerivWithinAt
        (fun s : Real => traceFreeRicciNormSq scalar ricciNormSq s x)
        ((ricciNormLap (t : Real) x +
            (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x)) -
          ((1 : Real) / 3) *
            (scalarCurvatureSqLaplacian (t : Real) x +
              (-2 * gradScalarNormSq (t : Real) x +
                4 * scalar (t : Real) x * ricciNormSq (t : Real) x)))
        D.carrier
        (t : Real) := by
    have hfun : (fun s : Real => traceFreeRicciNormSq scalar ricciNormSq s x) =
        fun s : Real => ricciNormSq s x - ((1 : Real) / 3) * scalar s x ^ 2 := by
      funext s
      unfold traceFreeRicciNormSq traceFreeRicciNormSqOf traceFreeRicciNormSqAtOf
      ring
    rw [hfun]
    exact hDeriv0
  have hValue :
      ((ricciNormLap (t : Real) x +
          (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x)) -
        ((1 : Real) / 3) *
          (scalarCurvatureSqLaplacian (t : Real) x +
            (-2 * gradScalarNormSq (t : Real) x +
              4 * scalar (t : Real) x * ricciNormSq (t : Real) x))) =
      traceFreeRicciNormSqLaplacian (t : Real) x +
        (-2 * nablaRicNormSq (t : Real) x +
          ((2 : Real) / 3) * gradScalarNormSq (t : Real) x +
          (4 * ricciNormSq (t : Real) x *
              traceFreeRicciNormSq scalar ricciNormSq (t : Real) x -
            2 * Q (t : Real) x) / scalar (t : Real) x) := by
    rw [hLap t x, ← hRel (t : Real) x hR]
    ring
  rw [hValue] at hDeriv
  exact hDeriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_heat_equation_of_reaction_relation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_heat_equation_of_reaction_relation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_heat_equation_of_reaction_relation ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_heat_equation_of_reaction_relation

omit [TopologicalSpace M] in
theorem trace_free_ricci_norm_sq_heat_equation
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (scalar scalarLap ricciNormSq ricciNormLap
      nablaRicNormSq gradScalarNormSq Q reaction : Real -> M -> Real)
    (hscalar : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap ricciNormSq)
    (hRic : RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq reaction)
    (hRel : TraceFreeRicciReactionRelation
      scalar ricciNormSq (traceFreeRicciNormSq scalar ricciNormSq) Q reaction) :
    TraceFreeRicciNormSqHeatEquationOn
      (D := D)
      (traceFreeRicciNormSq scalar ricciNormSq)
      (traceFreeRicciNormSqLaplacian scalar scalarLap gradScalarNormSq ricciNormLap)
      nablaRicNormSq gradScalarNormSq scalar ricciNormSq Q := by
  exact trace_free_ricci_norm_sq_heat_equation_of_reaction_relation
    (D := D)
    scalar ricciNormSq ricciNormLap
    (scalarCurvatureSqLaplacian scalar scalarLap gradScalarNormSq)
    (traceFreeRicciNormSqLaplacian scalar scalarLap gradScalarNormSq ricciNormLap)
    nablaRicNormSq gradScalarNormSq Q reaction
    hRic
    (scalar_curvature_sq_heat_equation
      (D := D) scalar scalarLap gradScalarNormSq ricciNormSq hscalar)
    (by intro t x; rfl)
    hRel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_heat_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_heat_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_heat_equation ``Submission.DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_heat_equation

end DifferentialGeometry.PDE.RicciFlow
