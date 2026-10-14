import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Regularized

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedIndexIntegrand_congr_of_eventuallyEq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    {alpha beta : Real → M}
    (Y W : ∀ r, TangentSpace I (alpha r))
    (Y' W' : ∀ r, TangentSpace I (beta r)) (s : Real)
    (halpha : alpha =ᶠ[nhds s] beta)
    (hY : ∀ᶠ r in nhds s, (Y r : E) = (Y' r : E))
    (hW : ∀ᶠ r in nhds s, (W r : E) = (W' r : E)) :
    lRegularizedIndexIntegrand S T alpha Y W s =
      lRegularizedIndexIntegrand S T beta Y' W' s := by
  have hx : alpha s = beta s := halpha.self_of_nhds
  have hA : (lVelocity (I := I) alpha s : E) =
      (lVelocity (I := I) beta s : E) := by
    with_unfolding_all exact
      (congrArg (fun L : Real →L[Real] E ↦ L 1)
        (halpha.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)))
  have hDY :=
    DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := I) (S.base.metric (T - s ^ 2)) Y Y' halpha hY
  have hDW :=
    DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := I) (S.base.metric (T - s ^ 2)) W W' halpha hW
  have hYs : (Y s : E) = (Y' s : E) := hY.self_of_nhds
  have hWs : (W s : E) = (W' s : E) := hW.self_of_nhds
  unfold lRegularizedIndexIntegrand
  dsimp only
  rw [hx, hA, hDY, hDW, hYs, hWs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_congr_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_congr_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_congr_of_eventuallyEq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_congr_of_eventuallyEq

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedIndex_congr_of_eventuallyEq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    {alpha beta : Real → M}
    (Y W : ∀ r, TangentSpace I (alpha r))
    (Y' W' : ∀ r, TangentSpace I (beta r)) (a b : Real)
    (halpha : ∀ s ∈ Set.uIoo a b, alpha =ᶠ[nhds s] beta)
    (hY : ∀ s ∈ Set.uIoo a b,
      ∀ᶠ r in nhds s, (Y r : E) = (Y' r : E))
    (hW : ∀ s ∈ Set.uIoo a b,
      ∀ᶠ r in nhds s, (W r : E) = (W' r : E)) :
    lRegularizedIndex S T alpha Y W a b =
      lRegularizedIndex S T beta Y' W' a b := by
  unfold lRegularizedIndex
  apply intervalIntegral.integral_congr_ae
  filter_upwards
    [MeasureTheory.Measure.ae_ne MeasureTheory.volume (_root_.Max.max a b)]
      with s hsmax hs
  change s ∈ Set.Ioc (_root_.Min.min a b) (_root_.Max.max a b) at hs
  have hsIoo : s ∈ Set.Ioo (_root_.Min.min a b) (_root_.Max.max a b) :=
    ⟨hs.1, lt_of_le_of_ne hs.2 hsmax⟩
  have hsu : s ∈ Set.uIoo a b := by
    simpa only [Set.uIoo] using hsIoo
  exact lRegularizedIndexIntegrand_congr_of_eventuallyEq (I := I) S T Y W Y' W' s
    (halpha s hsu) (hY s hsu) (hW s hsu)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_congr_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_congr_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_congr_of_eventuallyEq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_congr_of_eventuallyEq

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem intervalIntegrable_lRegularizedIndexIntegrand_congr_of_eventuallyEq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    {alpha beta : Real → M}
    (Y W : ∀ r, TangentSpace I (alpha r))
    (Y' W' : ∀ r, TangentSpace I (beta r)) (a b : Real)
    (hab : a ≤ b)
    (halpha : ∀ s ∈ Set.Ioo a b, alpha =ᶠ[nhds s] beta)
    (hY : ∀ s ∈ Set.Ioo a b,
      ∀ᶠ r in nhds s, (Y r : E) = (Y' r : E))
    (hW : ∀ s ∈ Set.Ioo a b,
      ∀ᶠ r in nhds s, (W r : E) = (W' r : E)) :
    IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y W)
        MeasureTheory.volume a b ↔
      IntervalIntegrable (lRegularizedIndexIntegrand S T beta Y' W')
        MeasureTheory.volume a b := by
  have hae : lRegularizedIndexIntegrand S T alpha Y W =ᵐ[
      MeasureTheory.volume.restrict (Set.uIoc a b)]
      lRegularizedIndexIntegrand S T beta Y' W' := by
    filter_upwards [MeasureTheory.Measure.ae_ne
      (MeasureTheory.volume.restrict (Set.uIoc a b)) b,
      MeasureTheory.ae_restrict_mem measurableSet_uIoc]
      with s hsb hs
    have hsIoc : s ∈ Set.Ioc a b := by
      simpa only [Set.uIoc_of_le hab] using hs
    have hsIoo : s ∈ Set.Ioo a b :=
      ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hsb⟩
    exact lRegularizedIndexIntegrand_congr_of_eventuallyEq (I := I) S T Y W Y' W' s
      (halpha s hsIoo) (hY s hsIoo) (hW s hsIoo)
  exact ⟨fun h ↦ h.congr_ae hae, fun h ↦ h.congr_ae hae.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedIndexIntegrand_congr_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedIndexIntegrand_congr_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedIndexIntegrand_congr_of_eventuallyEq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedIndexIntegrand_congr_of_eventuallyEq

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedIndexIntegrand_add
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M)
    (Y Z W : ∀ s, TangentSpace I (alpha s)) (s : Real)
    (hY : DifferentiableAt Real (chartRepAt (I := I) alpha Y s) s)
    (hZ : DifferentiableAt Real (chartRepAt (I := I) alpha Z s) s) :
    lRegularizedIndexIntegrand S T alpha (fun r ↦ Y r + Z r) W s =
      lRegularizedIndexIntegrand S T alpha Y W s + lRegularizedIndexIntegrand S T alpha Z W s := by
  let t := T - s ^ 2
  let g := S.base.metric t
  let x := alpha s
  let A := lVelocity (I := I) alpha s
  let DY := covDerivAlong (I := I) g alpha Y s
  let DZ := covDerivAlong (I := I) g alpha Z s
  let DW := covDerivAlong (I := I) g alpha W s
  let Rm := S.base.rm04 t x
  let Hess := hessianSec (I := I) (S.base.connection t)
    (metricCov_smooth (I := I) g) (S.scalar t)
    (scalarSmoothOfSolution (I := I) S t) x
  let N := totalNabla0SFun (𝕜 := Real) (I := I)
    2 (S.base.connection t) (S.ricci t) x
  have hcov :
      covDerivAlong (I := I) g alpha (fun r ↦ Y r + Z r) s = DY + DZ := by
    simpa only [g, DY, DZ] using
      covDerivAlong_add (I := I) g alpha Y Z s hY hZ
  have hinner : g.inner x (DY + DZ) DW =
      g.inner x DY DW + g.inner x DZ DW := by
    rw [map_add, add_apply]
  have hRm : Rm (vec4 (Y s + Z s) A A (W s)) =
      Rm (vec4 (Y s) A A (W s)) + Rm (vec4 (Z s) A A (W s)) := by
    have h := Rm.map_update_add (vec4 (I := I) 0 A A (W s))
      (0 : Fin 4) (Y s) (Z s)
    change Rm (vec4 (Y s + Z s) A A (W s)) =
      Rm (vec4 (Y s) A A (W s)) + Rm (vec4 (Z s) A A (W s)) at h
    exact h
  have hHess : Hess (vec2 (Y s + Z s) (W s)) =
      Hess (vec2 (Y s) (W s)) + Hess (vec2 (Z s) (W s)) := by
    have h := Hess.map_update_add (vec2 (I := I) 0 (W s))
      (0 : Fin 2) (Y s) (Z s)
    have hl : Function.update (vec2 (I := I) 0 (W s)) (0 : Fin 2)
        (Y s + Z s) = vec2 (Y s + Z s) (W s) := by
      funext i
      fin_cases i <;> simp [vec2]
    have hY' : Function.update (vec2 (I := I) 0 (W s)) (0 : Fin 2)
        (Y s) = vec2 (Y s) (W s) := by
      funext i
      fin_cases i <;> simp [vec2]
    have hZ' : Function.update (vec2 (I := I) 0 (W s)) (0 : Fin 2)
        (Z s) = vec2 (Z s) (W s) := by
      funext i
      fin_cases i <;> simp [vec2]
    simpa only [hl, hY', hZ'] using h
  have hN0 : N (vec3 A (Y s + Z s) (W s)) =
      N (vec3 A (Y s) (W s)) + N (vec3 A (Z s) (W s)) := by
    have h := N.map_update_add (vec3 (I := I) A 0 (W s))
      (1 : Fin 3) (Y s) (Z s)
    have hl : Function.update (vec3 (I := I) A 0 (W s)) (1 : Fin 3)
        (Y s + Z s) = vec3 A (Y s + Z s) (W s) := by
      funext i
      fin_cases i <;> simp [vec3]
    have hY' : Function.update (vec3 (I := I) A 0 (W s)) (1 : Fin 3)
        (Y s) = vec3 A (Y s) (W s) := by
      funext i
      fin_cases i <;> simp [vec3]
    have hZ' : Function.update (vec3 (I := I) A 0 (W s)) (1 : Fin 3)
        (Z s) = vec3 A (Z s) (W s) := by
      funext i
      fin_cases i <;> simp [vec3]
    simpa only [hl, hY', hZ'] using h
  have hN1 : N (vec3 (Y s + Z s) A (W s)) =
      N (vec3 (Y s) A (W s)) + N (vec3 (Z s) A (W s)) := by
    have h := N.map_update_add (vec3 (I := I) 0 A (W s))
      (0 : Fin 3) (Y s) (Z s)
    have hl : Function.update (vec3 (I := I) 0 A (W s)) (0 : Fin 3)
        (Y s + Z s) = vec3 (Y s + Z s) A (W s) := by
      funext i
      fin_cases i <;> simp [vec3]
    have hY' : Function.update (vec3 (I := I) 0 A (W s)) (0 : Fin 3)
        (Y s) = vec3 (Y s) A (W s) := by
      funext i
      fin_cases i <;> simp [vec3]
    have hZ' : Function.update (vec3 (I := I) 0 A (W s)) (0 : Fin 3)
        (Z s) = vec3 (Z s) A (W s) := by
      funext i
      fin_cases i <;> simp [vec3]
    simpa only [hl, hY', hZ'] using h
  have hN2 : N (vec3 (W s) A (Y s + Z s)) =
      N (vec3 (W s) A (Y s)) + N (vec3 (W s) A (Z s)) := by
    have h := N.map_update_add (vec3 (I := I) (W s) A 0)
      (2 : Fin 3) (Y s) (Z s)
    have hl : Function.update (vec3 (I := I) (W s) A 0) (2 : Fin 3)
        (Y s + Z s) = vec3 (W s) A (Y s + Z s) := by
      funext i
      fin_cases i <;> simp [vec3]
    have hY' : Function.update (vec3 (I := I) (W s) A 0) (2 : Fin 3)
        (Y s) = vec3 (W s) A (Y s) := by
      funext i
      fin_cases i <;> simp [vec3]
    have hZ' : Function.update (vec3 (I := I) (W s) A 0) (2 : Fin 3)
        (Z s) = vec3 (W s) A (Z s) := by
      funext i
      fin_cases i <;> simp [vec3]
    simpa only [hl, hY', hZ'] using h
  simp only [lRegularizedIndexIntegrand]
  change (1 / 2 : Real) *
        (g.inner x (covDerivAlong (I := I) g alpha
            (fun r ↦ Y r + Z r) s) DW -
          Rm (vec4 (Y s + Z s) A A (W s))) +
      s ^ 2 * Hess (vec2 (Y s + Z s) (W s)) +
      s * (N (vec3 A (Y s + Z s) (W s)) -
        N (vec3 (Y s + Z s) A (W s)) -
        N (vec3 (W s) A (Y s + Z s))) = _
  rw [hcov, hinner, hRm, hHess, hN0, hN1, hN2]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_add ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_add

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedIndexIntegrand_add_right
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M)
    (Y W Z : ∀ s, TangentSpace I (alpha s)) (s : Real)
    (hW : DifferentiableAt Real (chartRepAt (I := I) alpha W s) s)
    (hZ : DifferentiableAt Real (chartRepAt (I := I) alpha Z s) s) :
    lRegularizedIndexIntegrand S T alpha Y (fun r ↦ W r + Z r) s =
      lRegularizedIndexIntegrand S T alpha Y W s + lRegularizedIndexIntegrand S T alpha Y Z s := by
  calc
    lRegularizedIndexIntegrand S T alpha Y (fun r ↦ W r + Z r) s =
        lRegularizedIndexIntegrand S T alpha (fun r ↦ W r + Z r) Y s :=
      lRegularizedIndexIntegrand_symm (I := I) S T alpha Y (fun r ↦ W r + Z r) s
    _ = lRegularizedIndexIntegrand S T alpha W Y s + lRegularizedIndexIntegrand S T alpha Z Y s :=
      lRegularizedIndexIntegrand_add (I := I) S T alpha W Z Y s hW hZ
    _ = lRegularizedIndexIntegrand S T alpha Y W s + lRegularizedIndexIntegrand S T alpha Y Z s := by
      rw [lRegularizedIndexIntegrand_symm (I := I) S T alpha W Y s,
        lRegularizedIndexIntegrand_symm (I := I) S T alpha Z Y s]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_add_right ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_add_right

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedIndexIntegrand_smul
    (S : SolutionOn (I := I) (M := M) D) (T c : Real)
    (alpha : Real → M)
    (Y W : ∀ s, TangentSpace I (alpha s)) (s : Real) :
    lRegularizedIndexIntegrand S T alpha (fun r ↦ c • Y r) W s =
      c * lRegularizedIndexIntegrand S T alpha Y W s := by
  let t := T - s ^ 2
  let g := S.base.metric t
  let x := alpha s
  let A := lVelocity (I := I) alpha s
  let DY := covDerivAlong (I := I) g alpha Y s
  let DW := covDerivAlong (I := I) g alpha W s
  let Rm := S.base.rm04 t x
  let Hess := hessianSec (I := I) (S.base.connection t)
    (metricCov_smooth (I := I) g) (S.scalar t)
    (scalarSmoothOfSolution (I := I) S t) x
  let N := totalNabla0SFun (𝕜 := Real) (I := I)
    2 (S.base.connection t) (S.ricci t) x
  have hcov :
      covDerivAlong (I := I) g alpha (fun r ↦ c • Y r) s = c • DY := by
    simpa only [g, DY] using covDerivAlong_smul (I := I) g alpha c Y s
  have hinner : g.inner x (c • DY) DW = c * g.inner x DY DW := by
    rw [map_smul, smul_apply]
    rfl
  have hRm : Rm (vec4 (c • Y s) A A (W s)) =
      c * Rm (vec4 (Y s) A A (W s)) := by
    have h := Rm.map_update_smul (vec4 (I := I) 0 A A (W s))
      (0 : Fin 4) c (Y s)
    change Rm (vec4 (c • Y s) A A (W s)) =
      c * Rm (vec4 (Y s) A A (W s)) at h
    exact h
  have hHess : Hess (vec2 (c • Y s) (W s)) =
      c * Hess (vec2 (Y s) (W s)) := by
    have h := Hess.map_update_smul (vec2 (I := I) 0 (W s))
      (0 : Fin 2) c (Y s)
    have hl : Function.update (vec2 (I := I) 0 (W s)) (0 : Fin 2)
        (c • Y s) = vec2 (c • Y s) (W s) := by
      funext i
      fin_cases i <;> simp [vec2]
    have hr : Function.update (vec2 (I := I) 0 (W s)) (0 : Fin 2)
        (Y s) = vec2 (Y s) (W s) := by
      funext i
      fin_cases i <;> simp [vec2]
    simpa only [hl, hr, smul_eq_mul] using h
  have hN0 : N (vec3 A (c • Y s) (W s)) =
      c * N (vec3 A (Y s) (W s)) := by
    have h := N.map_update_smul (vec3 (I := I) A 0 (W s))
      (1 : Fin 3) c (Y s)
    have hl : Function.update (vec3 (I := I) A 0 (W s)) (1 : Fin 3)
        (c • Y s) = vec3 A (c • Y s) (W s) := by
      funext i
      fin_cases i <;> simp [vec3]
    have hr : Function.update (vec3 (I := I) A 0 (W s)) (1 : Fin 3)
        (Y s) = vec3 A (Y s) (W s) := by
      funext i
      fin_cases i <;> simp [vec3]
    simpa only [hl, hr, smul_eq_mul] using h
  have hN1 : N (vec3 (c • Y s) A (W s)) =
      c * N (vec3 (Y s) A (W s)) := by
    have h := N.map_update_smul (vec3 (I := I) 0 A (W s))
      (0 : Fin 3) c (Y s)
    have hl : Function.update (vec3 (I := I) 0 A (W s)) (0 : Fin 3)
        (c • Y s) = vec3 (c • Y s) A (W s) := by
      funext i
      fin_cases i <;> simp [vec3]
    have hr : Function.update (vec3 (I := I) 0 A (W s)) (0 : Fin 3)
        (Y s) = vec3 (Y s) A (W s) := by
      funext i
      fin_cases i <;> simp [vec3]
    simpa only [hl, hr, smul_eq_mul] using h
  have hN2 : N (vec3 (W s) A (c • Y s)) =
      c * N (vec3 (W s) A (Y s)) := by
    have h := N.map_update_smul (vec3 (I := I) (W s) A 0)
      (2 : Fin 3) c (Y s)
    have hl : Function.update (vec3 (I := I) (W s) A 0) (2 : Fin 3)
        (c • Y s) = vec3 (W s) A (c • Y s) := by
      funext i
      fin_cases i <;> simp [vec3]
    have hr : Function.update (vec3 (I := I) (W s) A 0) (2 : Fin 3)
        (Y s) = vec3 (W s) A (Y s) := by
      funext i
      fin_cases i <;> simp [vec3]
    simpa only [hl, hr, smul_eq_mul] using h
  simp only [lRegularizedIndexIntegrand]
  change (1 / 2 : Real) *
        (g.inner x (covDerivAlong (I := I) g alpha
            (fun r ↦ c • Y r) s) DW -
          Rm (vec4 (c • Y s) A A (W s))) +
      s ^ 2 * Hess (vec2 (c • Y s) (W s)) +
      s * (N (vec3 A (c • Y s) (W s)) -
        N (vec3 (c • Y s) A (W s)) -
        N (vec3 (W s) A (c • Y s))) = _
  rw [hcov, hinner, hRm, hHess, hN0, hN1, hN2]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_smul ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_smul

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedIndexIntegrand_smul_right
    (S : SolutionOn (I := I) (M := M) D) (T c : Real)
    (alpha : Real → M)
    (Y W : ∀ s, TangentSpace I (alpha s)) (s : Real) :
    lRegularizedIndexIntegrand S T alpha Y (fun r ↦ c • W r) s =
      c * lRegularizedIndexIntegrand S T alpha Y W s := by
  calc
    lRegularizedIndexIntegrand S T alpha Y (fun r ↦ c • W r) s =
        lRegularizedIndexIntegrand S T alpha (fun r ↦ c • W r) Y s :=
      lRegularizedIndexIntegrand_symm (I := I) S T alpha Y (fun r ↦ c • W r) s
    _ = c * lRegularizedIndexIntegrand S T alpha W Y s :=
      lRegularizedIndexIntegrand_smul (I := I) S T c alpha W Y s
    _ = c * lRegularizedIndexIntegrand S T alpha Y W s := by
      rw [lRegularizedIndexIntegrand_symm (I := I) S T alpha W Y s]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_smul_right ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndexIntegrand_smul_right

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedIndex_add
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M)
    (Y Z W : ∀ s, TangentSpace I (alpha s)) (a b : Real)
    (hY : ∀ s ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) alpha Y s) s)
    (hZ : ∀ s ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) alpha Z s) s)
    (hYint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y W)
      MeasureTheory.volume a b)
    (hZint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Z W)
      MeasureTheory.volume a b) :
    lRegularizedIndex S T alpha (fun s ↦ Y s + Z s) W a b =
      lRegularizedIndex S T alpha Y W a b + lRegularizedIndex S T alpha Z W a b := by
  unfold lRegularizedIndex
  rw [← intervalIntegral.integral_add hYint hZint]
  apply intervalIntegral.integral_congr
  intro s hs
  exact lRegularizedIndexIntegrand_add (I := I) S T alpha Y Z W s (hY s hs) (hZ s hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedIndex_add_right
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M)
    (Y W Z : ∀ s, TangentSpace I (alpha s)) (a b : Real)
    (hW : ∀ s ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) alpha W s) s)
    (hZ : ∀ s ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) alpha Z s) s)
    (hWint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y W)
      MeasureTheory.volume a b)
    (hZint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y Z)
      MeasureTheory.volume a b) :
    lRegularizedIndex S T alpha Y (fun s ↦ W s + Z s) a b =
      lRegularizedIndex S T alpha Y W a b + lRegularizedIndex S T alpha Y Z a b := by
  unfold lRegularizedIndex
  rw [← intervalIntegral.integral_add hWint hZint]
  apply intervalIntegral.integral_congr
  intro s hs
  exact lRegularizedIndexIntegrand_add_right (I := I) S T alpha Y W Z s (hW s hs) (hZ s hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add_right ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add_right

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedIndex_smul
    (S : SolutionOn (I := I) (M := M) D) (T c : Real)
    (alpha : Real → M)
    (Y W : ∀ s, TangentSpace I (alpha s)) (a b : Real) :
    lRegularizedIndex S T alpha (fun s ↦ c • Y s) W a b =
      c * lRegularizedIndex S T alpha Y W a b := by
  unfold lRegularizedIndex
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  exact lRegularizedIndexIntegrand_smul (I := I) S T c alpha Y W s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_smul ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_smul

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedIndex_smul_right
    (S : SolutionOn (I := I) (M := M) D) (T c : Real)
    (alpha : Real → M)
    (Y W : ∀ s, TangentSpace I (alpha s)) (a b : Real) :
    lRegularizedIndex S T alpha Y (fun s ↦ c • W s) a b =
      c * lRegularizedIndex S T alpha Y W a b := by
  unfold lRegularizedIndex
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  exact lRegularizedIndexIntegrand_smul_right (I := I) S T c alpha Y W s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_smul_right ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_smul_right

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedIndex_add_adjacent
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (Y W : ∀ s, TangentSpace I (alpha s))
    (a c b : Real)
    (hac : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y W)
      MeasureTheory.volume a c)
    (hcb : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y W)
      MeasureTheory.volume c b) :
    lRegularizedIndex S T alpha Y W a c + lRegularizedIndex S T alpha Y W c b =
      lRegularizedIndex S T alpha Y W a b := by
  exact intervalIntegral.integral_add_adjacent_intervals hac hcb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add_adjacent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add_adjacent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add_adjacent ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add_adjacent

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedIndex_add_smul_self
    (S : SolutionOn (I := I) (M := M) D) (T c : Real)
    (alpha : Real → M)
    (Y W : ∀ s, TangentSpace I (alpha s)) (a b : Real)
    (hY : ∀ s ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) alpha Y s) s)
    (hW : ∀ s ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) alpha W s) s)
    (hYYint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y Y)
      MeasureTheory.volume a b)
    (hYWint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y W)
      MeasureTheory.volume a b)
    (hWWint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha W W)
      MeasureTheory.volume a b) :
    lRegularizedIndex S T alpha (fun s ↦ Y s + c • W s)
        (fun s ↦ Y s + c • W s) a b =
      lRegularizedIndex S T alpha Y Y a b +
        2 * c * lRegularizedIndex S T alpha Y W a b +
        c ^ 2 * lRegularizedIndex S T alpha W W a b := by
  have hYWscaled : IntervalIntegrable
      (fun s ↦ (2 * c) * lRegularizedIndexIntegrand S T alpha Y W s)
      MeasureTheory.volume a b := hYWint.const_mul (2 * c)
  have hWWscaled : IntervalIntegrable
      (fun s ↦ c ^ 2 * lRegularizedIndexIntegrand S T alpha W W s)
      MeasureTheory.volume a b := hWWint.const_mul (c ^ 2)
  unfold lRegularizedIndex
  calc
    (∫ s in a..b, lRegularizedIndexIntegrand S T alpha
        (fun r ↦ Y r + c • W r) (fun r ↦ Y r + c • W r) s) =
      ∫ s in a..b, lRegularizedIndexIntegrand S T alpha Y Y s +
        (2 * c) * lRegularizedIndexIntegrand S T alpha Y W s +
        c ^ 2 * lRegularizedIndexIntegrand S T alpha W W s := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hYs := hY s hs
      have hWs := hW s hs
      have hcWs : DifferentiableAt Real
          (chartRepAt (I := I) alpha (fun r ↦ c • W r) s) s := by
        rw [chartRepAt_smul]
        exact hWs.const_smul c
      calc
        lRegularizedIndexIntegrand S T alpha (fun r ↦ Y r + c • W r)
            (fun r ↦ Y r + c • W r) s =
          lRegularizedIndexIntegrand S T alpha Y (fun r ↦ Y r + c • W r) s +
            lRegularizedIndexIntegrand S T alpha (fun r ↦ c • W r)
              (fun r ↦ Y r + c • W r) s :=
          lRegularizedIndexIntegrand_add (I := I) S T alpha Y (fun r ↦ c • W r)
            (fun r ↦ Y r + c • W r) s hYs hcWs
        _ = (lRegularizedIndexIntegrand S T alpha Y Y s +
              lRegularizedIndexIntegrand S T alpha Y (fun r ↦ c • W r) s) +
            c * lRegularizedIndexIntegrand S T alpha W
              (fun r ↦ Y r + c • W r) s := by
          rw [lRegularizedIndexIntegrand_add_right (I := I) S T alpha Y Y
              (fun r ↦ c • W r) s hYs hcWs,
            lRegularizedIndexIntegrand_smul (I := I) S T c alpha W
              (fun r ↦ Y r + c • W r) s]
        _ = lRegularizedIndexIntegrand S T alpha Y Y s +
            2 * c * lRegularizedIndexIntegrand S T alpha Y W s +
            c ^ 2 * lRegularizedIndexIntegrand S T alpha W W s := by
          rw [lRegularizedIndexIntegrand_smul_right (I := I) S T c alpha Y W s,
            lRegularizedIndexIntegrand_add_right (I := I) S T alpha W Y
              (fun r ↦ c • W r) s hYs hcWs,
            lRegularizedIndexIntegrand_smul_right (I := I) S T c alpha W W s,
            lRegularizedIndexIntegrand_symm (I := I) S T alpha W Y s]
          ring
    _ = (∫ s in a..b, lRegularizedIndexIntegrand S T alpha Y Y s) +
        (∫ s in a..b, (2 * c) * lRegularizedIndexIntegrand S T alpha Y W s) +
        ∫ s in a..b, c ^ 2 * lRegularizedIndexIntegrand S T alpha W W s := by
      rw [intervalIntegral.integral_add (hYYint.add hYWscaled) hWWscaled,
        intervalIntegral.integral_add hYYint hYWscaled]
    _ = (∫ s in a..b, lRegularizedIndexIntegrand S T alpha Y Y s) +
        2 * c * (∫ s in a..b, lRegularizedIndexIntegrand S T alpha Y W s) +
        c ^ 2 * ∫ s in a..b, lRegularizedIndexIntegrand S T alpha W W s := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add_smul_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add_smul_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add_smul_self ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedIndex_add_smul_self

private theorem exists_neg_scale {k Q : Real} (hk : 0 < k) :
    ∃ s : Real, 2 * s * k + s ^ 2 * Q < 0 := by
  have hden : 0 < |Q| + 1 := by positivity
  let s : Real := -k / (|Q| + 1)
  have hsneg : s < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hk) hden
  have hsQ : |s * Q| < k := by
    simp only [s]
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hk, abs_of_pos hden,
      div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [abs_nonneg Q]
  have hsum : 0 < 2 * k + s * Q := by
    linarith [(abs_lt.mp hsQ).1]
  refine ⟨s, ?_⟩
  calc
    2 * s * k + s ^ 2 * Q = s * (2 * k + s * Q) := by ring
    _ < 0 := mul_neg_of_neg_of_pos hsneg hsum

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_neg_scale
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_neg_scale target :: scope.openDecls } }

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem exists_lRegularizedIndex_split_lt_zero_of_cross_pos
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (Y W : ∀ s, TangentSpace I (alpha s))
    (a c b : Real)
    (hY : ∀ s ∈ Set.uIcc a c,
      DifferentiableAt Real (chartRepAt (I := I) alpha Y s) s)
    (hW : ∀ s ∈ Set.uIcc a c,
      DifferentiableAt Real (chartRepAt (I := I) alpha W s) s)
    (hYYint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y Y)
      MeasureTheory.volume a c)
    (hYWint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y W)
      MeasureTheory.volume a c)
    (hWWac : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha W W)
      MeasureTheory.volume a c)
    (hWWcb : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha W W)
      MeasureTheory.volume c b)
    (hYY : lRegularizedIndex S T alpha Y Y a c = 0)
    (hYW : 0 < lRegularizedIndex S T alpha Y W a c) :
    ∃ k : Real,
      lRegularizedIndex S T alpha (fun s ↦ Y s + k • W s)
          (fun s ↦ Y s + k • W s) a c +
        lRegularizedIndex S T alpha (fun s ↦ k • W s)
          (fun s ↦ k • W s) c b < 0 := by
  let Q := lRegularizedIndex S T alpha W W a b
  obtain ⟨k, hk⟩ := exists_neg_scale hYW (Q := Q)
  refine ⟨k, ?_⟩
  have hprefix := lRegularizedIndex_add_smul_self (I := I) S T k alpha Y W a c hY hW
    hYYint hYWint hWWac
  have htail : lRegularizedIndex S T alpha (fun s ↦ k • W s)
      (fun s ↦ k • W s) c b =
      k ^ 2 * lRegularizedIndex S T alpha W W c b := by
    rw [lRegularizedIndex_smul (I := I) S T k alpha W
        (fun s ↦ k • W s) c b,
      lRegularizedIndex_smul_right (I := I) S T k alpha W W c b]
    ring
  have hjoin := lRegularizedIndex_add_adjacent (I := I) S T alpha W W a c b hWWac hWWcb
  rw [hprefix, htail, hYY, zero_add]
  dsimp only [Q] at hk
  rw [← hjoin] at hk
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lRegularizedIndex_split_lt_zero_of_cross_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lRegularizedIndex_split_lt_zero_of_cross_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lRegularizedIndex_split_lt_zero_of_cross_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lRegularizedIndex_split_lt_zero_of_cross_pos

private theorem exists_pos_scale {h Q : Real} (hh : h < 0) :
    ∃ k : Real, 2 * k * h + k ^ 2 * Q < 0 := by
  have hden : 0 < |Q| + 1 := by positivity
  let k : Real := -h / (|Q| + 1)
  have hkpos : 0 < k := div_pos (neg_pos.mpr hh) hden
  have hkQ : |k * Q| < -h := by
    simp only [k]
    rw [abs_mul, abs_div, abs_neg, abs_of_neg hh,
      abs_of_pos hden, div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [abs_nonneg Q]
  have hsum : 2 * h + k * Q < 0 := by
    linarith [(abs_lt.mp hkQ).2]
  refine ⟨k, ?_⟩
  calc
    2 * k * h + k ^ 2 * Q = k * (2 * h + k * Q) := by ring
    _ < 0 := mul_neg_of_pos_of_neg hkpos hsum

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_pos_scale
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_pos_scale target :: scope.openDecls } }

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem exists_lRegularizedIndex_split_lt_zero_of_cross_neg
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (Y W : ∀ s, TangentSpace I (alpha s))
    (a c b : Real)
    (hY : ∀ s ∈ _root_.Set.uIcc c b,
      DifferentiableAt Real (chartRepAt (I := I) alpha Y s) s)
    (hW : ∀ s ∈ _root_.Set.uIcc c b,
      DifferentiableAt Real (chartRepAt (I := I) alpha W s) s)
    (hYYint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y Y)
      MeasureTheory.volume c b)
    (hYWint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y W)
      MeasureTheory.volume c b)
    (hWWac : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha W W)
      MeasureTheory.volume a c)
    (hWWcb : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha W W)
      MeasureTheory.volume c b)
    (hYY : lRegularizedIndex S T alpha Y Y c b = 0)
    (hYW : lRegularizedIndex S T alpha Y W c b < 0) :
    ∃ k : Real,
      lRegularizedIndex S T alpha (fun s ↦ k • W s)
          (fun s ↦ k • W s) a c +
        lRegularizedIndex S T alpha (fun s ↦ Y s + k • W s)
          (fun s ↦ Y s + k • W s) c b < 0 := by
  let Q := lRegularizedIndex S T alpha W W a b
  obtain ⟨k, hk⟩ := exists_pos_scale hYW (Q := Q)
  refine ⟨k, ?_⟩
  have htail := lRegularizedIndex_add_smul_self (I := I) S T k alpha Y W c b hY hW
    hYYint hYWint hWWcb
  have hprefix : lRegularizedIndex S T alpha (fun s ↦ k • W s)
      (fun s ↦ k • W s) a c =
      k ^ 2 * lRegularizedIndex S T alpha W W a c := by
    rw [lRegularizedIndex_smul (I := I) S T k alpha W
        (fun s ↦ k • W s) a c,
      lRegularizedIndex_smul_right (I := I) S T k alpha W W a c]
    ring
  have hjoin := lRegularizedIndex_add_adjacent (I := I) S T alpha W W a c b hWWac hWWcb
  rw [hprefix, htail, hYY, zero_add]
  dsimp only [Q] at hk
  rw [← hjoin] at hk
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lRegularizedIndex_split_lt_zero_of_cross_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lRegularizedIndex_split_lt_zero_of_cross_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lRegularizedIndex_split_lt_zero_of_cross_neg ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lRegularizedIndex_split_lt_zero_of_cross_neg

end DifferentialGeometry.PDE.RicciFlow.Perelman
