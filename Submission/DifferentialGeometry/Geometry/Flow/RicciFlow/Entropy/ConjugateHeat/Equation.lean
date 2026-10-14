import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Volume
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak
import Submission.DifferentialGeometry.Analysis.Parabolic.ScalarHeat.TimeDependent
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.Family
import Mathlib.Analysis.Calculus.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

open _root_.Submission.DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume
open scoped _root_.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

def reverseFamily
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily
      (I := I) (M := M) Real)
    (T : Real) :
    DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily
      (I := I) (M := M) Real where
  metric := fun s => G.metric (T - s)
  connection := fun s => G.connection (T - s)
  metricCompatible := fun s => G.metricCompatible (T - s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.reverseFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.reverseFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.reverseFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.reverseFamily

omit [FiniteDimensional ℝ E] in
@[simp] theorem reverse_metric
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily
      (I := I) (M := M) Real)
    (T s : Real) :
    (reverseFamily G T).metric s = G.metric (T - s) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_metric

theorem heat_pot_add
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily
      (I := I) (M := M) Real)
    (V u : Real → M → Real) (T a : Real)
    (h : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D
      (reverseFamily G T) V u) :
    DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
      (D.timeShift (-a)) (reverseFamily G (T + a))
      (fun r x => V (r - a) x) (fun r x => u (r - a) x) := by
  refine
    { jointSmooth := ?_
      jointCont := ?_
      sliceSmooth := ?_
      equation := ?_ }
  · have hmap :
        ContMDiff ((modelWithCornersSelf Real Real).prod I)
          ((modelWithCornersSelf Real Real).prod I) ∞
          (fun p : Real × M => (p.1 - a, p.2)) :=
      (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
    have hmaps :
        Set.MapsTo (fun p : Real × M => (p.1 - a, p.2))
          ((D.timeShift (-a)).regular ×ˢ (Set.univ : Set M))
          (D.regular ×ˢ (Set.univ : Set M)) := by
      intro p hp
      exact ⟨by simpa [sub_eq_add_neg] using hp.1, hp.2⟩
    have hcomp := h.jointSmooth.comp hmap.contMDiffOn hmaps
    convert hcomp using 1
    funext p
    rfl
  · have hmap : Continuous (fun p : Real × M => (p.1 - a, p.2)) :=
      (continuous_fst.sub continuous_const).prodMk continuous_snd
    have hmaps :
        Set.MapsTo (fun p : Real × M => (p.1 - a, p.2))
          ((D.timeShift (-a)).carrier ×ˢ (Set.univ : Set M))
          (D.carrier ×ˢ (Set.univ : Set M)) := by
      intro p hp
      exact ⟨by simpa [sub_eq_add_neg] using hp.1, hp.2⟩
    have hcomp := h.jointCont.comp hmap.continuousOn hmaps
    convert hcomp using 1
    funext p
    rfl
  · intro r hr
    exact h.sliceSmooth (r - a) (by simpa [sub_eq_add_neg] using hr)
  · intro r hr x
    have hr' : r - a ∈ D.regular := by
      simpa [sub_eq_add_neg] using hr
    have heq := h.equation (r - a) hr' x
    have hshift : HasDerivAt (fun s : Real => s - a) 1 r := by
      simpa using (hasDerivAt_id (x := r)).sub_const a
    have hcomp := heq.comp r hshift
    have htime : T - (r - a) = T + a - r := by ring
    have hcomp' :
        HasDerivAt (fun s : Real => u (s - a) x)
          (DifferentialGeometry.Geometry.Curvature.laplacianAt
              (I := I) (reverseFamily G T) (r - a) (u (r - a)) x +
            V (r - a) x * u (r - a) x) r := by
      convert hcomp using 1
      · rfl
      · rfl
      · funext s
        rfl
      · simp
    convert hcomp' using 1
    all_goals
      simp only [reverseFamily,
        DifferentialGeometry.Geometry.Curvature.laplacianAt, htime]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.heat_pot_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.heat_pot_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.heat_pot_add ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.heat_pot_add

def reverseHeat (T : Real) (u : Real → M → Real) : Real → M → Real :=
  fun s x => u (T - s) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.reverseHeat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.reverseHeat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.reverseHeat ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.reverseHeat

omit [TopologicalSpace M] in
@[simp] theorem reverse_heat_apply
    (T : Real) (u : Real → M → Real) (s : Real) (x : M) :
    reverseHeat T u s x = u (T - s) x := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_heat_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_heat_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_heat_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_heat_apply

omit [TopologicalSpace M] in
theorem reverse_deriv
    (T : Real) (u : Real → M → Real) (s : Real) (x : M)
    (hu : DifferentiableAt Real (fun t : Real => u t x) (T - s)) :
    deriv (fun r : Real => reverseHeat T u r x) s =
      -deriv (fun t : Real => u t x) (T - s) := by
  have hsub : HasDerivAt (fun r : Real => T - r) (-1) s := by
    have hsubRaw :=
      (hasDerivAt_const (x := s) (c := T)).sub (hasDerivAt_id (x := s))
    convert hsubRaw using 1
    · rfl
    · rfl
    · funext r
      rfl
    · norm_num
  have hcomp := hu.hasDerivAt.comp s hsub
  have hderiv := hcomp.deriv
  convert hderiv using 1
  · apply congrArg (fun f : Real → Real => deriv f s)
    funext r
    rfl
  · ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_deriv ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_deriv

theorem conj_heat_forward
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily
      (I := I) (M := M) Real)
    (scalar u : Real → M → Real) (T s : Real) (x : M)
    (hu : DifferentiableAt Real (fun t : Real => u t x) (T - s))
    (hconj : deriv (fun t : Real => u t x) (T - s) =
      -DifferentialGeometry.Geometry.Curvature.laplacianAt
          (I := I) G (T - s) (u (T - s)) x +
        scalar (T - s) x * u (T - s) x) :
    deriv (fun r : Real => reverseHeat T u r x) s =
      DifferentialGeometry.Geometry.Curvature.laplacianAt
          (I := I) (reverseFamily G T) s (reverseHeat T u s) x -
        scalar (T - s) x * reverseHeat T u s x := by
  rw [reverse_deriv T u s x hu, hconj]
  change
    -(-DifferentialGeometry.Geometry.Curvature.laplacianAt
          (I := I) G (T - s) (u (T - s)) x +
        scalar (T - s) x * u (T - s) x) =
      DifferentialGeometry.Geometry.Curvature.laplacianAt
          (I := I) G (T - s) (u (T - s)) x -
        scalar (T - s) x * u (T - s) x
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_forward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_forward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_forward ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_forward

theorem conj_heat_backward
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily
      (I := I) (M := M) Real)
    (scalar v : Real → M → Real) (T t : Real) (x : M)
    (hv : DifferentiableAt Real (fun s : Real => v s x) (T - t))
    (hforward : deriv (fun s : Real => v s x) (T - t) =
      DifferentialGeometry.Geometry.Curvature.laplacianAt
          (I := I) (reverseFamily G T) (T - t) (v (T - t)) x -
        scalar t x * v (T - t) x) :
    deriv (fun s : Real => reverseHeat T v s x) t =
      -DifferentialGeometry.Geometry.Curvature.laplacianAt
          (I := I) G t (reverseHeat T v t) x +
        scalar t x * reverseHeat T v t x := by
  rw [reverse_deriv T v t x hv, hforward]
  change
    -(DifferentialGeometry.Geometry.Curvature.laplacianAt
          (I := I) G (T - (T - t)) (v (T - t)) x -
        scalar t x * v (T - t) x) =
      -DifferentialGeometry.Geometry.Curvature.laplacianAt
          (I := I) G t (v (T - t)) x + scalar t x * v (T - t) x
  rw [show T - (T - t) = t by ring]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_backward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_backward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_backward ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_backward

omit [TopologicalSpace M] in
@[simp] theorem reverse_heat_reverse
    (T : Real) (u : Real → M → Real) :
    reverseHeat T (reverseHeat T u) = u := by
  funext s x
  change u (T - (T - s)) x = u s x
  rw [show T - (T - s) = s by ring]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_heat_reverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_heat_reverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_heat_reverse ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.reverse_heat_reverse

def IsConjHeatOn
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily
      (I := I) (M := M) Real)
    (scalar u : Real → M → Real) (T : Real) : Prop :=
  DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D (reverseFamily G T)
    (fun s x => -scalar (T - s) x) (reverseHeat T u)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.IsConjHeatOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.IsConjHeatOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.IsConjHeatOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.IsConjHeatOn

theorem conj_heat_of_pot
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily
      (I := I) (M := M) Real)
    (scalar v : Real → M → Real) (T : Real)
    (h : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D
      (reverseFamily G T) (fun s x => -scalar (T - s) x) v) :
    IsConjHeatOn D G scalar (reverseHeat T v) T := by
  simpa only [IsConjHeatOn, reverse_heat_reverse] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_of_pot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_of_pot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_of_pot ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_of_pot

theorem heat_pot_to_conj
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily
      (I := I) (M := M) Real)
    (scalar v : Real → M → Real) (T t : Real)
    (h : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D
      (reverseFamily G T) (fun s x => -scalar (T - s) x) v)
    (ht : T - t ∈ D.regular) (x : M) :
    HasDerivAt (fun s : Real => reverseHeat T v s x)
      (-DifferentialGeometry.Geometry.Curvature.laplacianAt
          (I := I) G t (reverseHeat T v t) x +
        scalar t x * reverseHeat T v t x) t := by
  have hsub : HasDerivAt (fun s : Real => T - s) (-1) t := by
    have hsubRaw :=
      (hasDerivAt_const (x := t) (c := T)).sub (hasDerivAt_id (x := t))
    convert hsubRaw using 1
    · rfl
    · rfl
    · funext s
      rfl
    · norm_num
  have hcomp := (h.equation (T - t) ht x).comp t hsub
  convert hcomp using 1
  · rfl
  · rfl
  · funext s
    rfl
  · change
      -DifferentialGeometry.Geometry.Curvature.laplacianAt
            (I := I) G t (v (T - t)) x + scalar t x * v (T - t) x =
        (DifferentialGeometry.Geometry.Curvature.laplacianAt
            (I := I) G (T - (T - t)) (v (T - t)) x +
          -scalar (T - (T - t)) x * v (T - t) x) * -1
    rw [show T - (T - t) = t by ring]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.heat_pot_to_conj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.heat_pot_to_conj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.heat_pot_to_conj ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.heat_pot_to_conj

theorem conj_heat_mass_deriv
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily
      (I := I) (M := M) Real)
    (scalar u : Real → M → Real) {t : Real}
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t)
    (huRegularity : FunctionRegularAt u t)
    (huSmooth : ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (htrace : ∀ x : M, traceTimeDerivMetricAt (I := I) G t x =
      (-2 : Real) * scalar t x)
    (hconj : ∀ x : M,
      deriv (fun s : Real => u s x) t =
        -ΔG (I := I) (G.metric t) ⟨_, huSmooth⟩ x + scalar t x * u t x) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, u s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      0 t := by
  have hvariation :=
    volume_variation_ricciFlow_at (I := I) (M := M) G scalar hg huRegularity htrace
  have hgreen :=
    integral_smul_laplacian_sub_eq_zero_family
      (I := I) (M := M) (fun s : Real => G.metric s)
      (f := fun _ : M => (1 : Real)) (h := u t)
      contMDiff_const huSmooth t
  have hlap :
      ∫ x, ΔG (I := I) (G.metric t) ⟨_, huSmooth⟩ x
        ∂(volumeMeasureFamily (I := I) (M := M) G t) = 0 := by
    have hconst (x : M) :
        ΔG (I := I) (G.metric t) ⟨fun _ : M => (1 : Real), contMDiff_const⟩ x = 0 := by
      convert Δ_g_const (I := I) (G.metric t) 1 x
      rfl
    simp only [one_mul, hconst, _root_.MulZeroClass.mul_zero, sub_zero] at hgreen
    change
      (∫ (x : M), ΔG (I := I) (G.metric t) ⟨u t, huSmooth⟩ x
        ∂(riemannianMeasureFamily (I := I) (M := M) (fun s => G.metric s) t)) = 0
    exact hgreen
  have hmass :
      (∫ x, (deriv (fun s : Real => u s x) t - scalar t x * u t x)
        ∂(volumeMeasureFamily (I := I) (M := M) G t)) = 0 := by
    calc
      (∫ x, (deriv (fun s : Real => u s x) t - scalar t x * u t x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t)) =
          ∫ x, -ΔG (I := I) (G.metric t) ⟨_, huSmooth⟩ x
            ∂(volumeMeasureFamily (I := I) (M := M) G t) := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [hconj x]
        ring
      _ = 0 := by rw [_root_.MeasureTheory.integral_neg, hlap, neg_zero]
  exact hvariation.congr_deriv hmass

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_mass_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_mass_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_mass_deriv ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_mass_deriv

theorem conj_heat_mass_eq
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily
      (I := I) (M := M) Real)
    (scalar u : Real → M → Real) {a b : Real} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) a)
    (huRegularity : FunctionRegularAt u a)
    (huSmooth : ∀ t ∈ Set.Icc a b,
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (htrace : ∀ t ∈ Set.Icc a b, ∀ x : M,
      traceTimeDerivMetricAt (I := I) G t x = (-2 : Real) * scalar t x)
    (hconj : ∀ (t : Real) (ht : t ∈ Set.Icc a b) (x : M),
      deriv (fun s : Real => u s x) t =
        -ΔG (I := I) (G.metric t) ⟨u t, huSmooth t ht⟩ x +
          scalar t x * u t x) :
    (∫ x, u b x ∂(volumeMeasureFamily (I := I) (M := M) G b)) =
      ∫ x, u a x ∂(volumeMeasureFamily (I := I) (M := M) G a) := by
  let mass : Real → Real := fun t =>
    ∫ x, u t x ∂(volumeMeasureFamily (I := I) (M := M) G t)
  have huRegularityAt : ∀ t : Real, FunctionRegularAt u t := fun _ =>
    { hasDerivAt_time := huRegularity.hasDerivAt_time
      continuous_joint := huRegularity.continuous_joint
      continuous_deriv_joint := huRegularity.continuous_deriv_joint }
  have hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt mass 0 t := by
    intro t ht
    simpa only [mass] using
      conj_heat_mass_deriv (I := I) (M := M) G scalar u (t := t)
        (hg.at_any t) (huRegularityAt t) (huSmooth t ht) (htrace t ht)
        (hconj t ht)
  have hdiff : DifferentiableOn Real mass (Set.Icc a b) := by
    intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  have hconst : ∀ t ∈ Set.Icc a b, mass t = mass a :=
    constant_of_has_deriv_right_zero hdiff.continuousOn (fun t ht =>
      (hderiv t ⟨ht.1, le_of_lt ht.2⟩).hasDerivWithinAt)
  simpa only [mass] using hconst b (Set.right_mem_Icc.mpr hab)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_mass_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_mass_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_mass_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_mass_eq

theorem conj_heat_mass_one
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily
      (I := I) (M := M) Real)
    (scalar u : Real → M → Real) {a b : Real}
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) a)
    (huRegularity : FunctionRegularAt u a)
    (huSmooth : ∀ t ∈ Set.Icc a b,
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (htrace : ∀ t ∈ Set.Icc a b, ∀ x : M,
      traceTimeDerivMetricAt (I := I) G t x = (-2 : Real) * scalar t x)
    (hconj : ∀ (t : Real) (ht : t ∈ Set.Icc a b) (x : M),
      deriv (fun s : Real => u s x) t =
        -ΔG (I := I) (G.metric t) ⟨u t, huSmooth t ht⟩ x +
          scalar t x * u t x)
    (hmass : (∫ x, u b x ∂(volumeMeasureFamily (I := I) (M := M) G b)) = 1) :
    ∀ t ∈ Set.Icc a b,
      (∫ x, u t x ∂(volumeMeasureFamily (I := I) (M := M) G t)) = 1 := by
  intro t ht
  have huRegularityAt : FunctionRegularAt u t :=
    { hasDerivAt_time := huRegularity.hasDerivAt_time
      continuous_joint := huRegularity.continuous_joint
      continuous_deriv_joint := huRegularity.continuous_deriv_joint }
  have hmass_eq :=
    conj_heat_mass_eq (I := I) (M := M) G scalar u ht.2
      (hg.at_any t) huRegularityAt
      (fun s hs => huSmooth s ⟨ht.1.trans hs.1, hs.2⟩)
      (fun s hs x => htrace s ⟨ht.1.trans hs.1, hs.2⟩ x)
      (fun s hs x => by
        simpa using hconj s ⟨ht.1.trans hs.1, hs.2⟩ x)
  calc
    (∫ x, u t x ∂(volumeMeasureFamily (I := I) (M := M) G t)) =
        ∫ x, u b x ∂(volumeMeasureFamily (I := I) (M := M) G b) := hmass_eq.symm
    _ = 1 := hmass

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_mass_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_mass_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_mass_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conj_heat_mass_one

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
