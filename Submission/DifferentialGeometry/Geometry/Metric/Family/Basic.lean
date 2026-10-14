import Submission.DifferentialGeometry.Analysis.Time
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Defs
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.BallMonotonicity
import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Submission.DifferentialGeometry.Analysis.TimeInterval
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import Submission.DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import Submission.DifferentialGeometry.Geometry.Metric.QuadraticBounds.TimeSlab
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


set_option autoImplicit false

open _root_.Submission.DifferentialGeometry.Analysis
namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

structure MetricConnectionFamily (Time : Type*) where
  metric : Time -> SmoothRiemannianMetric I M
  connection : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _)
  metricCompatible : forall t : Time,
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) (connection t)
      (metric t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily

structure MetricConnectionFamilyOn (D : RealTimeInterval) where
  metric : Real -> SmoothRiemannianMetric I M
  connection : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)
  metricCompatible : forall t : RealTimeInterval.FlowTime D,
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I)
      (connection (t : Real)) (metric (t : Real))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn

namespace MetricConnectionFamily

def restrict
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (D : RealTimeInterval) :
    MetricConnectionFamilyOn (I := I) (M := M) D where
  metric := G.metric
  connection := G.connection
  metricCompatible := fun t => G.metricCompatible (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily.restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily.restrict ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily.restrict

@[simp] theorem restrict_metric
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (D : RealTimeInterval) (t : Real) :
    (G.restrict D).metric t = G.metric t := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily.restrict_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily.restrict_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily.restrict_metric ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily.restrict_metric

@[simp] theorem restrict_connection
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (D : RealTimeInterval) (t : Real) :
    (G.restrict D).connection t = G.connection t := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily.restrict_connection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily.restrict_connection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily.restrict_connection ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily.restrict_connection

end MetricConnectionFamily

namespace MetricConnectionFamilyOn


def toFlowTimeFamily
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) :
    MetricConnectionFamily (I := I) (M := M) (RealTimeInterval.FlowTime D) where
  metric := fun t => G.metric (t : Real)
  connection := fun t => G.connection (t : Real)
  metricCompatible := fun t => G.metricCompatible t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.toFlowTimeFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.toFlowTimeFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.toFlowTimeFamily ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.toFlowTimeFamily


def toRegularTimeFamily
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) :
    MetricConnectionFamily (I := I) (M := M) (RealTimeInterval.RegularTime D) where
  metric := fun t => G.metric (t : Real)
  connection := fun t => G.connection (t : Real)
  metricCompatible := fun t => G.metricCompatible (RealTimeInterval.regularToFlow t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.toRegularTimeFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.toRegularTimeFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.toRegularTimeFamily ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.toRegularTimeFamily


def metricAt
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    SmoothRiemannianMetric I M :=
  G.metric (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricAt ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricAt


def connectionAt
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    CovariantDerivative I E (TangentSpace I : M -> Type _) :=
  G.connection (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.connectionAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.connectionAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.connectionAt ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.connectionAt

@[simp] theorem metricAt_eq
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    G.metricAt t = G.metric (t : Real) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricAt_eq ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricAt_eq

@[simp] theorem connectionAt_eq
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    G.connectionAt t = G.connection (t : Real) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.connectionAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.connectionAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.connectionAt_eq ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.connectionAt_eq


theorem metricCompatibleAt
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) (G.connectionAt t)
      (G.metricAt t) := by
  exact G.metricCompatible t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricCompatibleAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricCompatibleAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricCompatibleAt ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricCompatibleAt


theorem metricCompatibleAt_regular
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.RegularTime D) :
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I)
      (G.connection (t : Real)) (G.metric (t : Real)) := by
  exact G.metricCompatible (RealTimeInterval.regularToFlow t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricCompatibleAt_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricCompatibleAt_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricCompatibleAt_regular ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricCompatibleAt_regular

end MetricConnectionFamilyOn

section TimeSmoothness

variable {A Time : Type*} [CommRing A] [Algebra Real A]

def metricFamilySmoothInTime
    (td : TimeDerivativeData Real A Time) [TimeRegularFam td]
    (G : MetricConnectionFamily (I := I) (M := M) Time) : Prop :=
  forall (x : M) (X Y : TangentSpace I x),
    td.isSmoothFam (fun t : Time => (G.metric t).inner x X Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricFamilySmoothInTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricFamilySmoothInTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricFamilySmoothInTime ``Submission.DifferentialGeometry.Geometry.Curvature.metricFamilySmoothInTime


theorem metric_smooth_coeff_of_metricFamilySmoothInTime
    (td : TimeDerivativeData Real A Time) [TimeRegularFam td]
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (hG : metricFamilySmoothInTime td G)
    (x : M) (X Y : TangentSpace I x) :
    td.isSmoothFam (fun t : Time => (G.metric t).inner x X Y) :=
  hG x X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metric_smooth_coeff_of_metricFamilySmoothInTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metric_smooth_coeff_of_metricFamilySmoothInTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metric_smooth_coeff_of_metricFamilySmoothInTime ``Submission.DifferentialGeometry.Geometry.Curvature.metric_smooth_coeff_of_metricFamilySmoothInTime


noncomputable def metricTimeDerivative
    (td : TimeDerivativeData Real A Time)
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (x : M) (X Y : TangentSpace I x) : Real :=
  td.dtApply (fun s : Time => (G.metric s).inner x X Y) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricTimeDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricTimeDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricTimeDerivative ``Submission.DifferentialGeometry.Geometry.Curvature.metricTimeDerivative

@[simp] theorem metricTimeDerivative_eq
    (td : TimeDerivativeData Real A Time)
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (x : M) (X Y : TangentSpace I x) :
    metricTimeDerivative td G t x X Y =
      td.dtApply (fun s : Time => (G.metric s).inner x X Y) t := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricTimeDerivative_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricTimeDerivative_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricTimeDerivative_eq ``Submission.DifferentialGeometry.Geometry.Curvature.metricTimeDerivative_eq

end TimeSmoothness

section IntervalSmoothness

variable [FiniteDimensional Real E]

def tensor0SFamilyContinuousOnSet
    (s : Nat) (K : Set Real)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    Prop :=
  Continuous (fun q : {t : Real // t ∈ K} × M =>
    TotalSpace.mk' (Tensor0SModel s Real E)
      (E := fun x : M => Tensor0SSpace s I x) q.2 (A q.1.1 q.2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet

abbrev SmoothTwoTensorFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.SmoothTwoTensorFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.SmoothTwoTensorFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.SmoothTwoTensorFamily ``Submission.DifferentialGeometry.Geometry.Curvature.SmoothTwoTensorFamily

structure SmoothTwoTensorFamilyOnSet
    (K : Set Real) (A : SmoothTwoTensorFamily (I := I) (M := M)) : Prop where
  coeff :
    ∀ (x : M) (X Y : TangentSpace I x),
      ContDiffOn Real ⊤
        (fun t : Real => A t x (fun i : Fin 2 => if i = 0 then X else Y)) K
  tensor_cont :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => A t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.SmoothTwoTensorFamilyOnSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.SmoothTwoTensorFamilyOnSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.SmoothTwoTensorFamilyOnSet ``Submission.DifferentialGeometry.Geometry.Curvature.SmoothTwoTensorFamilyOnSet

namespace tensor0SFamilyContinuousOnSet


theorem mono
    {s : Nat} {K L : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s L A)
    (hKL : K ⊆ L) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A := by
  unfold tensor0SFamilyContinuousOnSet at hA ⊢
  let incl : {t : Real // t ∈ K} × M -> {t : Real // t ∈ L} × M :=
    fun q => (⟨q.1.1, hKL q.1.2⟩, q.2)
  have htime : Continuous (fun q : {t : Real // t ∈ K} × M =>
      (⟨q.1.1, hKL q.1.2⟩ : {t : Real // t ∈ L})) := by
    exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _)
  have hincl : Continuous incl := by
    dsimp [incl]
    exact htime.prodMk continuous_snd
  exact hA.comp hincl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.mono ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.mono


theorem comp_time
    {s : Nat} {K L : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s L A)
    {φ : Real -> Real} (hφ : Continuous φ) (hmaps : Set.MapsTo φ K L) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => A (φ t) x) := by
  unfold tensor0SFamilyContinuousOnSet at hA ⊢
  let pull : {t : Real // t ∈ K} × M -> {t : Real // t ∈ L} × M :=
    fun q => (⟨φ q.1.1, hmaps q.1.2⟩, q.2)
  have htime : Continuous (fun q : {t : Real // t ∈ K} × M =>
      (⟨φ q.1.1, hmaps q.1.2⟩ : {t : Real // t ∈ L})) := by
    exact ((hφ.comp (continuous_subtype_val.comp continuous_fst)).subtype_mk _)
  have hpull : Continuous pull := by
    dsimp [pull]
    exact htime.prodMk continuous_snd
  exact hA.comp hpull

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.comp_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.comp_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.comp_time ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.comp_time

theorem of_union_closedOpen
    {s : Nat} {a c b : Real} (hac : a < c)
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (h1 : tensor0SFamilyContinuousOnSet (I := I) (M := M) s (Set.Ico a c) A)
    (h2 : tensor0SFamilyContinuousOnSet (I := I) (M := M) s (Set.Ioo a b) A) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s (Set.Ico a b) A := by
  unfold tensor0SFamilyContinuousOnSet at h1 h2 ⊢
  rw [continuous_iff_continuousAt]
  rintro q
  rcases lt_or_ge (q.1.1 : Real) c with hlt | hge
  · have hopen : IsOpen {q' : {t : Real // t ∈ Set.Ico a b} × M | (q'.1.1 : Real) < c} :=
      isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const
    have hcont : ContinuousOn
        (fun q' : {t : Real // t ∈ Set.Ico a b} × M =>
          TotalSpace.mk' (Tensor0SModel s Real E)
            (E := fun x : M => Tensor0SSpace s I x) q'.2 (A q'.1.1 q'.2))
        {q' : {t : Real // t ∈ Set.Ico a b} × M | (q'.1.1 : Real) < c} := by
      rw [continuousOn_iff_continuous_domRestrict]
      refine h1.comp (f := fun w : {q' : {t : Real // t ∈ Set.Ico a b} × M //
          (q'.1.1 : Real) < c} =>
          (⟨w.1.1.1, Set.mem_Ico.mpr ⟨(Set.mem_Ico.mp w.1.1.2).1, w.2⟩⟩, w.1.2)) ?_
      exact (((continuous_subtype_val.comp continuous_fst).comp
        continuous_subtype_val).subtype_mk _).prodMk
        (continuous_snd.comp continuous_subtype_val)
    exact hcont.continuousAt (hopen.mem_nhds hlt)
  · have hopen : IsOpen {q' : {t : Real // t ∈ Set.Ico a b} × M | a < (q'.1.1 : Real)} :=
      isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)
    have hcont : ContinuousOn
        (fun q' : {t : Real // t ∈ Set.Ico a b} × M =>
          TotalSpace.mk' (Tensor0SModel s Real E)
            (E := fun x : M => Tensor0SSpace s I x) q'.2 (A q'.1.1 q'.2))
        {q' : {t : Real // t ∈ Set.Ico a b} × M | a < (q'.1.1 : Real)} := by
      rw [continuousOn_iff_continuous_domRestrict]
      refine h2.comp (f := fun w : {q' : {t : Real // t ∈ Set.Ico a b} × M //
          a < (q'.1.1 : Real)} =>
          (⟨w.1.1.1, Set.mem_Ioo.mpr ⟨w.2, (Set.mem_Ico.mp w.1.1.2).2⟩⟩, w.1.2)) ?_
      exact (((continuous_subtype_val.comp continuous_fst).comp
        continuous_subtype_val).subtype_mk _).prodMk
        (continuous_snd.comp continuous_subtype_val)
    exact hcont.continuousAt (hopen.mem_nhds (lt_of_lt_of_le hac hge))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.of_union_closedOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.of_union_closedOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.of_union_closedOpen ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.of_union_closedOpen

theorem congr
    {s : Nat} {K : Set Real}
    {A B : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A)
    (hAB : ∀ t ∈ K, ∀ x : M, A t x = B t x) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s K B := by
  unfold tensor0SFamilyContinuousOnSet at hA ⊢
  refine hA.congr (fun q => ?_)
  rw [hAB q.1.1 q.1.2 q.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.congr ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.congr


theorem const_smul
    {s : Nat} {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (c : Real)
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => c • A t x) := by
  let := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) s
  unfold tensor0SFamilyContinuousOnSet at hA ⊢
  rw [continuous_iff_continuousAt] at hA ⊢
  intro q
  have hAq := hA q
  rw [FiberBundle.continuousAt_totalSpace] at hAq ⊢
  refine ⟨hAq.1, ?_⟩
  set e := _root_.FiberBundle.trivializationAt (Tensor0SModel s Real E)
    (fun x => Tensor0SSpace s I x) q.2 with he
  have hbase : ∀ᶠ x in nhds q, x.2 ∈ e.baseSet :=
    continuousAt_snd (e.open_baseSet.mem_nhds (by
      rw [he]
      exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ q.2))
  refine (hAq.2.const_smul c).congr_of_eventuallyEq ?_
  filter_upwards [hbase] with x hx
  exact (e.linear Real hx).map_smul c (A x.1.1 x.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.const_smul ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.const_smul


theorem add
    {s : Nat} {K : Set Real}
    {A B : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A)
    (hB : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K B) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => A t x + B t x) := by
  let := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) s
  unfold tensor0SFamilyContinuousOnSet at hA hB ⊢
  rw [continuous_iff_continuousAt] at hA hB ⊢
  intro q
  have hAq := hA q
  have hBq := hB q
  rw [FiberBundle.continuousAt_totalSpace] at hAq hBq ⊢
  refine ⟨hAq.1, ?_⟩
  set e := _root_.FiberBundle.trivializationAt (Tensor0SModel s Real E)
    (fun x => Tensor0SSpace s I x) q.2 with he
  have hbase : ∀ᶠ x in nhds q, x.2 ∈ e.baseSet :=
    continuousAt_snd (e.open_baseSet.mem_nhds (by
      rw [he]
      exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ q.2))
  refine (hAq.2.add hBq.2).congr_of_eventuallyEq ?_
  filter_upwards [hbase] with x hx
  exact (e.linear Real hx).map_add (A x.1.1 x.2) (B x.1.1 x.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.add ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.add

theorem smul
    {s : Nat} {K : Set Real}
    {f : Real -> M -> Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hf : Continuous (fun q : {t : Real // t ∈ K} × M => f q.1.1 q.2))
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => f t x • A t x) := by
  let := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) s
  unfold tensor0SFamilyContinuousOnSet at hA ⊢
  rw [continuous_iff_continuousAt] at hA ⊢
  intro q
  have hAq := hA q
  have hfq : ContinuousAt (fun q : {t : Real // t ∈ K} × M => f q.1.1 q.2) q :=
    hf.continuousAt
  rw [FiberBundle.continuousAt_totalSpace] at hAq ⊢
  refine ⟨hAq.1, ?_⟩
  set e := _root_.FiberBundle.trivializationAt (Tensor0SModel s Real E)
    (fun x => Tensor0SSpace s I x) q.2 with he
  have hbase : ∀ᶠ x in nhds q, x.2 ∈ e.baseSet :=
    continuousAt_snd (e.open_baseSet.mem_nhds (by
      rw [he]
      exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ q.2))
  refine (hfq.smul hAq.2).congr_of_eventuallyEq ?_
  filter_upwards [hbase] with x hx
  exact (e.linear Real hx).map_smul (f x.1.1 x.2) (A x.1.1 x.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.smul ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.smul

theorem tangentBundle
    {s : Nat} {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel s Real E)
        (E := fun x : M => Tensor0SSpace s I x) q.2.proj
        (A q.1.1 q.2.proj)) := by
  unfold tensor0SFamilyContinuousOnSet at hA
  let pull : {t : Real // t ∈ K} × TangentBundle I M -> {t : Real // t ∈ K} × M :=
    fun q => (q.1, q.2.proj)
  have hpull : Continuous pull := by
    dsimp [pull]
    exact continuous_fst.prodMk
      ((FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_snd)
  exact hA.comp hpull

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.tangentBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.tangentBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.tangentBundle ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.tangentBundle

theorem eval_continuous
    {s : Nat} {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A)
    {P : Type*} [TopologicalSpace P]
    {τ : P -> Real} {b : P -> M}
    (hτ : Continuous τ) (hτK : ∀ p : P, τ p ∈ K)
    (hb : Continuous b)
    {v : Fin s -> (p : P) -> TangentSpace I (b p)}
    (hv : ∀ i : Fin s, Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b p) (v i p))) :
    Continuous (fun p : P => A (τ p) (b p) (fun i : Fin s => v i p)) := by
  let T : (p : P) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s (b p) :=
    fun p => A (τ p) (b p)
  have hT : Continuous (fun p : P =>
      TotalSpace.mk' (Tensor0SModel s Real E)
        (E := fun x : M => Tensor0SSpace s I x) (b p) (T p)) := by
    unfold tensor0SFamilyContinuousOnSet at hA
    let pull : P -> {t : Real // t ∈ K} × M :=
      fun p => (⟨τ p, hτK p⟩, b p)
    have hpull : Continuous pull := by
      dsimp [pull]
      exact ((hτ.subtype_mk _).prodMk hb)
    let h : Continuous (fun p : P =>
        TotalSpace.mk' (Tensor0SModel s Real E)
          (E := fun x : M => Tensor0SSpace s I x) (b p) (T p)) := hA.comp hpull
    exact h
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M) (P := P) (n := s)
    b hb T hT v hv
  let h : Continuous (fun p : P => A (τ p) (b p) (fun i : Fin s => v i p)) := hEval
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.eval_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.eval_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.eval_continuous ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.eval_continuous

end tensor0SFamilyContinuousOnSet

theorem tensor0SFamily_quadCont
    {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K A) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      quad02 (I := I) (M := M) (A q.1.1 q.2.proj) q.2.2) := by
  let P := {t : Real // t ∈ K} × TangentBundle I M
  let b : P -> M := fun q => q.2.proj
  let T : (q : P) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (b q) :=
    fun q => A q.1.1 (b q)
  let v : Fin 2 -> (q : P) -> TangentSpace I (b q) :=
    fun _ q => q.2.2
  have hb : Continuous b := by
    dsimp [b]
    exact (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_snd
  have hT : Continuous (fun q : P =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) (b q) (T q)) := by
    simpa [P, b, T] using
      tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M) hA
  have hv : ∀ i : Fin 2, Continuous (fun q : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b q) (v i q)) := by
    intro i
    simpa [P, b, v] using (continuous_snd :
      Continuous (fun q : P => (q.2 : TangentBundle I M)))
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M) (P := P) (n := 2)
    b hb T hT v hv
  let h : Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      quad02 (I := I) (M := M) (A q.1.1 q.2.proj) q.2.2) := hEval
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SFamily_quadCont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SFamily_quadCont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SFamily_quadCont ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SFamily_quadCont

structure MetricFamilySmoothOn
    (D : RealTimeInterval)
    (g_fam : ℝ → SmoothRiemannianMetric I M) : Prop where
  coeff :
    forall (x : M) (X Y : TangentSpace I x),
    ContDiffOn Real ∞ (fun t : Real => (g_fam t).inner x X Y) D.regular
  coeff_cont :
    forall (x : M) (X Y : TangentSpace I x),
    ContinuousOn (fun t : Real => (g_fam t).inner x X Y) D.carrier
  metricTensor_cont :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => metricTensorField (I := I) (g_fam t) x)
  frameCompSmooth :
    forall {Idx : Type} [Fintype Idx]
      (frame : Idx -> (x : M) -> TangentSpace I x) {u : Set M},
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u ->
      forall i j : Idx,
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M =>
            (g_fam p.1).inner p.2 (frame i p.2) (frame j p.2))
          (D.regular ×ˢ u)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn


theorem metric_smooth_coeff_of_metricFamilySmoothOn
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (x : M) (X Y : TangentSpace I x) :
    ContDiffOn Real ∞ (fun t : Real => (g_fam t).inner x X Y) D.regular :=
  hG.coeff x X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metric_smooth_coeff_of_metricFamilySmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metric_smooth_coeff_of_metricFamilySmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metric_smooth_coeff_of_metricFamilySmoothOn ``Submission.DifferentialGeometry.Geometry.Curvature.metric_smooth_coeff_of_metricFamilySmoothOn


theorem metric_coeff_cont_of_metricFamilySmoothOn
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (x : M) (X Y : TangentSpace I x) :
    ContinuousOn (fun t : Real => (g_fam t).inner x X Y) D.carrier :=
  hG.coeff_cont x X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metric_coeff_cont_of_metricFamilySmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metric_coeff_cont_of_metricFamilySmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metric_coeff_cont_of_metricFamilySmoothOn ``Submission.DifferentialGeometry.Geometry.Curvature.metric_coeff_cont_of_metricFamilySmoothOn


theorem metricTensor_cont_of_metricFamilySmoothOn
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => metricTensorField (I := I) (g_fam t) x) :=
  hG.metricTensor_cont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricTensor_cont_of_metricFamilySmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricTensor_cont_of_metricFamilySmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricTensor_cont_of_metricFamilySmoothOn ``Submission.DifferentialGeometry.Geometry.Curvature.metricTensor_cont_of_metricFamilySmoothOn


theorem metricTensor_cont_restrict_of_metricFamilySmoothOn
    {D : RealTimeInterval} {K : Set Real}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (hK : K ⊆ D.carrier) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricTensorField (I := I) (g_fam t) x) :=
  tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
    hG.metricTensor_cont hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricTensor_cont_restrict_of_metricFamilySmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricTensor_cont_restrict_of_metricFamilySmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricTensor_cont_restrict_of_metricFamilySmoothOn ``Submission.DifferentialGeometry.Geometry.Curvature.metricTensor_cont_restrict_of_metricFamilySmoothOn


theorem metricTensor_tangentBundle_cont_of_metricFamilySmoothOn
    {D : RealTimeInterval} {K : Set Real}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (hK : K ⊆ D.carrier) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
        (metricTensorField (I := I) (g_fam q.1.1) q.2.proj)) :=
  tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M)
    (metricTensor_cont_restrict_of_metricFamilySmoothOn (I := I) (M := M)
      g_fam hG hK)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricTensor_tangentBundle_cont_of_metricFamilySmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricTensor_tangentBundle_cont_of_metricFamilySmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricTensor_tangentBundle_cont_of_metricFamilySmoothOn ``Submission.DifferentialGeometry.Geometry.Curvature.metricTensor_tangentBundle_cont_of_metricFamilySmoothOn

theorem metricTimeBundleQuad_cont_of_metricFamilySmoothOn
    {D : RealTimeInterval} {K : Set Real}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (hK : K ⊆ D.carrier) :
    Continuous
      (metricTimeBundleQuad (I := I) (M := M) g_fam K) := by
  have hquad :=
    tensor0SFamily_quadCont (I := I) (M := M)
      (metricTensor_cont_restrict_of_metricFamilySmoothOn (I := I) (M := M)
        g_fam hG hK)
  let h : Continuous
      (metricTimeBundleQuad (I := I) (M := M) g_fam K) := hquad
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricTimeBundleQuad_cont_of_metricFamilySmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricTimeBundleQuad_cont_of_metricFamilySmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricTimeBundleQuad_cont_of_metricFamilySmoothOn ``Submission.DifferentialGeometry.Geometry.Curvature.metricTimeBundleQuad_cont_of_metricFamilySmoothOn


noncomputable def metricCoeff
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (x : M) (X Y : TangentSpace I x) : Real -> Real :=
  fun t => (g_fam t).inner x X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricCoeff ``Submission.DifferentialGeometry.Geometry.Curvature.metricCoeff

omit [FiniteDimensional ℝ E] in
@[simp] theorem metricCoeff_eq
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (x : M) (X Y : TangentSpace I x) (t : Real) :
    metricCoeff g_fam x X Y t = (g_fam t).inner x X Y := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricCoeff_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricCoeff_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricCoeff_eq ``Submission.DifferentialGeometry.Geometry.Curvature.metricCoeff_eq

end IntervalSmoothness

end DifferentialGeometry.Geometry.Curvature
