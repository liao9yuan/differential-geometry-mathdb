import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def IsMetricCompatibleOn
    (cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    (g : SmoothRiemannianMetric I M) (s : Set M := Set.univ) : Prop :=
  ∀ ⦃Y Z : Π x : M, TangentSpace I x⦄ ⦃x : M⦄,
    MDiffAt (T% Y) x → MDiffAt (T% Z) x → x ∈ s →
    ∀ v : TangentSpace I x,
      (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
        g.inner x (cov Y x v) (Z x) + g.inner x (Y x) (cov Z x v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn

def IsMetricCompatible (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) : Prop :=
  IsMetricCompatibleOn cov.toFun g Set.univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatible ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatible

def metricCompatibleDifferential
    (g : SmoothRiemannianMetric I M) {x : M}
    (covY : TangentSpace I x →L[ℝ] TangentSpace I x)
    (covZ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (Yx Zx : TangentSpace I x) : TangentSpace I x →L[ℝ] ℝ :=
  (g.inner x Zx).comp covY + (g.inner x Yx).comp covZ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricCompatibleDifferential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricCompatibleDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricCompatibleDifferential ``Submission.DifferentialGeometry.Geometry.Connection.metricCompatibleDifferential

omit [FiniteDimensional ℝ E] in
@[simp]
lemma metricCompatibleDifferential_apply
    (g : SmoothRiemannianMetric I M) {x : M}
    (covY : TangentSpace I x →L[ℝ] TangentSpace I x)
    (covZ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (Yx Zx : TangentSpace I x) (v : TangentSpace I x) :
    metricCompatibleDifferential g covY covZ Yx Zx v =
      g.inner x Zx (covY v) + g.inner x Yx (covZ v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricCompatibleDifferential_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricCompatibleDifferential_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricCompatibleDifferential_apply ``Submission.DifferentialGeometry.Geometry.Connection.metricCompatibleDifferential_apply

namespace IsMetricCompatibleOn

variable
    {cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
    {g : SmoothRiemannianMetric I M}

omit [FiniteDimensional ℝ E] in
lemma mono {s t : Set M} (h : IsMetricCompatibleOn cov g t) (hst : s ⊆ t) :
    IsMetricCompatibleOn cov g s :=
  fun _Y _Z _x hY hZ hxs v => h hY hZ (hst hxs) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.mono ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.mono

omit [FiniteDimensional ℝ E] in
lemma iUnion {ι : Type*} {s : ι → Set M}
    (h : ∀ i, IsMetricCompatibleOn cov g (s i)) :
    IsMetricCompatibleOn cov g (⋃ i, s i) := by
  intro Y Z x hY hZ hx v
  obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
  exact h i hY hZ hxsi v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.iUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.iUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.iUnion ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.iUnion

omit [FiniteDimensional ℝ E] in
lemma swap {s : Set M} (h : IsMetricCompatibleOn cov g s)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hxs : x ∈ s)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Z b) (Y b)) x) v =
      g.inner x (cov Z x v) (Y x) + g.inner x (Z x) (cov Y x v) := by
  have hfun : (fun b => g.inner b (Z b) (Y b)) = (fun b => g.inner b (Y b) (Z b)) := by
    funext b; exact (g.symm b (Z b) (Y b))
  rw [hfun]
  have hYZ := h hY hZ hxs v
  rw [g.symm x (cov Z x v) (Y x), g.symm x (Z x) (cov Y x v),
      add_comm]
  exact hYZ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.swap ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.swap

omit [FiniteDimensional ℝ E] in
lemma apply {s : Set M} (h : IsMetricCompatibleOn cov g s)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hxs : x ∈ s)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
      g.inner x (cov Y x v) (Z x) + g.inner x (Y x) (cov Z x v) :=
  h hY hZ hxs v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.apply ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.apply

omit [FiniteDimensional ℝ E] in
lemma hasMFDerivAt {s : Set M} (h : IsMetricCompatibleOn cov g s)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hxs : x ∈ s)
    (hsmooth : MDifferentiableAt I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) :
    HasMFDerivAt I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x
      (metricCompatibleDifferential g (cov Y x) (cov Z x) (Y x) (Z x)) := by
  refine hsmooth.hasMFDerivAt.congr_mfderiv ?_
  ext v
  change (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
      g.inner x (Z x) (cov Y x v) + g.inner x (Y x) (cov Z x v)
  rw [h hY hZ hxs v, g.symm x (cov Y x v) (Z x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.hasMFDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.hasMFDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.hasMFDerivAt ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.hasMFDerivAt

end IsMetricCompatibleOn

namespace IsMetricCompatible

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
variable {g : SmoothRiemannianMetric I M}

omit [FiniteDimensional ℝ E] in
lemma apply (h : IsMetricCompatible cov g)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
      g.inner x (cov.toFun Y x v) (Z x) + g.inner x (Y x) (cov.toFun Z x v) :=
  h hY hZ (Set.mem_univ _) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatible.apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatible.apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatible.apply ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatible.apply

omit [FiniteDimensional ℝ E] in
lemma mvfderiv_inner (h : IsMetricCompatible cov g)
    {Y Z : ∀ x : M, TangentSpace I x} {x : M}
    (v : TangentSpace I x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    mvfderiv I (fun b => g.inner b (Y b) (Z b)) x v =
      g.inner x (cov.toFun Y x v) (Z x) +
        g.inner x (Y x) (cov.toFun Z x v) :=
  h.apply hY hZ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatible.mvfderiv_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatible.mvfderiv_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatible.mvfderiv_inner ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatible.mvfderiv_inner

omit [FiniteDimensional ℝ E] in
lemma swap (h : IsMetricCompatible cov g)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Z b) (Y b)) x) v =
      g.inner x (cov.toFun Z x v) (Y x) + g.inner x (Z x) (cov.toFun Y x v) :=
  IsMetricCompatibleOn.swap h hY hZ (Set.mem_univ _) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatible.swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatible.swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatible.swap ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatible.swap

omit [FiniteDimensional ℝ E] in
lemma hasMFDerivAt (h : IsMetricCompatible cov g)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hsmooth :
      MDifferentiableAt I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) :
    HasMFDerivAt I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x
      (metricCompatibleDifferential g (cov.toFun Y x) (cov.toFun Z x) (Y x) (Z x)) :=
  IsMetricCompatibleOn.hasMFDerivAt h hY hZ (Set.mem_univ _) hsmooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatible.hasMFDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatible.hasMFDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatible.hasMFDerivAt ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatible.hasMFDerivAt

omit [FiniteDimensional ℝ E] in
lemma toIsMetricCompatibleOn (h : IsMetricCompatible cov g) {s : Set M} :
    IsMetricCompatibleOn cov.toFun g s :=
  IsMetricCompatibleOn.mono (t := Set.univ) h (fun _ _ => trivial)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatible.toIsMetricCompatibleOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatible.toIsMetricCompatibleOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatible.toIsMetricCompatibleOn ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatible.toIsMetricCompatibleOn

omit [FiniteDimensional ℝ E] in
@[simp]
lemma toIsMetricCompatibleOn_univ_iff :
    IsMetricCompatibleOn cov.toFun g Set.univ ↔ IsMetricCompatible cov g := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatible.toIsMetricCompatibleOn_univ_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatible.toIsMetricCompatibleOn_univ_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatible.toIsMetricCompatibleOn_univ_iff ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatible.toIsMetricCompatibleOn_univ_iff

end IsMetricCompatible

omit [FiniteDimensional ℝ E] in
lemma IsMetricCompatibleOn.toIsMetricCompatible
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {g : SmoothRiemannianMetric I M}
    (h : IsMetricCompatibleOn cov.toFun g Set.univ) :
    IsMetricCompatible cov g := h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.toIsMetricCompatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.toIsMetricCompatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.toIsMetricCompatible ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricCompatibleOn.toIsMetricCompatible

end Connection
end Geometry
end DifferentialGeometry
