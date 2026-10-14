import Submission.DifferentialGeometry.Topology.Attachment.TransitionGluing
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.LimitDomains
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.LimitIdentities
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.CenterClassification

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]
  [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [∀ k, PseudoEMetricSpace (M k)] [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

def IntrinsicBallChart.bufferedTransitionGlueData
    {ι : Type uE} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in _root_.Filter.atTop,
      (near i j = _root_.Bool.true → _root_.EDist.edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = _root_.Bool.false → ENNReal.ofReal (ρ / 4) ≤ _root_.EDist.edist (x i k) (x j k)))
    (J : {a : ι × ι // near a.1 a.2 = _root_.Bool.true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a)) :
    TopCat.GlueData.{uE} := by
  have hrefl : ∀ i, near i i = true := by
    intro i
    apply EMetric.eq_true_self_of_eventually_edist_lt_or_ge x (l := _root_.Filter.atTop)
      (by positivity : 0 < ENNReal.ofReal (ρ / 4)) near hclass i
  have hsymm : ∀ i j, near i j = _root_.Bool.true → near j i = true := by
    intro i j hij
    have hs := EMetric.eq_swap_of_eventually_edist_lt_or_ge x (l := _root_.Filter.atTop) near hclass i j
    rw [← hs]
    exact hij
  let U : Set E := Metric.ball (0 : E) (ρ / 8)
  have hU : IsOpen U := Metric.isOpen_ball
  have hsub : U ⊆ Metric.ball (0 : E) (ρ / 2) := Metric.ball_subset_ball (by linarith)
  have hself : ∀ i z, z ∈ U → J ⟨(i,i),hrefl i⟩ z = z := by
    intro i z hz
    have heq := NormalBallChart.transition_limit_self
      (fun k => (c i k).toNormalBallChart (g k) (hEnorm k) (x i k) hρ)
      (hconv ⟨(i,i),hrefl i⟩) (fun z hz => Filter.Eventually.of_forall (fun k => by
        change z ∈ (c i k).hom.source
        rw [(c i k).source_eq]
        exact Metric.ball_subset_ball (by linarith) hz))
    exact heq (hsub hz)
  have hinv : ∀ i j (h : near i j = _root_.Bool.true) z, z ∈ U → J ⟨(i,j),h⟩ z ∈ U →
      J ⟨(j,i),hsymm i j h⟩ (J ⟨(i,j),h⟩ z) = z := by
    intro i j hij z hz _
    have hnear : ∀ᶠ k in _root_.Filter.atTop, _root_.EDist.edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4) :=
      (hclass i j).mono fun k hk => hk.1 hij
    have hi := IntrinsicBallChart.transition_limit_inverse_on_ball_of_lt g hEnorm (x i) (x j) hρ
      (c i) (c j) (s := ρ / 8) (by positivity) (by linarith) (hconv ⟨(i,j),hij⟩) (hconv ⟨(j,i),hsymm i j hij⟩)
      (hcont ⟨(i,j),hij⟩) (hcont ⟨(j,i),hsymm i j hij⟩) hnear
    exact hi.1 hz
  have htrans : ∀ i j k (hij : near i j = _root_.Bool.true) (hjk : near j k = _root_.Bool.true) z,
      z ∈ U → J ⟨(i,j),hij⟩ z ∈ U → J ⟨(j,k),hjk⟩ (J ⟨(i,j),hij⟩ z) ∈ U →
      ∃ hik : near i k = _root_.Bool.true,
        J ⟨(i,k),hik⟩ z = J ⟨(j,k),hjk⟩ (J ⟨(i,j),hij⟩ z) := by
    intro i j k hij hjk z hz h1 h2
    exact IntrinsicBallChart.transition_limit_trans_on_ball g hEnorm x hρ c near hclass J hcont hconv (s := ρ / 8) (by positivity) le_rfl hij hjk hz h1 h2
  exact TopCat.GlueData.ofTransitionMaps (U := U) (hU := hU) (near := near) (J := J)
    (hJ := fun a => (hcont a).mono hsub) (hrefl := hrefl) (hsymm := hsymm)
    (hself := hself) (hinv := hinv) (htrans := htrans)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData
variable
    {ι : Type uE} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))

theorem IntrinsicBallChart.bufferedTransitionGlueData_index :
    (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).J = ι := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_index ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_index

theorem IntrinsicBallChart.bufferedTransitionGlueData_patch (i : ι) :
    (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).U i =
      TopCat.of (Metric.ball (0 : E) (ρ / 8)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_patch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_patch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_patch ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_patch

theorem IntrinsicBallChart.bufferedTransitionGlueData_overlap (i j : ι) :
    (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).V (i,j) =
      TopCat.of {z : Metric.ball (0 : E) (ρ / 8) |
        ∃ h : near i j = _root_.Bool.true, J ⟨(i,j),h⟩ z ∈ Metric.ball (0 : E) (ρ / 8)} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_overlap ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_overlap

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]
  [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [∀ k, PseudoEMetricSpace (M k)] [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

variable
    {N : ℕ} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : (Fin (N + 1)) → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : (Fin (N + 1)) → (Fin (N + 1)) → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : (Fin (N + 1)) × (Fin (N + 1)) // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))


def IntrinsicBallChart.finiteBufferedTransitionGlueData : TopCat.GlueData.{uE} :=
  IntrinsicBallChart.bufferedTransitionGlueData g hEnorm
    (fun i : ULift.{uE} (Fin (N + 1)) => x i.down) hρ
    (fun i k => c i.down k) (fun i j => near i.down j.down)
    (fun i j => hclass i.down j.down)
    (fun a => J ⟨(a.1.1.down, a.1.2.down), a.2⟩)
    (fun a => hcont ⟨(a.1.1.down, a.1.2.down), a.2⟩)
    (fun a => hconv ⟨(a.1.1.down, a.1.2.down), a.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData

theorem IntrinsicBallChart.finiteBufferedTransitionGlueData_index :
    (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).J =
      ULift.{uE} (Fin (N + 1)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_index ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_index

theorem IntrinsicBallChart.finiteBufferedTransitionGlueData_patch (i : ULift.{uE} (Fin (N + 1))) :
    (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).U i =
      TopCat.of (Metric.ball (0 : E) (ρ / 8)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_patch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_patch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_patch ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_patch

theorem IntrinsicBallChart.finiteBufferedTransitionGlueData_overlap (i j : ULift.{uE} (Fin (N + 1))) :
    (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).V (i,j) =
      TopCat.of {z : Metric.ball (0 : E) (ρ / 8) |
        ∃ h : near i.down j.down = _root_.Bool.true,
          J ⟨(i.down,j.down),h⟩ z ∈ Metric.ball (0 : E) (ρ / 8)} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_overlap ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_overlap

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]
  [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [∀ k, PseudoEMetricSpace (M k)] [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

variable
    {ι : Type uE} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))

theorem IntrinsicBallChart.bufferedTransitionGlueData_t2Space :
    T2Space (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued := by
  unfold IntrinsicBallChart.bufferedTransitionGlueData
  exact TopCat.GlueData.t2Space_ofTransitionMaps _ _ _ _ _ _ _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_t2Space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_t2Space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_t2Space ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueData_t2Space

def IntrinsicBallChart.transitionGlueCore :
    Set (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued :=
  ⋃ i, (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι i ''
    {z : Metric.ball (0 : E) (ρ / 8) | (z : E) ∈ Metric.ball 0 (ρ / 10)}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.transitionGlueCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.transitionGlueCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.transitionGlueCore ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.transitionGlueCore

def IntrinsicBallChart.transitionGlueCompactCore :
    Set (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued :=
  ⋃ i, Set.range (fun z : Metric.closedBall (0 : E) (ρ / 10) =>
    (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι i
      ⟨z, lt_of_le_of_lt z.property (by linarith : ρ / 10 < ρ / 8)⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.transitionGlueCompactCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.transitionGlueCompactCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.transitionGlueCompactCore ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.transitionGlueCompactCore

theorem IntrinsicBallChart.isOpen_transitionGlueCore :
    IsOpen (IntrinsicBallChart.transitionGlueCore g hEnorm x hρ c near hclass J hcont hconv) := by
  apply isOpen_iUnion
  intro i
  apply (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).ι_isOpenEmbedding i |>.isOpenMap
  exact Metric.isOpen_ball.preimage continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.isOpen_transitionGlueCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.isOpen_transitionGlueCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.isOpen_transitionGlueCore ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.isOpen_transitionGlueCore

theorem IntrinsicBallChart.zero_mem_transitionGlueCore (i : ι) :
    (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι i
      ⟨0, Metric.mem_ball_self (by positivity)⟩ ∈
      IntrinsicBallChart.transitionGlueCore g hEnorm x hρ c near hclass J hcont hconv := by
  exact mem_iUnion.mpr ⟨i, ⟨⟨0, Metric.mem_ball_self (by positivity)⟩,
    Metric.mem_ball_self (by positivity), rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.zero_mem_transitionGlueCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.zero_mem_transitionGlueCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.zero_mem_transitionGlueCore ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.zero_mem_transitionGlueCore

theorem IntrinsicBallChart.isCompact_transitionGlueCompactCore [Finite ι] :
    IsCompact (IntrinsicBallChart.transitionGlueCompactCore g hEnorm x hρ c near hclass J hcont hconv) := by
  let : Finite (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).J := by
    change Finite ι
    infer_instance
  apply isCompact_iUnion
  intro i
  apply isCompact_range
  apply ((IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι i).hom.continuous.comp
  exact continuous_subtype_val.subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.isCompact_transitionGlueCompactCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.isCompact_transitionGlueCompactCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.isCompact_transitionGlueCompactCore ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.isCompact_transitionGlueCompactCore

theorem IntrinsicBallChart.transitionGlueCore_subset_compactCore :
    IntrinsicBallChart.transitionGlueCore g hEnorm x hρ c near hclass J hcont hconv ⊆
      IntrinsicBallChart.transitionGlueCompactCore g hEnorm x hρ c near hclass J hcont hconv := by
  rintro z ⟨_, ⟨i, rfl⟩, ⟨w, hw, rfl⟩⟩
  exact mem_iUnion.mpr ⟨i, ⟨⟨(w : Metric.ball (0 : E) (ρ / 8)).val, Metric.ball_subset_closedBall hw⟩, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.transitionGlueCore_subset_compactCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.transitionGlueCore_subset_compactCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.transitionGlueCore_subset_compactCore ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.transitionGlueCore_subset_compactCore

theorem IntrinsicBallChart.isCompact_closure_transitionGlueCore [Finite ι] :
    IsCompact (closure (IntrinsicBallChart.transitionGlueCore g hEnorm x hρ c near hclass J hcont hconv)) := by
  let : T2Space (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued :=
    IntrinsicBallChart.bufferedTransitionGlueData_t2Space _ _ _ _ _ _ _ _ _ _
  have hK := IntrinsicBallChart.isCompact_transitionGlueCompactCore g hEnorm x hρ c near hclass J hcont hconv
  exact hK.of_isClosed_subset isClosed_closure
    (closure_minimal (IntrinsicBallChart.transitionGlueCore_subset_compactCore g hEnorm x hρ c near hclass J hcont hconv) hK.isClosed)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.isCompact_closure_transitionGlueCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.isCompact_closure_transitionGlueCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.isCompact_closure_transitionGlueCore ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.isCompact_closure_transitionGlueCore

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]
  [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [∀ k, PseudoEMetricSpace (M k)] [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

variable
    {N : ℕ} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : (Fin (N + 1)) → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : (Fin (N + 1)) → (Fin (N + 1)) → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : (Fin (N + 1)) × (Fin (N + 1)) // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))


theorem IntrinsicBallChart.finiteBufferedTransitionGlueData_t2Space :
    T2Space (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued := by
  unfold IntrinsicBallChart.finiteBufferedTransitionGlueData
  exact IntrinsicBallChart.bufferedTransitionGlueData_t2Space _ _ _ _ _ _ _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_t2Space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_t2Space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_t2Space ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_t2Space

theorem IntrinsicBallChart.finiteBufferedTransitionGlueData_secondCountableTopology :
    SecondCountableTopology (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued := by
  let D := IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
  let : Countable D.J := by
    change Countable (ULift.{uE} (Fin (N + 1)))
    infer_instance
  let : ∀ i : D.J, SecondCountableTopology (D.U i) := by
    intro i
    change SecondCountableTopology (Metric.ball (0 : E) (ρ / 8))
    infer_instance
  exact TopCat.GlueData.secondCountableTopology D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_secondCountableTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_secondCountableTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_secondCountableTopology ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.finiteBufferedTransitionGlueData_secondCountableTopology

def IntrinsicBallChart.bufferedTransitionGlueBasepoint :
    (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued :=
  (IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι
    (ULift.up 0) ⟨0, Metric.mem_ball_self (by positivity)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueBasepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueBasepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueBasepoint ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueBasepoint

theorem IntrinsicBallChart.bufferedTransitionGlueBasepoint_mem_range :
    IntrinsicBallChart.bufferedTransitionGlueBasepoint g hEnorm x hρ c near hclass J hcont hconv ∈
      Set.range ((IntrinsicBallChart.finiteBufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι (ULift.up 0)) :=
  ⟨⟨0, Metric.mem_ball_self (by positivity)⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueBasepoint_mem_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueBasepoint_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueBasepoint_mem_range ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.bufferedTransitionGlueBasepoint_mem_range

include hρ in
theorem IntrinsicBallChart.pointed_intrinsic_chart_zero
    (p : ∀ k, M k) (hbase : ∀ k, x 0 k = p k) (k : ℕ) :
    (c 0 k).hom 0 = p k := by
  calc
    (c 0 k).hom 0 = x 0 k := ((c 0 k).toNormalBallChart (g k) (hEnorm k) (x 0 k) hρ).map_zero
    _ = p k := hbase k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.pointed_intrinsic_chart_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.pointed_intrinsic_chart_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.pointed_intrinsic_chart_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.IntrinsicBallChart.pointed_intrinsic_chart_zero

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end
