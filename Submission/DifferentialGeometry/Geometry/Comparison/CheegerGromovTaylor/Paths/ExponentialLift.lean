import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.GaussLemma
import Submission.DifferentialGeometry.Geometry.Exponential.PathLifting
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Agreement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CheegerGromovTaylor

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

structure IntrinsicFrameLift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (γ : Real → M) (a b : Real) where
  toFun : Real → E
  contDiff : ContDiffOn Real 1 toFun (Set.Icc a b)
  start : toFun a = 0
  lifts :
    Set.EqOn
      ((intrinsicFramedExp (I := I) g hEnorm p) ∘ toFun)
      γ (Set.Icc a b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift

namespace IntrinsicFrameLift

variable {g : SmoothRiemannianMetric I M}
  {hEnorm : ∀ (x : M) (v : TangentSpace I x),
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v))}
  {p : M} {γ : Real → M} {a b R : Real}

theorem norm_le_length
    (L : IntrinsicFrameLift (I := I) g hEnorm p γ a b)
    (hfin : Manifold.pathELength I γ a b ≠ ⊤)
    {t : Real} (ht : t ∈ Set.Icc a b) :
    ‖L.toFun t‖ ≤ (Manifold.pathELength I γ a b).toReal := by
  have hsub : Set.Icc a t ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc le_rfl ht.2
  have hrad :
      ENNReal.ofReal ‖L.toFun t‖ ≤
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ L.toFun) a t :=
    intrinsicLift_norm_le (J := I) g hEnorm p ht.1 L.start
      (L.contDiff.mono hsub)
  have hlift :
      Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ L.toFun) a t =
        Manifold.pathELength I γ a t := by
    apply Manifold.pathELength_congr
    intro s hs
    exact L.lifts ⟨hs.1, hs.2.trans ht.2⟩
  have hmono :
      Manifold.pathELength I γ a t ≤
        Manifold.pathELength I γ a b :=
    Manifold.pathELength_mono le_rfl ht.2
  have hchain :
      ENNReal.ofReal ‖L.toFun t‖ ≤
        Manifold.pathELength I γ a b := by
    calc
      ENNReal.ofReal ‖L.toFun t‖
          ≤ Manifold.pathELength I
              ((intrinsicFramedExp (I := I) g hEnorm p) ∘ L.toFun) a t := hrad
      _ = Manifold.pathELength I γ a t := hlift
      _ ≤ Manifold.pathELength I γ a b := hmono
  have hreal :=
    (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mpr hchain
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using hreal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.norm_le_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.norm_le_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.norm_le_length ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.norm_le_length

theorem norm_lt
    (L : IntrinsicFrameLift (I := I) g hEnorm p γ a b)
    (hR : 0 < R)
    (hlen :
      Manifold.pathELength I γ a b < ENNReal.ofReal R)
    {t : Real} (ht : t ∈ Set.Icc a b) :
    ‖L.toFun t‖ < R := by
  have hsub : Set.Icc a t ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc le_rfl ht.2
  have hrad :
      ENNReal.ofReal ‖L.toFun t‖ ≤
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ L.toFun) a t :=
    intrinsicLift_norm_le (J := I) g hEnorm p ht.1 L.start
      (L.contDiff.mono hsub)
  have hlift :
      Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ L.toFun) a t =
        Manifold.pathELength I γ a t := by
    apply Manifold.pathELength_congr
    intro s hs
    exact L.lifts ⟨hs.1, hs.2.trans ht.2⟩
  have hmono :
      Manifold.pathELength I γ a t ≤
        Manifold.pathELength I γ a b :=
    Manifold.pathELength_mono le_rfl ht.2
  have hlt :
      ENNReal.ofReal ‖L.toFun t‖ < ENNReal.ofReal R := by
    calc
      ENNReal.ofReal ‖L.toFun t‖
          ≤ Manifold.pathELength I
              ((intrinsicFramedExp (I := I) g hEnorm p) ∘ L.toFun) a t := hrad
      _ = Manifold.pathELength I γ a t := hlift
      _ ≤ Manifold.pathELength I γ a b := hmono
      _ < ENNReal.ofReal R := hlen
  exact (ENNReal.ofReal_lt_ofReal_iff hR).mp hlt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.norm_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.norm_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.norm_lt ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.norm_lt

theorem maps_ball
    (L : IntrinsicFrameLift (I := I) g hEnorm p γ a b)
    (hR : 0 < R)
    (hlen :
      Manifold.pathELength I γ a b < ENNReal.ofReal R) :
    Set.MapsTo L.toFun (Set.Icc a b) (Metric.ball (0 : E) R) := by
  intro t ht
  simpa only [Metric.mem_ball, dist_zero_right] using L.norm_lt hR hlen ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.maps_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.maps_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.maps_ball ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.maps_ball

theorem eqOn
    (L L' : IntrinsicFrameLift (I := I) g hEnorm p γ a b)
    (hab : a ≤ b) (hR : 0 < R)
    (hlen :
      Manifold.pathELength I γ a b < ENNReal.ofReal R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    Set.EqOn L.toFun L'.toFun (Set.Icc a b) := by
  let hL :
      isLiftOn
        (intrinsicFramedExp (I := I) g hEnorm p)
        γ (Metric.ball (0 : E) R) 0 a b L.toFun :=
    ⟨L.contDiff.continuousOn, L.start,
      fun t ht ↦ ⟨L.maps_ball hR hlen ht, L.lifts ht⟩⟩
  let hL' :
      isLiftOn
        (intrinsicFramedExp (I := I) g hEnorm p)
        γ (Metric.ball (0 : E) R) 0 a b L'.toFun :=
    ⟨L'.contDiff.continuousOn, L'.start,
      fun t ht ↦ ⟨L'.maps_ball hR hlen ht, L'.lifts ht⟩⟩
  exact hL.eqOn hab Metric.isOpen_ball hloc hL'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.eqOn ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.IntrinsicFrameLift.eqOn

end IntrinsicFrameLift

theorem exists_intr_lift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {γ : Real → M} {a b R : Real}
    (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc a b))
    (hγa : γ a = p)
    (hlen :
      Manifold.pathELength I γ a b < ENNReal.ofReal R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    Nonempty (IntrinsicFrameLift (I := I) g hEnorm p γ a b) := by
  have hagree : framedExpMap (I := I) g p = intrinsicFramedExp (I := I) g hEnorm p := by
    funext z
    rw [framedExpMap_apply, intrinsicFrame_apply, expMap_eq_expMapIntrinsic g hEnorm p]
  have hdom : ∀ z ∈ Metric.ball (0 : E) R,
      normalFrame (I := I) g p z ∈ expDomain (I := I) g p := by
    intro z _
    rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
    exact _root_.Set.mem_univ _
  have hloc' : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R) := by
    rw [hagree]
    exact hloc
  obtain ⟨η, hη⟩ := exists_isLiftOn_framedExpMap g hEnorm p hab hγ hγa hlen hdom hloc'
  rw [hagree] at hη
  exact ⟨{
    toFun := η
    contDiff := hη.contDiffOn hloc hγ
    start := hη.2.1
    lifts := fun t ht ↦ (hη.2.2 t ht).2 }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.exists_intr_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.exists_intr_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.exists_intr_lift ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.exists_intr_lift

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry
