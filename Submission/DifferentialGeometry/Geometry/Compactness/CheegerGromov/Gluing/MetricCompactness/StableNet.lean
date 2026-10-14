import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.MetricCompactness.Assumptions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

namespace MetricCompactnessAssumptions

theorem cap_four
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessAssumptions (I := I) X) :
    (4 : Real) * inp.decay.lambda inp.D 0 <= inp.volume.r0 := by
  have hlam : 0 <= inp.decay.lambda inp.D 0 :=
    (inp.decay.lambda_pos inp.divisor_pos 0).le
  have hle :
      (4 : Real) <=
        max 4 (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) :=
    le_max_left _ _
  exact (mul_le_mul_of_nonneg_right hle hlam).trans inp.covering_scale_le_volume_radius

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.cap_four then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.cap_four"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.cap_four ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.cap_four

theorem cap_four_of_nonneg
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessAssumptions (I := I) X) {R : Real} (hR : 0 <= R) :
    (4 : Real) * inp.decay.lambda inp.D R <= inp.volume.r0 := by
  have hlam : inp.decay.lambda inp.D R <= inp.decay.lambda inp.D 0 :=
    inp.decay.lambda_antitone inp.divisor_pos hR
  have hmul :
      (4 : Real) * inp.decay.lambda inp.D R <=
        (4 : Real) * inp.decay.lambda inp.D 0 :=
    mul_le_mul_of_nonneg_left hlam (by norm_num)
  exact hmul.trans inp.cap_four

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.cap_four_of_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.cap_four_of_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.cap_four_of_nonneg ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.cap_four_of_nonneg

theorem cap_inter
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessAssumptions (I := I) X) :
    (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) *
        inp.decay.lambda inp.D 0 <= inp.volume.r0 := by
  have hlam : 0 <= inp.decay.lambda inp.D 0 :=
    (inp.decay.lambda_pos inp.divisor_pos 0).le
  have hle :
      50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) <=
        max 4 (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) :=
    le_max_right _ _
  exact (mul_le_mul_of_nonneg_right hle hlam).trans inp.covering_scale_le_volume_radius

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.cap_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.cap_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.cap_inter ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.cap_inter

theorem net_mult
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessAssumptions (I := I) X) (k : Nat) {R : Real}
    (hR : 0 <= R) {S : Set ((X.obj k).M)}
    (hS : S.PairwiseDisjoint (inp.decay.lambdaBall inp.D k))
    (hSR : ∀ x ∈ S, inp.decay.dist k x (X.obj k).basepoint <= R)
    (z : (X.obj k).M) (J : Finset ((X.obj k).M)) (hJS : ↑J ⊆ S)
    (hJz : ∀ x ∈ J, inp.decay.dist k x z <= 4 * inp.decay.lambda inp.D R) :
    J.card <= inp.volume.multiplicity 4 := by
  exact InjectivityRadiusDecay.net_multiplicity
    inp.decay inp.D k inp.divisor_pos inp.realizes inp.volume inp.dist_eq R
    (inp.cap_four_of_nonneg hR) hS hSR z J hJS hJz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.net_mult then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.net_mult"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.net_mult ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.net_mult

theorem inter_count
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (α : Nat) :
    ∀ᶠ k in _root_.Filter.atTop,
      ∀ xα : (X.obj (L.φ k)).M,
        seqCenter inp.decay inp.D P (L.φ k) α = _root_.Option.some xα →
      ∀ J : Finset Nat,
        (∀ β ∈ J, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) →
        J.card <=
          inp.volume.multiplicity
            (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) := by
  exact NetLimitData.inter_count inp.decay inp.divisor_pos P L inp.realizes inp.pack
    inp.volume inp.dist_eq inp.cap_inter α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.inter_count then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.inter_count"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.inter_count ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.inter_count

theorem nonempty_net_limit_data
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    Nonempty (NetLimitData inp.decay inp.D P) :=
  nonempty_netLimitData inp.decay inp.divisor_pos P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.nonempty_net_limit_data then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.nonempty_net_limit_data"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.nonempty_net_limit_data ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.nonempty_net_limit_data

theorem exists_stable_net
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    ∃ L : NetLimitData inp.decay inp.D P,
      ∀ α β : Nat,
        (∀ᶠ k in _root_.Filter.atTop, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in _root_.Filter.atTop, ¬ BInter inp.decay inp.D P L.lamInf α β (L.φ k)) :=
  exists_netLimitData_with_stable_intersections inp.decay inp.divisor_pos P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net

theorem exists_stable_net_with_intersection_bound
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessAssumptions (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    ∃ L : NetLimitData inp.decay inp.D P,
      (∀ α β : Nat,
        (∀ᶠ k in _root_.Filter.atTop, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in _root_.Filter.atTop, ¬ BInter inp.decay inp.D P L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in _root_.Filter.atTop,
          ∀ xα : (X.obj (L.φ k)).M,
            seqCenter inp.decay inp.D P (L.φ k) α = _root_.Option.some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) →
            J.card <=
              inp.volume.multiplicity
                (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)))) := by
  obtain ⟨L, hstable⟩ := inp.exists_stable_net P
  exact ⟨L, hstable, fun α => inp.inter_count P L α⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net_with_intersection_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net_with_intersection_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net_with_intersection_bound ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net_with_intersection_bound

theorem exists_stable_net_with_intersection_bound_of_complete_connected
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessAssumptions (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ L : NetLimitData inp.decay inp.D (properMetricsOfCompleteConnected (I := I) hcomplete hconn),
      (∀ α β : Nat,
        (∀ᶠ k in _root_.Filter.atTop,
          BInter inp.decay inp.D (properMetricsOfCompleteConnected (I := I) hcomplete hconn)
            L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in _root_.Filter.atTop,
          ¬ BInter inp.decay inp.D (properMetricsOfCompleteConnected (I := I) hcomplete hconn)
            L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in _root_.Filter.atTop,
          ∀ xα : (X.obj (L.φ k)).M,
            seqCenter inp.decay inp.D (properMetricsOfCompleteConnected (I := I) hcomplete hconn)
              (L.φ k) α = _root_.Option.some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J,
              BInter inp.decay inp.D (properMetricsOfCompleteConnected (I := I) hcomplete hconn)
                L.lamInf α β (L.φ k)) →
            J.card <=
              inp.volume.multiplicity
                (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)))) :=
  inp.exists_stable_net_with_intersection_bound (properMetricsOfCompleteConnected (I := I) hcomplete hconn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net_with_intersection_bound_of_complete_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net_with_intersection_bound_of_complete_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net_with_intersection_bound_of_complete_connected ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net_with_intersection_bound_of_complete_connected

theorem exists_stable_net_with_intersection_bound_subsequence
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessAssumptions (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (f : Nat -> Nat) :
    ∃ L : NetLimitData (inp.subseq f).decay (inp.subseq f).D
        (properMetricsOfCompleteConnected (I := I) (hcomplete.subseq f)
          (X.connected_subseq hconn f)),
      (∀ α β : Nat,
        (∀ᶠ k in _root_.Filter.atTop,
          BInter (inp.subseq f).decay (inp.subseq f).D
            (properMetricsOfCompleteConnected (I := I) (hcomplete.subseq f)
              (X.connected_subseq hconn f))
            L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in _root_.Filter.atTop,
          ¬ BInter (inp.subseq f).decay (inp.subseq f).D
            (properMetricsOfCompleteConnected (I := I) (hcomplete.subseq f)
              (X.connected_subseq hconn f))
            L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in _root_.Filter.atTop,
          ∀ xα : ((X.subseq f).obj (L.φ k)).M,
            seqCenter (inp.subseq f).decay (inp.subseq f).D
              (properMetricsOfCompleteConnected (I := I) (hcomplete.subseq f)
                (X.connected_subseq hconn f))
              (L.φ k) α = _root_.Option.some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J,
              BInter (inp.subseq f).decay (inp.subseq f).D
                (properMetricsOfCompleteConnected (I := I) (hcomplete.subseq f)
                  (X.connected_subseq hconn f))
                L.lamInf α β (L.φ k)) →
            J.card <=
              (inp.subseq f).volume.multiplicity
                (50 * Real.exp
                  ((inp.subseq f).decay.C *
                    (20 * (inp.subseq f).decay.lambda (inp.subseq f).D 0)))) := by
  exact (inp.subseq f).exists_stable_net_with_intersection_bound_of_complete_connected (hcomplete.subseq f)
    (X.connected_subseq hconn f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net_with_intersection_bound_subsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net_with_intersection_bound_subsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net_with_intersection_bound_subsequence ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.exists_stable_net_with_intersection_bound_subsequence

end MetricCompactnessAssumptions


end CheegerGromovCompactness
end DifferentialGeometry
