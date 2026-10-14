import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCap
import Submission.DifferentialGeometry.Topology.Manifold.Interval.TangentLift
import Submission.DifferentialGeometry.Topology.Manifold.ProductOrientationCongruence
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Submission.DifferentialGeometry.Bundle.Orientation.FrameTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Module _root_.Bundle _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphericalTubeSystem

universe u

local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "Interval" => _root_.Set.Icc (-2 : ℝ) 2
local notation "Tube" => S2 × Interval
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)

local instance _root_.Submission.DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat
local instance _root_.Submission.DifferentialGeometry.Topology.SphericalTubeSystem.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd

def intervalBasis (t : Interval) : _root_.Module.Basis (Fin 1) ℝ (TangentSpace (𝓡∂ 1) t) :=
  (Basis.singleton (Fin 1) ℝ).map
    (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm.toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.intervalBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.intervalBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.intervalBasis ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.intervalBasis

def normalFirstModelBasis (z : S2) (b : _root_.Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z))
    (t : Interval) : _root_.Module.Basis (Fin 3) ℝ (TangentSpace CI (z, t)) :=
  (((intervalBasis t).prod b).reindex finSumFinEquiv).map
    (LinearEquiv.prodComm ℝ (TangentSpace (𝓡∂ 1) t) (TangentSpace (𝓡 2) z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.normalFirstModelBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.normalFirstModelBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.normalFirstModelBasis ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.normalFirstModelBasis

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

def tubeDifferential (a : T.Index) (q : Tube) :
    TangentSpace CI q ≃ₗ[ℝ] TangentSpace (𝓡 3) (T.tube a q) :=
  LinearEquiv.ofBijective (mfderiv CI (𝓡 3) (T.tube a) q).toLinearMap
    (DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt
      CI (𝓡 3) (T.tube a) q ((T.smooth a).isImmersion.isImmersionAt q)
      (by change Module.finrank ℝ (E2 × E1) = Module.finrank ℝ E3; simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.tubeDifferential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.tubeDifferential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.tubeDifferential ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.tubeDifferential

def tubeFrame (a : T.Index) (z : S2)
    (b : _root_.Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (t : Interval) :
    Basis (Fin 3) ℝ (TangentSpace (𝓡 3) (T.tube a (z, t))) :=
  (normalFirstModelBasis z b t).map (tubeDifferential T a (z, t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.tubeFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.tubeFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.tubeFrame ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.tubeFrame

theorem tubeFrame_apply (a : T.Index) (z : S2)
    (b : _root_.Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (t : Interval) (i : Fin 3) :
    tubeFrame T a z b t i =
      mfderiv CI (𝓡 3) (T.tube a) (z, t) (normalFirstModelBasis z b t i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.tubeFrame_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.tubeFrame_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.tubeFrame_apply ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.tubeFrame_apply

end DifferentialGeometry.Topology.SphericalTubeSystem

namespace DifferentialGeometry.Topology.SphericalTubeSystem
universe u
local notation "Interval" => Set.Icc (-2 : ℝ) 2
local instance _root_.Submission.DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat_1 : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat_1 ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat_1
variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

theorem continuous_intervalVector (r : ℝ) :
    Continuous (fun t : Interval =>
      (⟨t, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm r⟩ :
        TangentBundle (𝓡∂ 1) Interval)) := by
  exact (DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc_symm.continuous.comp
    (continuous_id.prodMk continuous_const))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.continuous_intervalVector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.continuous_intervalVector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.continuous_intervalVector ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.continuous_intervalVector

end DifferentialGeometry.Topology.SphericalTubeSystem


namespace DifferentialGeometry.Topology.SphericalTubeSystem
universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "Interval" => Set.Icc (-2 : ℝ) 2
local notation "Tube" => S2 × Interval
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)
local instance _root_.Submission.DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat_2 : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat_2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat_2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat_2 ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat_2
variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

theorem continuous_productVector (z : S2) (v : TangentSpace (𝓡 2) z) (r : ℝ) :
    Continuous (fun t : Interval =>
      (⟨(z, t), (v, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm r)⟩ :
        TangentBundle CI Tube)) := by
  let hpair : Continuous (fun t : Interval =>
      ((⟨z, v⟩ : TangentBundle (𝓡 2) S2),
        (⟨t, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm r⟩ :
          TangentBundle (𝓡∂ 1) Interval))) :=
    continuous_const.prodMk (continuous_intervalVector r)
  have he := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓡 2) (I' := 𝓡∂ 1) (M := S2) (M' := Interval) (n := (0 : WithTop ℕ∞))).continuous
  have hc := he.comp hpair
  exact hc.congr (fun t => rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.continuous_productVector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.continuous_productVector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.continuous_productVector ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.continuous_productVector

private theorem normalFirstModelBasis_zero (z : S2)
    (b : _root_.Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (t : Interval) :
    normalFirstModelBasis z b t 0 =
      (0, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm 1) := by
  erw [normalFirstModelBasis, Basis.map_apply, Basis.reindex_apply]
  change LinearEquiv.prodComm ℝ (TangentSpace (𝓡∂ 1) t) (TangentSpace (𝓡 2) z)
    (((intervalBasis t).prod b) (Sum.inl 0)) = _
  simp [Basis.prod_apply, intervalBasis]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.normalFirstModelBasis_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.normalFirstModelBasis_zero target :: scope.openDecls } }

private theorem normalFirstModelBasis_succ (z : S2)
    (b : _root_.Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (t : Interval) (i : Fin 2) :
    normalFirstModelBasis z b t i.succ = (b i, 0) := by
  erw [normalFirstModelBasis, Basis.map_apply, Basis.reindex_apply]
  have hidx : (finSumFinEquiv (m := 1) (n := 2)).symm i.succ = Sum.inr i := by
    fin_cases i <;> rfl
  rw [hidx]
  simp [Basis.prod_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.normalFirstModelBasis_succ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.normalFirstModelBasis_succ target :: scope.openDecls } }

private theorem continuous_normalFirstModelBasis (z : S2)
    (b : _root_.Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (i : Fin 3) :
    Continuous (fun t : Interval =>
      (⟨(z, t), normalFirstModelBasis z b t i⟩ : TangentBundle CI Tube)) := by
  cases i using Fin.cases with
  | zero =>
    apply (continuous_productVector z 0 1).congr
    intro t
    exact congrArg (fun v : TangentSpace CI (z, t) =>
      (⟨(z, t), v⟩ : TangentBundle CI Tube)) (normalFirstModelBasis_zero z b t).symm
  | succ i =>
    apply (continuous_productVector z (b i) 0).congr
    intro t
    apply congrArg (fun v : TangentSpace CI (z, t) =>
      (⟨(z, t), v⟩ : TangentBundle CI Tube))
    change (b i, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm 0) = _
    rw [map_zero]
    exact (normalFirstModelBasis_succ z b t i).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.continuous_normalFirstModelBasis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.continuous_normalFirstModelBasis target :: scope.openDecls } }

theorem continuous_tubeFrame (a : T.Index) (z : S2)
    (b : _root_.Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (i : Fin 3) :
    Continuous (fun t : Interval =>
      (⟨T.tube a (z, t), T.tubeFrame a z b t i⟩ : TangentBundle (𝓡 3) M.Carrier)) := by
  have h := ((T.smooth a).contMDiff.continuous_tangentMap (by simp)).comp
    (continuous_normalFirstModelBasis z b i)
  exact h.congr (fun _ => rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.continuous_tubeFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.continuous_tubeFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.continuous_tubeFrame ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.continuous_tubeFrame


theorem tubeFrame_orientation_eq_iff (a : T.Index) (z : S2)
    (b : _root_.Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (t t' : Interval) :
    (T.tubeFrame a z b t).orientation = M.orientation.orientation (T.tube a (z, t)) ↔
      (T.tubeFrame a z b t').orientation = M.orientation.orientation (T.tube a (z, t')) := by
  let : PreconnectedSpace Interval := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  exact DifferentialGeometry.VectorBundle.frame_orientation_eq_iff
    (tangentBundleCore (𝓡 3) M.Carrier) (by simp)
    (fun t : Interval => T.tube a (z, t))
    ((T.tube a).continuous.comp (continuous_const.prodMk continuous_id))
    M.orientation.orientation
    (DifferentialGeometry.Topology.Manifold.isCompatibleOrientation_of_manifoldOrientation M.orientation)
    (T.tubeFrame a z b) (T.continuous_tubeFrame a z b) t t'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.tubeFrame_orientation_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.tubeFrame_orientation_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.tubeFrame_orientation_eq_iff ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.tubeFrame_orientation_eq_iff


def boundaryFrame (a : T.Index) (z : S2)
    (b : _root_.Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (side : Bool) :
    Basis (Fin 3) ℝ (TangentSpace (𝓡 3) (T.boundarySphere (a, side) z)) :=
  if side then
    (T.tubeFrame a z b (boundaryLevel side)).unitsSMul (Function.update 1 (0 : Fin 3) (-1))
  else T.tubeFrame a z b (boundaryLevel side)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame

theorem boundaryFrame_normal (a : T.Index) (z : S2)
    (b : _root_.Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (side : Bool) :
    T.boundaryFrame a z b side 0 =
      mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel side)
        (0, (if side then -1 else 1 : ℝ) •
          (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (boundaryLevel side)).symm 1) := by
  cases side with
  | false =>
    change mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel _root_.Bool.false)
      (normalFirstModelBasis z b (boundaryLevel _root_.Bool.false) 0) = _
    rw [normalFirstModelBasis_zero]
    simp only [Bool.false_eq_true, if_false, one_smul]
    rfl
  | true =>
    erw [boundaryFrame, if_pos rfl, Basis.unitsSMul_apply, Function.update_self, Units.neg_smul,
      one_smul, tubeFrame_apply, normalFirstModelBasis_zero]
    simp only [if_true, neg_smul, one_smul]
    change -(mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel _root_.Bool.true)
      (0, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (boundaryLevel _root_.Bool.true)).symm 1)) = _
    erw [show ((0 : TangentSpace (𝓡 2) z),
        -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (boundaryLevel _root_.Bool.true)).symm 1) =
      -((0 : TangentSpace (𝓡 2) z),
        (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (boundaryLevel _root_.Bool.true)).symm 1) from by simp]
    exact (map_neg (mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel _root_.Bool.true))
      (0, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (boundaryLevel _root_.Bool.true)).symm 1)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_normal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_normal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_normal ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_normal

theorem boundaryFrame_orientation_opposite (a : T.Index) (z : S2)
    (b : _root_.Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) :
    (T.boundaryFrame a z b _root_.Bool.false).orientation = M.orientation.orientation (T.boundarySphere (a, _root_.Bool.false) z) ↔
      (T.boundaryFrame a z b _root_.Bool.true).orientation ≠ M.orientation.orientation (T.boundarySphere (a, _root_.Bool.true) z) := by
  have htransport := T.tubeFrame_orientation_eq_iff a z b (boundaryLevel _root_.Bool.false) (boundaryLevel _root_.Bool.true)
  have hneg : (T.boundaryFrame a z b _root_.Bool.true).orientation =
      -(T.tubeFrame a z b (boundaryLevel _root_.Bool.true)).orientation :=
    Basis.orientation_neg_single _ 0
  change (T.tubeFrame a z b (boundaryLevel _root_.Bool.false)).orientation =
    M.orientation.orientation (T.tube a (z, boundaryLevel _root_.Bool.false)) ↔ _
  rw [hneg]
  constructor
  · intro hfalse htrue
    have h := htransport.mp hfalse
    have htrue' : -(T.tubeFrame a z b (boundaryLevel _root_.Bool.true)).orientation =
        M.orientation.orientation (T.tube a (z, boundaryLevel _root_.Bool.true)) := htrue
    have hbad : -(M.orientation.orientation (T.tube a (z, boundaryLevel _root_.Bool.true))) =
        M.orientation.orientation (T.tube a (z, boundaryLevel _root_.Bool.true)) :=
      (congrArg Neg.neg h).symm.trans htrue'
    exact Module.Ray.ne_neg_self _ hbad.symm
  · intro htrue
    apply htransport.mpr
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (T.tube a (z, boundaryLevel _root_.Bool.true))) :=
      inferInstanceAs (FiniteDimensional ℝ E3)
    rcases Orientation.eq_or_eq_neg
      (T.tubeFrame a z b (boundaryLevel _root_.Bool.true)).orientation
      (M.orientation.orientation (T.tube a (z, boundaryLevel _root_.Bool.true)))
      (by change Fintype.card (Fin 3) = Module.finrank ℝ E3; simp) with h | h
    · exact h
    · apply False.elim
      apply htrue
      change -(T.tubeFrame a z b (boundaryLevel _root_.Bool.true)).orientation =
        M.orientation.orientation (T.tube a (z, boundaryLevel _root_.Bool.true))
      rw [h, neg_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_orientation_opposite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_orientation_opposite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_orientation_opposite ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_orientation_opposite



theorem boundaryFrame_zero (a : T.Index) (z : S2)
    (b : _root_.Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (side : Bool) :
    T.boundaryFrame a z b side 0 = T.outwardVector (a, side) z := by
  rw [T.boundaryFrame_normal]
  have ht : (boundaryLevel side).val < 2 := by cases side <;> norm_num [boundaryLevel]
  rw [DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_symm_apply_of_lt _ ht]
  cases side <;> simp only [outwardVector, Bool.false_eq_true, if_false, if_true, one_smul, neg_smul]
  · exact congrArg (mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel _root_.Bool.false))
      (Prod.ext rfl (one_smul ℝ (EuclideanSpace.single 0 (1 : ℝ))))
  · exact congrArg (mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel _root_.Bool.true))
      (Prod.ext rfl (neg_one_smul ℝ (EuclideanSpace.single 0 (1 : ℝ))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_zero ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_zero


theorem boundaryFrame_succ (a : T.Index) (z : S2)
    (b : _root_.Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (side : Bool) (i : Fin 2) :
    T.boundaryFrame a z b side i.succ =
      mfderiv (𝓡 2) (𝓡 3) (T.boundarySphere (a, side)) z (b i) := by
  have hchain : mfderiv (𝓡 2) (𝓡 3) (T.boundarySphere (a, side)) z (b i) =
      mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel side) (b i, 0) := by
    change mfderiv (𝓡 2) (𝓡 3)
      ((T.tube a) ∘ fun y : S2 => (y, boundaryLevel side)) z (b i) = _
    erw [mfderiv_comp_apply z ((T.smooth a).contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_id.prodMk contMDiff_const :
        ContMDiff (𝓡 2) CI ∞ (fun y : S2 => (y, boundaryLevel side))).mdifferentiableAt (by simp)),
      mfderiv_prod_left]
    rfl
  rw [hchain]
  cases side with
  | false =>
    change mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel _root_.Bool.false)
      (normalFirstModelBasis z b (boundaryLevel _root_.Bool.false) i.succ) = _
    rw [normalFirstModelBasis_succ]
    rfl
  | true =>
    erw [boundaryFrame, if_pos rfl, Basis.unitsSMul_apply,
      Function.update_of_ne (Fin.succ_ne_zero i), Pi.one_apply, one_smul,
      tubeFrame_apply, normalFirstModelBasis_succ]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_succ ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.boundaryFrame_succ

end DifferentialGeometry.Topology.SphericalTubeSystem
