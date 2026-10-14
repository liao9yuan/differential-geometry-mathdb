import Submission.DifferentialGeometry.Geometry.Metric.Quotient
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderCoverScalarNormalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderAxialDistance
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import Submission.DifferentialGeometry.Geometry.Metric.DistancePullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact
private local instance sphereTwoDimension :
    Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoDimension target :: scope.openDecls } }
private local instance sphereTwoC1 : IsManifold I2 1 (Sphere 2) :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoC1 target :: scope.openDecls } }
private local instance cylinderC1 : IsManifold IC 1 Cylinder :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderC1 target :: scope.openDecls } }
private local instance sphereTwoConnected : ConnectedSpace (Sphere 2) := by
  apply Subtype.connectedSpace
  apply isConnected_sphere
  · exact Module.one_lt_rank_of_one_lt_finrank (by simp)
  · norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoConnected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoConnected target :: scope.openDecls } }

variable {P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval}
private local instance sourceC1 : IsManifold I3 1 P.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sourceC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sourceC1 target :: scope.openDecls } }

theorem ShrinkingCylinderCover.projection_eq_diagonal (C : ShrinkingCylinderCover P)
    (hdiag : C.DiagonalModel) (z : Cylinder) :
    C.projection (cylinderDiagonalDiffeomorph z) = C.projection z := by
  have hd := (hdiag.2 cylinderDiagonalDiffeomorph.toHomeomorph).mpr (Or.inr rfl)
  exact congrFun hd z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_eq_diagonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_eq_diagonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_eq_diagonal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_eq_diagonal

theorem ShrinkingCylinderCover.projection_edist_le_of_scalar_at_base_one
    (C : ShrinkingCylinderCover P) (hbase : PointedFlowScalarAtBase P 1) (z w : Cylinder) :
    riemannianEDistOf (P.S.base.metric 0) (C.projection z) (C.projection w) ≤
      riemannianEDistOf (cylinderReference.metric 0) z w := by
  have hmetric : ∀ q : Cylinder, ∀ v : TangentSpace IC q,
      (P.S.base.metric 0).inner (C.projection q)
        (mfderiv IC I3 C.projection q v) (mfderiv IC I3 C.projection q v) ≤
      (1 : ℝ) * (cylinderReference.metric 0).inner q v v := by
    rintro ⟨y, s⟩ ⟨v, a⟩
    have hh := C.projection_metric 0 le_rfl y s v v a a
    rw [C.extinctionTime_eq_one_of_scalar_at_base_one hbase] at hh
    rw [one_mul]
    have hcanon : (cylinderReference.metric 0).inner (y, s) (v, a) (v, a) =
        2 * (roundMetric (E := ThreeSpace) (n := 2)).inner y v v + a * a := by
      change (cylinderMetric (scaleMetric (_root_.Max.max (2 * (1 - 0)) 1) _
        (roundMetric (E := ThreeSpace) (n := 2)))).inner (y, s) (v, a) (v, a) = _
      erw [cylinderMetric_inner, scaleMetric_inner]
      norm_num
    rw [hcanon]
    simp only [sub_zero, mul_one] at hh
    with_unfolding_all exact hh.le
  have hh := edistOf_le_of_quad_of_localDiffeomorph (cylinderReference.metric 0)
    (P.S.base.metric 0) C.projection C.projection_local zero_lt_one hmetric z w
  simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_edist_le_of_scalar_at_base_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_edist_le_of_scalar_at_base_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_edist_le_of_scalar_at_base_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_edist_le_of_scalar_at_base_one

theorem exists_diagonal_projection_distance_upper_constant :
    ∃ D : ℝ, 0 < D ∧ ∀ (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
      (C : ShrinkingCylinderCover P), C.DiagonalModel → PointedFlowScalarAtBase P 1 →
      ∀ z w : Cylinder,
        (riemannianEDistOf (P.S.base.metric 0) (C.projection z) (C.projection w)).toReal ≤
          abs (|z.2| - |w.2|) + D := by
  obtain ⟨D, hD, hbound⟩ := exists_cylinderReference_axial_distance_error
  refine ⟨D, hD, ?_⟩
  intro P C hdiag hbase z w
  have hup (a b : Cylinder) :
      (riemannianEDistOf (P.S.base.metric 0) (C.projection a) (C.projection b)).toReal ≤
        |a.2 - b.2| + D := by
    have hfin : riemannianEDistOf (cylinderReference.metric 0) a b ≠ ⊤ :=
      riemannianEDistOf_ne_top (cylinderReference.metric 0) a b
    have hle := ENNReal.toReal_mono hfin
      (C.projection_edist_le_of_scalar_at_base_one hbase a b)
    have herr := (abs_le.mp (hbound cylinderReference a b)).2
    linarith
  rcases le_total 0 z.2 with hz | hz <;> rcases le_total 0 w.2 with hw | hw
  · simpa only [abs_of_nonneg hz, abs_of_nonneg hw] using hup z w
  · have hh := hup z (cylinderDiagonalDiffeomorph w)
    rw [C.projection_eq_diagonal hdiag w] at hh
    change _ ≤ |z.2 - -w.2| + D at hh
    simpa only [abs_of_nonneg hz, abs_of_nonpos hw] using hh
  · have hh := hup (cylinderDiagonalDiffeomorph z) w
    rw [C.projection_eq_diagonal hdiag z] at hh
    change _ ≤ |-z.2 - w.2| + D at hh
    simpa only [abs_of_nonpos hz, abs_of_nonneg hw] using hh
  · simpa only [abs_of_nonpos hz, abs_of_nonpos hw, neg_sub_neg, abs_sub_comm] using hup z w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_diagonal_projection_distance_upper_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_diagonal_projection_distance_upper_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_diagonal_projection_distance_upper_constant ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_diagonal_projection_distance_upper_constant

theorem ShrinkingCylinderCover.abs_height_eq_of_projection_eq_diagonal
    (C : ShrinkingCylinderCover P) (hdiag : C.DiagonalModel) {z w : Cylinder}
    (heq : C.projection z = C.projection w) : |z.2| = |w.2| := by
  obtain ⟨e, he⟩ := hdiag.1
  have hquot : CylinderDiagonalQuotient.proj z = CylinderDiagonalQuotient.proj w := by
    apply e.injective
    exact (he z).trans (heq.trans (he w).symm)
  rcases (CylinderDiagonalQuotient.proj_eq_iff z w).mp hquot with hw | hw
  · rw [hw]
  · rw [hw]
    exact (abs_neg z.2).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.abs_height_eq_of_projection_eq_diagonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.abs_height_eq_of_projection_eq_diagonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.abs_height_eq_of_projection_eq_diagonal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.abs_height_eq_of_projection_eq_diagonal

theorem ShrinkingCylinderCover.abs_height_sub_le_projection_distance
    (C : ShrinkingCylinderCover P) (hdiag : C.DiagonalModel)
    (hbase : PointedFlowScalarAtBase P 1) (z w : Cylinder) :
    abs (|z.2| - |w.2|) ≤
      (riemannianEDistOf (P.S.base.metric 0) (C.projection z) (C.projection w)).toReal := by
  have hpull : localPullMetric (P.S.base.metric 0) C.projection C.projection_local =
      cylinderReference.metric 0 := by
    apply SmoothRiemannianMetric.ext_inner
    rintro ⟨y, s⟩ ⟨v, a⟩ ⟨u, b⟩
    apply (localPullMetric_inner (P.S.base.metric 0) C.projection C.projection_local
      (y, s) (v, a) (u, b)).trans
    have hh := C.projection_metric 0 le_rfl y s v u a b
    rw [C.extinctionTime_eq_one_of_scalar_at_base_one hbase] at hh
    have hcanon : (cylinderReference.metric 0).inner (y, s) (v, a) (u, b) =
        2 * (roundMetric (E := ThreeSpace) (n := 2)).inner y v u + a * b := by
      change (cylinderMetric (scaleMetric (_root_.Max.max (2 * (1 - 0)) 1) _
        (roundMetric (E := ThreeSpace) (n := 2)))).inner (y, s) (v, a) (u, b) = _
      erw [cylinderMetric_inner, scaleMetric_inner]
      norm_num
    rw [hcanon]
    simp only [sub_zero, mul_one] at hh
    with_unfolding_all exact hh
  have hlower : ENNReal.ofReal (abs (|z.2| - |w.2|)) ≤
      riemannianEDistOf (P.S.base.metric 0) (C.projection z) (C.projection w) := by
    apply le_edistOf_of_coveringMap_localPullMetric (cylinderReference.metric 0)
      (P.S.base.metric 0) C.projection_local C.projection_covering hpull z (C.projection w)
    intro q hq
    have hheight : |q.2| = |w.2| := C.abs_height_eq_of_projection_eq_diagonal hdiag hq
    calc
      ENNReal.ofReal (abs (|z.2| - |w.2|)) =
          ENNReal.ofReal (abs (|z.2| - |q.2|)) := by rw [hheight]
      _ ≤ ENNReal.ofReal |z.2 - q.2| := ENNReal.ofReal_le_ofReal (abs_abs_sub_abs_le _ _)
      _ ≤ riemannianEDistOf (cylinderReference.metric 0) z q :=
        cylinderReference.height_edist_le z q
  have hfin : riemannianEDistOf (P.S.base.metric 0) (C.projection z) (C.projection w) ≠ ⊤ :=
    ne_top_of_le_ne_top (riemannianEDistOf_ne_top (cylinderReference.metric 0) z w)
      (C.projection_edist_le_of_scalar_at_base_one hbase z w)
  have hh := ENNReal.toReal_mono hfin hlower
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.abs_height_sub_le_projection_distance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.abs_height_sub_le_projection_distance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.abs_height_sub_le_projection_distance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.abs_height_sub_le_projection_distance

theorem ShrinkingCylinderCover.exists_nonnegative_height_lift
    (C : ShrinkingCylinderCover P) (hdiag : C.DiagonalModel) (x : P.M) :
    ∃ z : Cylinder, 0 ≤ z.2 ∧ C.projection z = x := by
  obtain ⟨z, hz⟩ := C.surjective x
  change C.projection z = x at hz
  by_cases hheight : 0 ≤ z.2
  · exact ⟨z, hheight, hz⟩
  · refine ⟨cylinderDiagonalDiffeomorph z, ?_, (C.projection_eq_diagonal hdiag z).trans hz⟩
    change 0 ≤ -z.2
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.exists_nonnegative_height_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.exists_nonnegative_height_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.exists_nonnegative_height_lift ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.exists_nonnegative_height_lift

theorem exists_diagonal_radial_error_constant :
    ∃ D : ℝ, 0 < D ∧ ∀ (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
      (C : ShrinkingCylinderCover P), C.DiagonalModel → PointedFlowScalarAtBase P 1 →
      ∀ z w : Cylinder, 0 ≤ z.2 → 0 ≤ w.2 →
        (riemannianEDistOf (P.S.base.metric 0) (C.projection z) (C.projection w)).toReal ≤
          |z.2 - w.2| + D := by
  obtain ⟨D, hD, hup⟩ := exists_diagonal_projection_distance_upper_constant
  exact ⟨D, hD, fun P C hdiag hbase z w hz hw => by
    simpa only [abs_of_nonneg hz, abs_of_nonneg hw] using hup P C hdiag hbase z w⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_diagonal_radial_error_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_diagonal_radial_error_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_diagonal_radial_error_constant ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_diagonal_radial_error_constant

private theorem equal_radius_cross_distance_le_of_radial_distance_bounds
    {R a b s c D : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (has : |a - R| ≤ s) (hsa : s ≤ |a - R| + D)
    (hbs : |b - R| ≤ s) (hsb : s ≤ |b - R| + D)
    (hc : c ≤ |a - b| + D) : c ≤ 2 * D + 2 * R := by
  have hau : a ≤ s + R := by linarith [(abs_le.mp has).2]
  have hbu : b ≤ s + R := by linarith [(abs_le.mp hbs).2]
  have hal : s - D - R ≤ a := by
    have habs : |a - R| ≤ a + R := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hbl : s - D - R ≤ b := by
    have habs : |b - R| ≤ b + R := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hcross : |a - b| ≤ D + 2 * R := by
    rw [abs_le]
    constructor <;> linarith
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.equal_radius_cross_distance_le_of_radial_distance_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.equal_radius_cross_distance_le_of_radial_distance_bounds target :: scope.openDecls } }

theorem ShrinkingCylinderCover.exists_cross_distance_bound_of_diagonalModel
    (C : ShrinkingCylinderCover P) (hdiag : C.DiagonalModel)
    (hbase : PointedFlowScalarAtBase P 1) (p : P.M) :
    ∃ B : ℝ, 0 < B ∧ ∀ x y : P.M,
      metricDistance (P.S.base.metric 0) p x = metricDistance (P.S.base.metric 0) p y →
      metricDistance (P.S.base.metric 0) x y ≤ B := by
  obtain ⟨D, hD, hup⟩ := exists_diagonal_radial_error_constant
  obtain ⟨z, hz, hzp⟩ := C.exists_nonnegative_height_lift hdiag p
  refine ⟨2 * D + 2 * z.2, by positivity, ?_⟩
  intro x y hsame
  obtain ⟨a, ha, hax⟩ := C.exists_nonnegative_height_lift hdiag x
  obtain ⟨b, hb, hby⟩ := C.exists_nonnegative_height_lift hdiag y
  have hupA := hup P C hdiag hbase a z ha hz
  have hupB := hup P C hdiag hbase b z hb hz
  have hupAB := hup P C hdiag hbase a b ha hb
  have hloA := C.abs_height_sub_le_projection_distance hdiag hbase a z
  have hloB := C.abs_height_sub_le_projection_distance hdiag hbase b z
  simp only [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg hz] at hloA hloB
  rw [hax, hzp] at hupA hloA
  rw [hby, hzp] at hupB hloB
  rw [hax, hby] at hupAB
  have hcomm (u v : P.M) : metricDistance (P.S.base.metric 0) u v =
      metricDistance (P.S.base.metric 0) v u := by
    unfold metricDistance
    rw [riemannianEDistOf_comm]
  change metricDistance (P.S.base.metric 0) x p ≤ _ at hupA
  change metricDistance (P.S.base.metric 0) y p ≤ _ at hupB
  change _ ≤ metricDistance (P.S.base.metric 0) x p at hloA
  change _ ≤ metricDistance (P.S.base.metric 0) y p at hloB
  rw [hcomm x p] at hupA hloA
  rw [hcomm y p, ← hsame] at hupB hloB
  exact equal_radius_cross_distance_le_of_radial_distance_bounds hz ha hb
    hloA hupA hloB hupB hupAB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.exists_cross_distance_bound_of_diagonalModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.exists_cross_distance_bound_of_diagonalModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.exists_cross_distance_bound_of_diagonalModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.exists_cross_distance_bound_of_diagonalModel

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
