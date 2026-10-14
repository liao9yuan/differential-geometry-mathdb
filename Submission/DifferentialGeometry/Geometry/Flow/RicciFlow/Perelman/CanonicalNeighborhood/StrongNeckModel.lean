import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeckPartialDiffeomorph
import Submission.DifferentialGeometry.Geometry.Metric.Construction.TensorOpenExtension
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Locality
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.OpenTensorJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.TensorError

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private instance strongNeckConversionSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.strongNeckConversionSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.strongNeckConversionSphereDimension target :: scope.openDecls } }

private theorem strongNeckBackgroundMetric_eq_reference (epsilon s : ℝ) (hs : s ≤ 0) :
    strongNeckBackgroundMetric epsilon s =
      (cylinderReferenceMetric s).restrictOpen (spatialNeckBuffer epsilon) := by
  rw [strongNeckBackgroundMetric_of_nonpos epsilon s hs]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  change (scalarOneShrinkingCylinderMetric s (hs.trans_lt (by norm_num))).inner x.val v w =
    (cylinderReferenceMetric s).inner x.val v w
  exact (scalarOneShrinkingCylinderMetric_inner s (hs.trans_lt (by norm_num))
    x.val.1 x.val.2 v.1 w.1 v.2 w.2).trans
      (cylinderReferenceMetric_inner s hs x.val v w).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.strongNeckBackgroundMetric_eq_reference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.strongNeckBackgroundMetric_eq_reference target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {yStar : SpatialNeckSphere} {p : M} {t epsilon : ℝ}

theorem KappaSolutions.StrongNeckWitness.exists_strongNeck
    (W : StrongNeckWitness S yStar p t epsilon) (hsmall : epsilon < 1 / 11) :
    ∃ N : StrongNeck S epsilon p t,
      N.map.source = spatialNeckBuffer epsilon ∧
      N.map.target = _root_.Set.range W.embedding ∧
      N.center = yStar ∧
      (∀ z : spatialNeckBuffer epsilon, N.map z.val = W.embedding z) ∧
      N.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) = W.embedding '' spatialNeckCentralDomain epsilon := by
  classical
  obtain ⟨F, hsource, htarget, hmap, hcentral⟩ := W.exists_partialDiffeomorph
  let K : Set Cylinder := _root_.Set.univ ×ˢ _root_.Set.Icc (-epsilon⁻¹) epsilon⁻¹
  let U : Set Cylinder := _root_.Set.univ ×ˢ _root_.Set.Ioo (-epsilon⁻¹) epsilon⁻¹
  have hK : IsCompact K := isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc
  have hKU : K ⊆ spatialNeckBuffer epsilon := by
    intro x hx
    change -epsilon⁻¹ - 1 < x.2 ∧ x.2 < epsilon⁻¹ + 1
    have h := hx.2
    constructor <;> linarith [h.1, h.2]
  have hUK : U ⊆ K := fun _ hx => ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
  let P : ℝ → Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2 := fun s =>
    (exists_tensor0SField_eqOn_openSubtype 2 (spatialNeckBuffer epsilon) hK hKU
      (metricTensorField (strongNeckNormalizedMetric S p t W.scalar_pos W.smooth_embedding s))).choose
  have hP (s : ℝ) (x : spatialNeckBuffer epsilon) (hx : x.val ∈ K)
      (v : Fin 2 → TangentSpace IC x) :
      P s x.val v =
        (strongNeckNormalizedMetric S p t W.scalar_pos W.smooth_embedding s).inner x (v 0) (v 1) :=
    (exists_tensor0SField_eqOn_openSubtype 2 (spatialNeckBuffer epsilon) hK hKU
      (metricTensorField (strongNeckNormalizedMetric S p t W.scalar_pos W.smooth_embedding s))).choose_spec
        x hx v
  let J : ℕ → ℝ → Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2 := fun b s =>
    (exists_tensor0SField_eqOn_openSubtype 2 (spatialNeckBuffer epsilon) hK hKU (W.jet b s)).choose
  have hJ (b : ℕ) (s : ℝ) (x : spatialNeckBuffer epsilon) (hx : x.val ∈ K)
      (v : Fin 2 → TangentSpace IC x) : J b s x.val v = W.jet b s x v :=
    (exists_tensor0SField_eqOn_openSubtype 2 (spatialNeckBuffer epsilon) hK hKU
      (W.jet b s)).choose_spec x hx v
  let jet : ℕ → ℝ → Tensor0SField (I := IC) (M := Cylinder) (n := ∞) 2
    | 0, s => P s - metricTensorField (cylinderReferenceMetric s)
    | b + 1, s => J (b + 1) s
  have hjet (b : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc (-1 : ℝ) 0)
      (x : spatialNeckBuffer epsilon) (hx : x.val ∈ K)
      (v : Fin 2 → TangentSpace IC x) : jet b s x.val v = W.jet b s x v := by
    cases b with
    | zero =>
      change P s x.val v - (cylinderReferenceMetric s).inner x.val (v 0) (v 1) = _
      rw [hP s x hx v, W.jet_zero s hs x v,
        strongNeckBackgroundMetric_eq_reference epsilon s hs.2,
        SmoothRiemannianMetric.restrictOpen_inner]
    | succ b => exact hJ (b + 1) s x hx v
  have hderiv (x : spatialNeckBuffer epsilon) (v : TangentSpace IC x) :
      mfderiv IC I3 W.embedding x v = mfderiv IC I3 F x.val v := by
    have hfun : (F ∘ (Subtype.val : spatialNeckBuffer epsilon → Cylinder)) =
        W.embedding := funext hmap
    have hF := F.mdifferentiableAt (by simp)
      (by rw [hsource]; exact x.property)
    have hval : MDifferentiableAt IC IC
        (Subtype.val : spatialNeckBuffer epsilon → Cylinder) x :=
      (contMDiff_subtype_val (I := IC) (U := spatialNeckBuffer epsilon)
        (n := ∞)).mdifferentiableAt (by decide)
    have h := mfderiv_comp x hF hval
    rw [hfun, mfderiv_subtype_val] at h
    exact DFunLike.congr_fun h v
  have hclose (a b : ℕ) (hab : a + 2 * b ≤ Nat.ceil epsilon⁻¹)
      (s : ℝ) (hs : s ∈ _root_.Set.Icc (-1 : ℝ) 0) (y : Cylinder) (hy : y ∈ U) :
      tensor02CovDerivNormWith a (jet b s)
        (cylinderReferenceMetric s) (cylinderReferenceMetric s) y ≤ epsilon := by
    let x : spatialNeckBuffer epsilon := ⟨y, hKU (hUK hy)⟩
    have hnear : {z : spatialNeckBuffer epsilon | z.val ∈ U} ∈ 𝓝 x :=
      ((isOpen_univ.prod isOpen_Ioo).preimage continuous_subtype_val).mem_nhds hy
    have heq : ∀ᶠ z : spatialNeckBuffer epsilon in 𝓝 x,
        restrictOpen0S (I := IC) 2 (V := spatialNeckBuffer epsilon) (jet b s) z =
          W.jet b s z := by
      filter_upwards [hnear] with z hz
      ext v
      exact hjet b s hs z (hUK hz) v
    obtain ⟨delta, _, hdelta, hc⟩ := W.closeness
    calc
      tensor02CovDerivNormWith a (jet b s)
          (cylinderReferenceMetric s) (cylinderReferenceMetric s) y =
        tensor02CovDerivNormWith a
          (restrictOpen0S (I := IC) 2 (V := spatialNeckBuffer epsilon) (jet b s))
          (strongNeckBackgroundMetric epsilon s) (strongNeckBackgroundMetric epsilon s) x := by
            rw [strongNeckBackgroundMetric_eq_reference epsilon s hs.2,
              tensor02CovDerivNormWith_restrictOpen0S]
      _ = tensor02CovDerivNormWith a (W.jet b s)
          (strongNeckBackgroundMetric epsilon s) (strongNeckBackgroundMetric epsilon s) x :=
        tensor02CovDerivNormWith_eq_of_eventuallyEq _ _ _ _ a x heq
      _ ≤ delta := hc a b hab s hs x ⟨hy.2.1.le, hy.2.2.le⟩
      _ ≤ epsilon := hdelta.le
  let cmp : MetricComparisonOn cylinderReference.metric
      (rescaledMetric S t (S.scalar t p) W.scalar_pos) F U (_root_.Set.Icc (-1 : ℝ) 0)
      (Nat.ceil epsilon⁻¹) epsilon :=
    { pullback := P
      pullback_eq := by
        intro s y hy v
        let x : spatialNeckBuffer epsilon := ⟨y, hKU (hUK hy)⟩
        rw [hP s x (hUK hy) v]
        erw [strongNeckNormalizedMetric_inner, ← hmap x,
          hderiv x (v 0), hderiv x (v 1)]
        rfl
      jet := jet
      jet_zero := fun _ _ _ => rfl
      jet_succ := by
        intro b s hs y hy v
        let x : spatialNeckBuffer epsilon := ⟨y, hKU (hUK hy)⟩
        rw [hjet (b + 1) s hs x (hUK hy) v]
        apply ((W.jet_succ b s hs x v).derivWithin
          (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0) s hs)).symm.trans
        exact derivWithin_congr (fun r hr => (hjet b r hr x (hUK hy) v).symm)
          (hjet b s hs x (hUK hy) v).symm
      equivalence := by
        intro s hs y hy v
        apply tensor_apply_bounds_of_metricTensorErrorNorm_le (P s) (cylinderReferenceMetric s) _ v
        exact hclose 0 0 (by simp) s hs y hy
      close := hclose }
  refine ⟨{
    eps_pos := W.epsilon_pos
    eps_small := hsmall
    Q_pos := W.scalar_pos
    cylinder := cylinderReference
    map := F
    center := yStar
    center_eq := (hmap (spatialNeckCentralPoint epsilon W.epsilon_pos yStar)).trans W.marked
    domain := fun y hy => hsource.symm ▸ hKU (hUK hy)
    time_domain := W.time_window
    comparison := cmp }, hsource, htarget, rfl, hmap, hcentral⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StrongNeckWitness.exists_strongNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StrongNeckWitness.exists_strongNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StrongNeckWitness.exists_strongNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StrongNeckWitness.exists_strongNeck

end DifferentialGeometry.PDE.RicciFlow.Perelman
