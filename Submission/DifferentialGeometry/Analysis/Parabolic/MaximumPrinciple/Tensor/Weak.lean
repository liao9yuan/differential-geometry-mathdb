import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.Barrier.Certification
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.Barrier.Continuation
import Submission.DifferentialGeometry.Geometry.Operator.Heat.Tensor
import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

open _root_.Submission.DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.PDE.RicciFlow

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem tensorBarrier_first_null_of_failure
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hcompact : TensorFirstNullCompactnessOn (I := I) (M := M)
      G S epsilon delta t0)
    (hinit_pos : ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x)
    (hfail : ¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0)
      (Set.Icc t0 (t0 + delta))) :
    Nonempty (TensorFirstNullData (I := I) (M := M) G S epsilon delta t0) := by
  exact hcompact.firstNull_of_failure hinit_pos hfail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tensorBarrier_first_null_of_failure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tensorBarrier_first_null_of_failure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tensorBarrier_first_null_of_failure ``Submission.DifferentialGeometry.PDE.RicciFlow.tensorBarrier_first_null_of_failure

private theorem firstNullOrder
    {timeDeriv laplacian drift reaction : Real}
    (htime : timeDeriv ≤ 0)
    (hlap : 0 ≤ laplacian)
    (hdrift : drift = 0)
    (hreaction : 0 ≤ reaction)
    (hstrict : drift + reaction < timeDeriv - laplacian) :
    False := by
  have hsource_nonneg : 0 ≤ drift + reaction := by
    simpa [hdrift] using hreaction
  have htarget_pos : 0 < timeDeriv - laplacian :=
    lt_of_le_of_lt hsource_nonneg hstrict
  have htarget_nonpos : timeDeriv - laplacian ≤ 0 := by
    simpa [sub_eq_add_neg] using add_nonpos htime (neg_nonpos.mpr hlap)
  exact (not_lt_of_ge htarget_nonpos) htarget_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.firstNullOrder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.firstNullOrder target :: scope.openDecls } }

omit [IsManifold I 2 M] in
theorem tensor_first_null_contradiction
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G
      N (Set.Icc t0 (t0 + delta)))
    (hsym : TwoTensorFamilySymmetricOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)))
    (hbilin :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) -> ∀ x,
        TwoTensorBilinearAt (I := I) (M := M) (S t) x)
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (hsigns : TensorFirstNullScalarSigns (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0 d) :
    False := by
  rcases hstrict with ⟨timeDeriv, _hderiv, hstrict_eval⟩
  have ht1_mem_slab : d.t1 ∈ Set.Icc t0 (t0 + delta) :=
    ⟨le_of_lt d.t1_mem.1, d.t1_mem.2⟩
  have _hstrict_at_first_null :
      tensorHeatWithDrift2QuadMetricAt (I := I) (G d.t1) (X d.t1)
          (nabla2Barrier d.t1 d.x1) (nablaBarrier d.t1 d.x1) d.v +
        N d.t1 (G d.t1)
            (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
            d.x1 d.v d.v <
        timeDeriv d.t1 d.x1 d.v := by
    exact hstrict_eval d.t1 d.t1_mem d.x1 d.v d.v_ne_zero
  have ht1_mem_until : d.t1 ∈ Set.Icc t0 d.t1 :=
    ⟨le_of_lt d.t1_mem.1, le_rfl⟩
  have hbarrier_nonnegative :
      TwoTensorNonnegativeAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
        d.x1 :=
    d.nonnegative_until d.t1 ht1_mem_until d.x1
  have hbarrier_symmetric :
      TwoTensorSymmetricAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
        d.x1 :=
    barrierSymmAt (I := I) (M := M)
      (G := G) (S := S) (epsilon := epsilon) (delta := delta)
      (t0 := t0) (t := d.t1) (x := d.x1)
      (hsym d.t1 ht1_mem_slab d.x1)
  have hbarrier_bilinear :
      TwoTensorBilinearAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
        d.x1 :=
    barrierBilinearAt (I := I) (M := M)
      (G := G) (S := S) (epsilon := epsilon) (delta := delta)
      (t0 := t0) (t := d.t1) (x := d.x1)
      (hbilin d.t1 ht1_mem_slab d.x1)
  have _hreaction_nonnegative :
      0 ≤
        N d.t1 (G d.t1)
          (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
          d.x1 d.v d.v := by
    exact hnull d.t1 ht1_mem_slab
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
      d.x1 hbarrier_symmetric hbarrier_bilinear hbarrier_nonnegative d.v d.null
  rcases hsigns with
    ⟨_signTimeDeriv, laplacian, drift, reaction,
      _hsignDeriv, _hheat_eq, _hreaction_eq,
      htime_nonpos, hlaplacian_nonneg, hdrift_zero, hreaction_nonneg, hstrict_ineq⟩
  exact firstNullOrder htime_nonpos hlaplacian_nonneg hdrift_zero
    hreaction_nonneg hstrict_ineq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tensor_first_null_contradiction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tensor_first_null_contradiction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tensor_first_null_contradiction ``Submission.DifferentialGeometry.PDE.RicciFlow.tensor_first_null_contradiction

omit [IsManifold I 2 M] in
theorem shortSlab_cert
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (hreg : TensorWeakMaximumPrincipleCompactness (I := I) (M := M) G S X N T)
    (hcert :
      ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
        TensorStrictCertSlab (I := I) (M := M) G S X N delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G
      N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t0) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      tensorBarrierUniformOnSlab (I := I) (M := M) G S delta t0 := by
  classical
  obtain ⟨delta, hdelta, hdeltaT, hstrict_uniform⟩ := hcert
  refine ⟨delta, hdelta, hdeltaT, ?_⟩
  intro epsilon hepsilon
  obtain ⟨cert⟩ := hstrict_uniform epsilon hepsilon
  by_contra hfail
  have hinit_pos : ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x :=
    tensorBarrier_initial_positive (I := I) (M := M)
      (G := G) (S := S) hepsilon.1 hdelta hinit
  have hsub : Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T := by
    intro t ht
    exact ⟨le_trans ht0.1 ht.1, le_trans ht.2 hdeltaT⟩
  have hcompact : TensorFirstNullCompactnessOn (I := I) (M := M)
      G S epsilon delta t0 :=
    hreg.firstNullCompactness epsilon delta t0 hepsilon.1 hdelta hsub
  obtain ⟨d⟩ :=
    tensorBarrier_first_null_of_failure (I := I) (M := M)
      (G := G) (S := S) (epsilon := epsilon) (delta := delta) (t0 := t0)
      hcompact hinit_pos hfail
  have hnull_slab : TensorNullEigenvectorCondition (I := I) (M := M) G
      N (Set.Icc t0 (t0 + delta)) := by
    intro t ht A x hsym hbilin hA v hv
    exact hnull t (hsub ht) A x hsym hbilin hA v hv
  exact tensor_first_null_contradiction (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := cert.nabla2Barrier) (nablaBarrier := cert.nablaBarrier)
    cert.strict hnull_slab
    (fun t ht => hreg.symmetric t (hsub ht))
    (fun t ht => hreg.bilinear t (hsub ht))
    d (cert.signs hnull_slab d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shortSlab_cert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shortSlab_cert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shortSlab_cert ``Submission.DifferentialGeometry.PDE.RicciFlow.shortSlab_cert

omit [IsManifold I 2 M] in
theorem tensorBarrier_nonnegative_on_short_slab
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    (hreg : TensorWeakMaximumPrincipleRegularityOn (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G
      N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t0) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      tensorBarrierUniformOnSlab (I := I) (M := M) G S delta t0 := by
  exact shortSlab_cert (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    ht0 hreg.toCompactness
    (certSlab_of_regularity (I := I) (M := M)
      (G := G) (S := S) (X := X) (N := N)
      ht0 ht0T hreg hparabolic)
    hnull hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tensorBarrier_nonnegative_on_short_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tensorBarrier_nonnegative_on_short_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tensorBarrier_nonnegative_on_short_slab ``Submission.DifferentialGeometry.PDE.RicciFlow.tensorBarrier_nonnegative_on_short_slab

omit [IsManifold I 2 M] in
theorem tensor_weak_maximum_principle_of_barrier_limit
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (hreg : TensorWeakMaximumPrincipleRegularityOn (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T) := by
  exact tensor_nonnegative_on_of_barrier_continuation (I := I) (M := M)
    (G := G) (S := S) hreg.barrierRegularity.tensor_eval_continuous hinit
    (fun t0 ht0 ht0T hinit_t0 =>
      shortSlab_cert (I := I) (M := M)
        (G := G) (S := S) (X := X) (N := N)
        ht0 hreg.toCompactness
        (certSlab_of_regularity (I := I) (M := M)
          (G := G) (S := S) (X := X) (N := N)
          ht0 ht0T hreg hparabolic)
        hnull hinit_t0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tensor_weak_maximum_principle_of_barrier_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tensor_weak_maximum_principle_of_barrier_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tensor_weak_maximum_principle_of_barrier_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.tensor_weak_maximum_principle_of_barrier_limit

omit [IsManifold I 2 M] in
theorem weak_maximum_principle_of_cert
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hreg : TensorWeakMaximumPrincipleCompactness (I := I) (M := M) G S X N T)
    (hcert :
      ∀ t0 : Real, t0 ∈ Set.Icc 0 T -> t0 < T ->
        ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
          TensorStrictCertSlab (I := I) (M := M) G S X N delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T) := by
  exact tensor_nonnegative_on_of_barrier_continuation (I := I) (M := M)
    (G := G) (S := S) hreg.barrierRegularity.tensor_eval_continuous hinit
    (fun t0 ht0 ht0T hinit_t0 =>
      shortSlab_cert (I := I) (M := M)
        (G := G) (S := S) (X := X) (N := N)
        ht0 hreg (hcert t0 ht0 ht0T) hnull hinit_t0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.weak_maximum_principle_of_cert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.weak_maximum_principle_of_cert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.weak_maximum_principle_of_cert ``Submission.DifferentialGeometry.PDE.RicciFlow.weak_maximum_principle_of_cert

theorem weak_maximum_principle_section_sec
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T : Real}
    (hreg : TensorWeakMaximumPrincipleSectionCompactness (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x => nabla2S t x) (fun t x => nablaS t x) T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) 0)
    (hcov1 : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (1 : WithTop ℕ∞))
    (hcovInf : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (∞ : WithTop ℕ∞))
    (hmc : ∀ t : Real,
      DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) (cov t) (G t))
    (hS : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T) := by
  exact weak_maximum_principle_of_cert (I := I) (M := M)
    (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
    (X := X) (N := N) hreg.toRaw
    (fun t0 ht0 ht0T =>
      strictCert_sec (I := I) (M := M)
        (G := G) (S := S) (X := X) (N := N)
        (nablaS := nablaS) (nabla2S := nabla2S) (cov := cov)
        ht0 ht0T hreg hparabolic hcov1 hcovInf hmc hS)
    hnull hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.weak_maximum_principle_section_sec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.weak_maximum_principle_section_sec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.weak_maximum_principle_section_sec ``Submission.DifferentialGeometry.PDE.RicciFlow.weak_maximum_principle_section_sec

structure TensorWeakMaximumPrincipleAssumptions
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (nablaS : TensorNabla1SecFamily (I := I) (M := M))
    (nabla2S : TensorNabla2SecFamily (I := I) (M := M))
    (T : Real) : Prop where
  time_nonneg : 0 ≤ T
  regularity : TensorWeakMaximumPrincipleSectionCompactness (I := I) (M := M) G S X N T
  parabolic :
    TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x => nabla2S t x) (fun t x => nablaS t x) T
  null : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T)
  initial :
    TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) 0
  connection_contMDiff_one : ∀ t : Real,
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (cov t) (1 : WithTop ℕ∞)
  connection_contMDiff_infty : ∀ t : Real,
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (cov t) (∞ : WithTop ℕ∞)
  metricCompatible : ∀ t : Real,
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) (cov t) (G t)
  spatial : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TensorWeakMaximumPrincipleAssumptions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TensorWeakMaximumPrincipleAssumptions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TensorWeakMaximumPrincipleAssumptions ``Submission.DifferentialGeometry.PDE.RicciFlow.TensorWeakMaximumPrincipleAssumptions

theorem tensor_weak_maximum_principle
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {T : Real}
    (data : TensorWeakMaximumPrincipleAssumptions (I := I) (M := M) G S X N cov nablaS nabla2S T) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T) := by
  exact weak_maximum_principle_section_sec (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nablaS := nablaS) (nabla2S := nabla2S) (cov := cov)
    data.regularity data.parabolic data.null data.initial
    data.connection_contMDiff_one data.connection_contMDiff_infty
      data.metricCompatible data.spatial

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tensor_weak_maximum_principle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tensor_weak_maximum_principle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tensor_weak_maximum_principle ``Submission.DifferentialGeometry.PDE.RicciFlow.tensor_weak_maximum_principle

omit [IsManifold I 2 M] in
theorem hamilton_tensor_weak_maximum_principle
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (hreg : TensorWeakMaximumPrincipleRegularityOn (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T) := by
  exact weak_maximum_principle_of_cert (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N) hreg.toCompactness
    (fun t0 ht0 ht0T =>
      certSlab_of_regularity (I := I) (M := M)
        (G := G) (S := S) (X := X) (N := N)
        ht0 ht0T hreg hparabolic)
    hnull hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamilton_tensor_weak_maximum_principle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamilton_tensor_weak_maximum_principle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamilton_tensor_weak_maximum_principle ``Submission.DifferentialGeometry.PDE.RicciFlow.hamilton_tensor_weak_maximum_principle

omit [IsManifold I 2 M] in
theorem hamilton_tensor_weak_maximum_principle_section
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (hreg : TensorWeakMaximumPrincipleSectionRegularity (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G (twoTensorSecToFamily (I := I) (M := M) S)
      X N nabla2S nablaS T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T) := by
  exact weak_maximum_principle_of_cert (I := I) (M := M)
    (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
    (X := X) (N := N) hreg.toCompactness.toRaw
    (fun t0 ht0 ht0T =>
      certSlab_of_sectionRegularity (I := I) (M := M)
        (G := G) (S := S) (X := X) (N := N)
        ht0 ht0T hreg hparabolic)
    hnull hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamilton_tensor_weak_maximum_principle_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamilton_tensor_weak_maximum_principle_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamilton_tensor_weak_maximum_principle_section ``Submission.DifferentialGeometry.PDE.RicciFlow.hamilton_tensor_weak_maximum_principle_section

end

end DifferentialGeometry.PDE.RicciFlow
