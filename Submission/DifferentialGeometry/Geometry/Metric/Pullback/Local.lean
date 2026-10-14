import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Cross
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import Submission.DifferentialGeometry.Geometry.Metric.Construction.Existence
import Submission.DifferentialGeometry.Geometry.Metric.Path.Composition
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open _root_.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N]

private theorem infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

run_cmd do
  let target := ``Submission.DifferentialGeometry.infty_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.infty_ne_zero target :: scope.openDecls } }

noncomputable def localPullInner
    (g : SmoothRiemannianMetric J N) (f : M → N) (x : M) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real :=
  let D : TangentSpace I x →L[Real] TangentSpace J (f x) :=
    mfderiv I J f x
  (ContinuousLinearMap.precomp Real D).comp ((g.inner (f x)).comp D)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPullInner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPullInner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPullInner ``Submission.DifferentialGeometry.localPullInner

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
theorem localPullInner_apply
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (x : M) (v w : TangentSpace I x) :
    localPullInner (I := I) (J := J) g f x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
  simp only [localPullInner, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPullInner_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPullInner_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPullInner_apply ``Submission.DifferentialGeometry.localPullInner_apply

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
private theorem localPullInner_symm
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (x : M) (v w : TangentSpace I x) :
    localPullInner (I := I) (J := J) g f x v w =
      localPullInner (I := I) (J := J) g f x w v := by
  rw [localPullInner_apply, localPullInner_apply]
  exact g.symm (f x) _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.localPullInner_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.localPullInner_symm target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
private theorem localPullInner_pos
    (g : SmoothRiemannianMetric J N) {f : M → N}
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < localPullInner (I := I) (J := J) g f x v v := by
  rw [localPullInner_apply]
  have hD :
      mfderiv I J f x v ≠ 0 := by
    intro hzero
    apply hv
    exact hinj x (by simpa only [map_zero] using hzero)
  exact g.pos (f x) _ hD

run_cmd do
  let target := ``Submission.DifferentialGeometry.localPullInner_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.localPullInner_pos target :: scope.openDecls } }

omit [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
private theorem localPullInner_bdd
    (g : SmoothRiemannianMetric J N) {f : M → N}
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) :
    ∀ x : M, Bornology.IsVonNBounded Real
      {v : TangentSpace I x |
        localPullInner (I := I) (J := J) g f x v v < 1} := by
  intro x
  exact Geometry.posDef_isVonNBounded (E := E)
    (localPullInner (I := I) (J := J) g f x)
    (localPullInner_pos (I := I) (J := J) g hinj x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.localPullInner_bdd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.localPullInner_bdd target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem push_smooth
    {f : M → N} (hf : ContMDiff I J ∞ f)
    (Y : ∀ x : M, TangentSpace I x)
    (hY : ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := TangentSpace I) x (Y x))) :
    ContMDiff I (J.prod 𝓘(Real, F)) ∞
      (fun x : M => TotalSpace.mk' F
        (E := (TangentSpace J : N → Type _))
        (f x) (mfderiv I J f x (Y x))) := by
  exact (hf.contMDiff_tangentMap (le_refl _)).comp hY

run_cmd do
  let target := ``Submission.DifferentialGeometry.push_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.push_smooth target :: scope.openDecls } }

omit [FiniteDimensional ℝ F] in
theorem contMDiff_localPullInner
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : ContMDiff I J ∞ f) :
    ContMDiff I (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun x : M => TotalSpace.mk' (E →L[Real] E →L[Real] Real) x
        (localPullInner (I := I) (J := J) g f x)) := by
  classical
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : M => TangentSpace I x →L[Real] Real)
    (φ := fun x : M => localPullInner (I := I) (J := J) g f x)
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : M => Real)
    (φ := fun x : M =>
      localPullInner (I := I) (J := J) g f x (Y x))
  intro W
  have hY := push_smooth (I := I) (J := J)
    hf (fun x => Y x) Y.contMDiff
  have hW := push_smooth (I := I) (J := J)
    hf (fun x => W x) W.contMDiff
  have hg :
      ContMDiff I (J.prod 𝓘(Real, F →L[Real] F →L[Real] Real)) ∞
        (fun x : M => TotalSpace.mk'
          (F →L[Real] F →L[Real] Real)
          (E := fun y : N =>
            TangentSpace J y →L[Real] TangentSpace J y →L[Real] Real)
          (f x) (g.inner (f x))) :=
    g.contMDiff.comp hf
  have htotal :
      ContMDiff I (J.prod 𝓘(Real, Real)) ∞
        (fun x : M => TotalSpace.mk' Real
          (E := Bundle.Trivial N Real) (f x)
          (g.inner (f x)
            (mfderiv I J f x (Y x))
            (mfderiv I J f x (W x)))) :=
    ContMDiff.clm_bundle_apply₂
      (E₁ := fun y : N => TangentSpace J y)
      (E₂ := fun y : N => TangentSpace J y)
      (E₃ := fun _ : N => Real)
      (b := f)
      (ψ := fun x => g.inner (f x))
      (v := fun x => mfderiv I J f x (Y x))
      (w := fun x => mfderiv I J f x (W x))
      hg hY hW
  have hscalar :
      ContMDiff I 𝓘(Real, Real) ∞
        (fun x : M =>
          g.inner (f x)
            (mfderiv I J f x (Y x))
            (mfderiv I J f x (W x))) := by
    intro x
    have hx := htotal x
    rw [_root_.Bundle.contMDiffAt_totalSpace] at hx
    exact hx.2
  have hpull :
      ContMDiff I 𝓘(Real, Real) ∞
        (fun x : M =>
          localPullInner (I := I) (J := J) g f x (Y x) (W x)) := by
    simpa only [localPullInner_apply] using hscalar
  intro x
  rw [_root_.Bundle.contMDiffAt_section]
  refine hpull.contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards with y
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.contMDiff_localPullInner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.contMDiff_localPullInner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.contMDiff_localPullInner ``Submission.DifferentialGeometry.contMDiff_localPullInner

noncomputable def SmoothRiemannianMetric.pullbackOfImmersion
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : ContMDiff I J ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) :
    SmoothRiemannianMetric I M where
  inner x := localPullInner (I := I) (J := J) g f x
  symm x v w := localPullInner_symm (I := I) (J := J) g f x v w
  pos x v hv := localPullInner_pos (I := I) (J := J) g hinj x v hv
  isVonNBounded := localPullInner_bdd (I := I) (J := J) g hinj
  contMDiff := contMDiff_localPullInner (I := I) (J := J) g f hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion ``Submission.DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion

noncomputable def localPullMetric
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) :
    SmoothRiemannianMetric I M :=
  g.pullbackOfImmersion (I := I) f hf.contMDiff fun x => by
    rw [← hf.mfderivToContinuousLinearEquiv_coe infty_ne_zero]
    exact (hf.mfderivToContinuousLinearEquiv infty_ne_zero x).injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPullMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPullMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPullMetric ``Submission.DifferentialGeometry.localPullMetric

omit [FiniteDimensional ℝ F] in
theorem SmoothRiemannianMetric.pullbackOfImmersion_inner
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : ContMDiff I J ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (x : M) (v w : TangentSpace I x) :
    (g.pullbackOfImmersion (I := I) f hf hinj).inner x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) :=
  localPullInner_apply (I := I) (J := J) g f x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion_inner ``Submission.DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion_inner

@[simp]
theorem SmoothRiemannianMetric.pullbackOfImmersion_id [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    g.pullbackOfImmersion (id : M → M) contMDiff_id
      (fun x => by rw [mfderiv_id]; exact Function.injective_id) = g := by
  ext x v w
  rw [SmoothRiemannianMetric.pullbackOfImmersion_inner, mfderiv_id]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion_id ``Submission.DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion_id

theorem SmoothRiemannianMetric.pullbackOfImmersion_comp
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Type*} [TopologicalSpace K] {L : ModelWithCorners ℝ V K}
    {P : Type*} [TopologicalSpace P] [ChartedSpace K P] [IsManifold L ∞ P]
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric L P) (h : N → P) (f : M → N)
    (hh : ContMDiff J L ∞ h) (hf : ContMDiff I J ∞ f)
    (hhinj : ∀ x, Function.Injective (mfderiv J L h x))
    (hfinj : ∀ x, Function.Injective (mfderiv I J f x)) :
    (g.pullbackOfImmersion h hh hhinj).pullbackOfImmersion f hf hfinj =
      g.pullbackOfImmersion (h ∘ f) (hh.comp hf)
        (fun x => by
          rw [mfderiv_comp x (hh.mdifferentiableAt infty_ne_zero)
            (hf.mdifferentiableAt infty_ne_zero)]
          exact (hhinj (f x)).comp (hfinj x)) := by
  ext x v w
  rw [SmoothRiemannianMetric.pullbackOfImmersion_inner,
    SmoothRiemannianMetric.pullbackOfImmersion_inner,
    SmoothRiemannianMetric.pullbackOfImmersion_inner,
    mfderiv_comp x (hh.mdifferentiableAt infty_ne_zero)
      (hf.mdifferentiableAt infty_ne_zero)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion_comp ``Submission.DifferentialGeometry.SmoothRiemannianMetric.pullbackOfImmersion_comp

omit [FiniteDimensional ℝ F] in
theorem localPullMetric_inner
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f)
    (x : M) (v w : TangentSpace I x) :
    (localPullMetric (I := I) (J := J) g f hf).inner x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) :=
  localPullInner_apply (I := I) (J := J) g f x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPullMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPullMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPullMetric_inner ``Submission.DifferentialGeometry.localPullMetric_inner

omit [FiniteDimensional ℝ F] in
theorem localPull_enorm
    [T2Space M]
    [_root_.Bundle.RiemannianBundle (fun y : N ↦ TangentSpace J y)]
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (y : N) (w : TangentSpace J y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f)
    (x : M) (v : TangentSpace I x) :
    letI : _root_.Bundle.RiemannianBundle
        (fun y : M ↦ TangentSpace I y) :=
      ⟨(localPullMetric (I := I) (J := J) g f hf).toRiemannianMetric⟩
    ‖mfderiv I J f x v‖ₑ = ‖v‖ₑ := by
  let : _root_.Bundle.RiemannianBundle
      (fun y : M ↦ TangentSpace I y) :=
    ⟨(localPullMetric (I := I) (J := J) g f hf).toRiemannianMetric⟩
  rw [hEnorm, ← ofReal_norm, norm_eq_sqrt_real_inner]
  have hsrc :
      (_root_.Inner.inner Real v v : Real) =
        (localPullMetric (I := I) (J := J) g f hf).inner x v v :=
    rfl
  rw [hsrc, localPullMetric_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPull_enorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPull_enorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPull_enorm ``Submission.DifferentialGeometry.localPull_enorm

omit [FiniteDimensional ℝ F] in
theorem localPull_pathLen
    [T2Space M]
    [_root_.Bundle.RiemannianBundle (fun y : N ↦ TangentSpace J y)]
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (y : N) (w : TangentSpace J y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f)
    {γ : Real → M} {a b : Real}
    (hγ : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc a b)) :
    letI : _root_.Bundle.RiemannianBundle
        (fun y : M ↦ TangentSpace I y) :=
      ⟨(localPullMetric (I := I) (J := J) g f hf).toRiemannianMetric⟩
    Manifold.pathELength J (f ∘ γ) a b =
      Manifold.pathELength I γ a b := by
  let : _root_.Bundle.RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨(localPullMetric (I := I) (J := J) g f hf).toRiemannianMetric⟩
  apply Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq f
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact ((hγ.mdifferentiableOn one_ne_zero) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  · exact Filter.Eventually.of_forall
      (fun _ => hf.contMDiff.mdifferentiableAt (by decide))
  · exact Filter.Eventually.of_forall
      (fun t => localPull_enorm g hEnorm f hf (γ t) _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPull_pathLen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPull_pathLen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPull_pathLen ``Submission.DifferentialGeometry.localPull_pathLen

theorem localPullMetric_subtype_val
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U] :
    localPullMetric g (Subtype.val : U → M) (isLocalDiffeomorph_subtype_val U) =
      g.restrictOpen U := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
    mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPullMetric_subtype_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPullMetric_subtype_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPullMetric_subtype_val ``Submission.DifferentialGeometry.localPullMetric_subtype_val

omit [FiniteDimensional ℝ F] in
theorem Diffeomorph.pullbackMetricCross_eq_localPullMetric
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    Diffeomorph.pullbackMetricCross g Φ = localPullMetric g Φ Φ.isLocalDiffeomorph := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetricCross_inner, localPullMetric_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetricCross_eq_localPullMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetricCross_eq_localPullMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetricCross_eq_localPullMetric ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetricCross_eq_localPullMetric

end DifferentialGeometry
