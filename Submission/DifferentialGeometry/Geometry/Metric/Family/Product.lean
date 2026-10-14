import Submission.DifferentialGeometry.Geometry.Metric.Product
import Submission.DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair
import Submission.DifferentialGeometry.Geometry.Metric.Family.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ F] [IsManifold J ∞ N] [T2Space N] in
private theorem mfderiv_fst_apply
    (x : M × N) (v : TangentSpace (I.prod J) x) :
    mfderiv (I.prod J) I Prod.fst x v = v.1 := by
  rw [mfderiv_fst]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.mfderiv_fst_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.mfderiv_fst_apply target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ F] [IsManifold J ∞ N] [T2Space N] in
private theorem mfderiv_snd_apply
    (x : M × N) (v : TangentSpace (I.prod J) x) :
    mfderiv (I.prod J) J Prod.snd x v = v.2 := by
  rw [mfderiv_snd]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.mfderiv_snd_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.mfderiv_snd_apply target :: scope.openDecls } }

private theorem prod_inner_mfderiv
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (v w : TangentSpace (I.prod J) x) :
    (g.prod h).inner x v w =
      g.inner x.1 (mfderiv (I.prod J) I Prod.fst x v)
          (mfderiv (I.prod J) I Prod.fst x w) +
        h.inner x.2 (mfderiv (I.prod J) J Prod.snd x v)
          (mfderiv (I.prod J) J Prod.snd x w) :=
  (SmoothRiemannianMetric.prod_inner g h x v w).trans <|
    congrArg₂ (· + ·)
      (congrArg₂ (fun a b => g.inner x.1 a b)
        (mfderiv_fst_apply x v).symm (mfderiv_fst_apply x w).symm)
      (congrArg₂ (fun a b => h.inner x.2 a b)
        (mfderiv_snd_apply x v).symm (mfderiv_snd_apply x w).symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.prod_inner_mfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.prod_inner_mfderiv target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
private theorem prod_frame_contMDiffOn_of_joint
    {A : Set ℝ} {g : ℝ → SmoothRiemannianMetric I M}
    {h : ℝ → SmoothRiemannianMetric J N}
    (hmg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set M)))
    (hmh : ContMDiffOn (𝓘(ℝ, ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun p : ℝ × N => (⟨p.2, (h p.1).inner p.2⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x => TangentSpace J x →L[ℝ] TangentSpace J x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set N)))
    {Idx : Type}
    (frame : Idx → (x : M × N) → TangentSpace (I.prod J) x) {u : Set (M × N)}
    (hframe : ∀ k, ContMDiffOn (I.prod J) ((I.prod J).prod 𝓘(ℝ, E × F)) ∞
      (fun x => TotalSpace.mk' (E × F) x (frame k x)) u) (i j : Idx) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod J)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × (M × N) => ((g p.1).prod (h p.1)).inner p.2 (frame i p.2) (frame j p.2))
      (A ×ˢ u) := by
  have hmapg : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod J)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × (M × N) => (p.1, p.2.1)) :=
    contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)
  have hmaph : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod J)) (𝓘(ℝ, ℝ).prod J) ∞
      (fun p : ℝ × (M × N) => (p.1, p.2.2)) :=
    contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)
  have hmg' := hmg.comp hmapg.contMDiffOn (fun p hp => ⟨hp.1, Set.mem_univ _⟩ :
    Set.MapsTo (fun p : ℝ × (M × N) => (p.1, p.2.1)) (A ×ˢ u) (A ×ˢ Set.univ))
  have hmh' := hmh.comp hmaph.contMDiffOn (fun p hp => ⟨hp.1, Set.mem_univ _⟩ :
    Set.MapsTo (fun p : ℝ × (M × N) => (p.1, p.2.2)) (A ×ˢ u) (A ×ˢ Set.univ))
  have hv (k : Idx) : ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod J)) ((I.prod J).prod 𝓘(ℝ, E × F)) ∞
      (fun p : ℝ × (M × N) => TotalSpace.mk' (E × F) p.2 (frame k p.2)) (A ×ˢ u) :=
    (hframe k).comp contMDiffOn_snd (fun p hp => hp.2)
  have hvg (k : Idx) :=
    (contMDiff_fst.contMDiff_tangentMap (m := (∞ : WithTop ℕ∞)) le_rfl).comp_contMDiffOn (hv k)
  have hvh (k : Idx) :=
    (contMDiff_snd.contMDiff_tangentMap (m := (∞ : WithTop ℕ∞)) le_rfl).comp_contMDiffOn (hv k)
  have hpg := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I) (E₂ := TangentSpace I) (E₃ := Bundle.Trivial M ℝ)
    (b := fun p : ℝ × (M × N) => p.2.1) hmg' (hvg i) (hvg j)
  have hph := ContMDiffOn.clm_bundle_apply₂ (F₁ := F) (F₂ := F) (F₃ := ℝ)
    (E₁ := TangentSpace J) (E₂ := TangentSpace J) (E₃ := Bundle.Trivial N ℝ)
    (b := fun p : ℝ × (M × N) => p.2.2) hmh' (hvh i) (hvh j)
  have hpgscalar : ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod J)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × (M × N) => (g p.1).inner p.2.1
        (mfderiv (I.prod J) I Prod.fst p.2 (frame i p.2))
        (mfderiv (I.prod J) I Prod.fst p.2 (frame j p.2))) (A ×ˢ u) := by
    intro p hp
    have hs := hpg p hp
    rw [Bundle.contMDiffWithinAt_totalSpace] at hs
    exact hs.2
  have hphscalar : ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod J)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × (M × N) => (h p.1).inner p.2.2
        (mfderiv (I.prod J) J Prod.snd p.2 (frame i p.2))
        (mfderiv (I.prod J) J Prod.snd p.2 (frame j p.2))) (A ×ˢ u) := by
    intro p hp
    have hs := hph p hp
    rw [Bundle.contMDiffWithinAt_totalSpace] at hs
    exact hs.2
  apply (hpgscalar.add hphscalar).congr
  intro p hp
  exact prod_inner_mfderiv (g p.1) (h p.1) p.2 (frame i p.2) (frame j p.2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.prod_frame_contMDiffOn_of_joint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.prod_frame_contMDiffOn_of_joint target :: scope.openDecls } }


theorem metricCLMSection_jointContMDiffOn_prod
    (g : ℝ → SmoothRiemannianMetric I M) (h : ℝ → SmoothRiemannianMetric J N)
    (A : Set ℝ)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set M)))
    (hh : ContMDiffOn (𝓘(ℝ, ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun p : ℝ × N => (⟨p.2, (h p.1).inner p.2⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x => TangentSpace J x →L[ℝ] TangentSpace J x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set N))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod J))
      ((I.prod J).prod 𝓘(ℝ, (E × F) →L[ℝ] (E × F) →L[ℝ] ℝ)) ∞
      (fun p : ℝ × (M × N) =>
        (⟨p.2, ((g p.1).prod (h p.1)).inner p.2⟩ :
          _root_.Bundle.TotalSpace ((E × F) →L[ℝ] (E × F) →L[ℝ] ℝ)
            (fun x => TangentSpace (I.prod J) x →L[ℝ]
              TangentSpace (I.prod J) x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set (M × N))) := by
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on (fun t => (g t).prod (h t)) A
  intro x₀ i j
  exact prod_frame_contMDiffOn_of_joint hg hh (chartBasisVecFiber (I := I.prod J) x₀)
    (chartBasisVec_contMDiffOn (I := I.prod J) x₀) i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricCLMSection_jointContMDiffOn_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricCLMSection_jointContMDiffOn_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricCLMSection_jointContMDiffOn_prod ``Submission.DifferentialGeometry.Geometry.Curvature.metricCLMSection_jointContMDiffOn_prod

private theorem prod_frame_contMDiffOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    {h : ℝ → SmoothRiemannianMetric J N}
    (hg : MetricFamilySmoothOn D g) (hh : MetricFamilySmoothOn D h)
    {Idx : Type}
    (frame : Idx → (x : M × N) → TangentSpace (I.prod J) x) {u : Set (M × N)}
    (hframe : IsLocalFrameOn (I.prod J) (E × F) ∞ frame u) (i j : Idx) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod J)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × (M × N) => ((g p.1).prod (h p.1)).inner p.2 (frame i p.2) (frame j p.2))
      (D.regular ×ˢ u) := by
  have hmg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (D.regular ×ˢ (Set.univ : Set M)) := by
    intro p hp
    exact (hg.metricCLMSmoothAt (D.regular_isOpen.mem_nhds hp.1)).contMDiffWithinAt
  have hmh : ContMDiffOn (𝓘(ℝ, ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun p : ℝ × N => (⟨p.2, (h p.1).inner p.2⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x => TangentSpace J x →L[ℝ] TangentSpace J x →L[ℝ] ℝ)))
      (D.regular ×ˢ (Set.univ : Set N)) := by
    intro p hp
    exact (hh.metricCLMSmoothAt (D.regular_isOpen.mem_nhds hp.1)).contMDiffWithinAt
  exact prod_frame_contMDiffOn_of_joint hmg hmh frame hframe.contMDiffOn i j

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.prod_frame_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.prod_frame_contMDiffOn target :: scope.openDecls } }

private theorem prod_metricTensor_cont
    {K : Set Real}
    (g : Real → SmoothRiemannianMetric I M)
    (h : Real → SmoothRiemannianMetric J N)
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricTensorField (I := I) (g t) x))
    (hh : tensor0SFamilyContinuousOnSet (I := J) (M := N) 2 K
      (fun t x => metricTensorField (I := J) (h t) x)) :
    tensor0SFamilyContinuousOnSet (I := I.prod J) (M := M × N) 2 K
      (fun t x => metricTensorField (I := I.prod J) ((g t).prod (h t)) x) := by
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp
    (N := fun x₀ => (_root_.FiberBundle.trivializationAt (E × F) (TangentSpace (I.prod J)) x₀).baseSet)
    (hN := fun x₀ => (Trivialization.open_baseSet _).mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt (E × F) (TangentSpace (I.prod J)) x₀))
  intro x₀ idx
  rw [continuousOn_iff_continuous_domRestrict]
  let P := {q : {t : Real // t ∈ K} × (M × N) //
    q.2 ∈ (_root_.FiberBundle.trivializationAt (E × F) (TangentSpace (I.prod J)) x₀).baseSet}
  have hslot : ∀ k : Fin 2, Continuous (fun p : P =>
      chartBasisVec (I := I.prod J) x₀ (idx k) p.1.2) := by
    intro k
    exact (chartBasisVec_contMDiffOn (I := I.prod J) x₀ (idx k)).continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val) (fun p => p.2)
  have hslot₁ : ∀ k : Fin 2, Continuous (fun p : P =>
      TotalSpace.mk' E (E := TangentSpace I) p.1.2.1
        (mfderiv (I.prod J) I Prod.fst p.1.2
          (chartBasisVecFiber (I := I.prod J) x₀ (idx k) p.1.2))) := by
    intro k
    exact ((contMDiff_fst (n := 1)).continuous_tangentMap le_rfl).comp (hslot k)
  have hslot₂ : ∀ k : Fin 2, Continuous (fun p : P =>
      TotalSpace.mk' F (E := TangentSpace J) p.1.2.2
        (mfderiv (I.prod J) J Prod.snd p.1.2
          (chartBasisVecFiber (I := I.prod J) x₀ (idx k) p.1.2))) := by
    intro k
    exact ((contMDiff_snd (n := 1)).continuous_tangentMap le_rfl).comp (hslot k)
  have hc₁ := hg.eval_continuous
    (τ := fun p : P => p.1.1.1) (b := fun p : P => p.1.2.1)
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
    (fun p => p.1.1.2)
    (continuous_fst.comp (continuous_snd.comp continuous_subtype_val)) hslot₁
  have hc₂ := hh.eval_continuous
    (τ := fun p : P => p.1.1.1) (b := fun p : P => p.1.2.2)
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
    (fun p => p.1.1.2)
    (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)) hslot₂
  refine (hc₁.add hc₂).congr ?_
  intro p
  simp only [metricTensorField_apply, SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd,
    Set.domRestrict_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.prod_metricTensor_cont
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.prod_metricTensor_cont target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
theorem MetricFamilySmoothOn.prod
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    {h : ℝ → SmoothRiemannianMetric J N}
    (hg : MetricFamilySmoothOn D g) (hh : MetricFamilySmoothOn D h) :
    MetricFamilySmoothOn D (fun t => (g t).prod (h t)) where
  coeff := by
    intro x v w
    apply ((hg.coeff x.1 (mfderiv (I.prod J) I Prod.fst x v)
      (mfderiv (I.prod J) I Prod.fst x w)).add
      (hh.coeff x.2 (mfderiv (I.prod J) J Prod.snd x v)
        (mfderiv (I.prod J) J Prod.snd x w))).congr
    intro t _
    exact prod_inner_mfderiv (g t) (h t) x v w
  coeff_cont := by
    intro x v w
    apply ((hg.coeff_cont x.1 (mfderiv (I.prod J) I Prod.fst x v)
      (mfderiv (I.prod J) I Prod.fst x w)).add
      (hh.coeff_cont x.2 (mfderiv (I.prod J) J Prod.snd x v)
        (mfderiv (I.prod J) J Prod.snd x w))).congr
    intro t _
    exact prod_inner_mfderiv (g t) (h t) x v w
  metricTensor_cont := prod_metricTensor_cont g h hg.metricTensor_cont hh.metricTensor_cont
  frameCompSmooth := by
    intro Idx _ frame u hframe i j
    exact prod_frame_contMDiffOn hg hh frame hframe i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.prod ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.prod

end DifferentialGeometry.Geometry.Curvature
