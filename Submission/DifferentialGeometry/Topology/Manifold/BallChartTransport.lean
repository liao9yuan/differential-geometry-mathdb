import Submission.DifferentialGeometry.Topology.Manifold.EmbeddedBallStraightening
import Submission.DifferentialGeometry.Topology.Manifold.PartialChartSupportedExtension
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.TransportDiffeomorphism

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private def diffeomorphOfContDiff (f g : E → E) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hl : Function.LeftInverse g f) (hr : Function.RightInverse g f) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  { toEquiv := { toFun := f, invFun := g, left_inv := hl, right_inv := hr }
    contMDiff_toFun := hf.contMDiff
    contMDiff_invFun := hg.contMDiff }

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.diffeomorphOfContDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.diffeomorphOfContDiff target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem diffeomorphOfContDiff_apply (f g : E → E) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hl : Function.LeftInverse g f) (hr : Function.RightInverse g f)
    (y : E) : diffeomorphOfContDiff f g hf hg hl hr y = f y := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.diffeomorphOfContDiff_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.diffeomorphOfContDiff_apply target :: scope.openDecls } }

private def modelTranslateDiffeomorph (t : E) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  diffeomorphOfContDiff (fun y => y + t) (fun y => y - t)
    (contDiff_id.add contDiff_const) (contDiff_id.sub contDiff_const)
    (fun y => by simp) (fun y => by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.modelTranslateDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.modelTranslateDiffeomorph target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem modelTranslateDiffeomorph_apply (t y : E) :
    modelTranslateDiffeomorph t y = y + t := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.modelTranslateDiffeomorph_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.modelTranslateDiffeomorph_apply target :: scope.openDecls } }

private def modelScaleDiffeomorph (c : ℝ) (hc : c ≠ 0) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  diffeomorphOfContDiff (fun y => c • y) (fun y => c⁻¹ • y)
    (contDiff_const_smul c) (contDiff_const_smul c⁻¹)
    (fun y => by simp only [smul_smul, inv_mul_cancel₀ hc, one_smul])
    (fun y => by simp only [smul_smul, mul_inv_cancel₀ hc, one_smul])

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.modelScaleDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.modelScaleDiffeomorph target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem modelScaleDiffeomorph_apply (c : ℝ) (hc : c ≠ 0) (y : E) :
    modelScaleDiffeomorph c hc y = c • y := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.modelScaleDiffeomorph_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.modelScaleDiffeomorph_apply target :: scope.openDecls } }

private def modelLinearDiffeomorph (A : E ≃L[ℝ] E) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  diffeomorphOfContDiff (fun y => A y) (fun y => A.symm y) A.contDiff A.symm.contDiff
    (fun y => A.symm_apply_apply y) (fun y => A.apply_symm_apply y)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.modelLinearDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.modelLinearDiffeomorph target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem modelLinearDiffeomorph_apply (A : E ≃L[ℝ] E) (y : E) :
    modelLinearDiffeomorph A y = A y := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.modelLinearDiffeomorph_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.modelLinearDiffeomorph_apply target :: scope.openDecls } }

private def modelAffineDiffeomorph (A₀ A₁ : E ≃L[ℝ] E) (ε₀ ε₁ : ℝ) (hε₀ : ε₀ ≠ 0)
    (hε₁ : ε₁ ≠ 0) (p₀ p₁ : E) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  (modelTranslateDiffeomorph (-p₀)).trans
    ((modelLinearDiffeomorph A₀.symm).trans
      ((modelScaleDiffeomorph ε₀⁻¹ (inv_ne_zero hε₀)).trans
        ((modelLinearDiffeomorph A₁).trans
          ((modelScaleDiffeomorph ε₁ hε₁).trans (modelTranslateDiffeomorph p₁)))))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.modelAffineDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.modelAffineDiffeomorph target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem modelAffineDiffeomorph_apply (A₀ A₁ : E ≃L[ℝ] E) (ε₀ ε₁ : ℝ)
    (hε₀ : ε₀ ≠ 0) (hε₁ : ε₁ ≠ 0) (p₀ p₁ : E) (y : E) :
    modelAffineDiffeomorph A₀ A₁ ε₀ ε₁ hε₀ hε₁ p₀ p₁ y =
      ε₁ • A₁ (ε₀⁻¹ • A₀.symm (y - p₀)) + p₁ := by
  simp only [modelAffineDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    modelTranslateDiffeomorph_apply, modelScaleDiffeomorph_apply, modelLinearDiffeomorph_apply,
    sub_eq_add_neg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.modelAffineDiffeomorph_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.modelAffineDiffeomorph_apply target :: scope.openDecls } }

theorem exists_diffeomorph_eqOn_closedBall_of_partialDiffeomorphs
    (φ₀ φ₁ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (h₀ : _root_.Metric.closedBall (0 : E) 2 ⊆ φ₀.source) (h₁ : _root_.Metric.closedBall (0 : E) 2 ⊆ φ₁.source) :
    ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ∀ x ∈ _root_.Metric.closedBall (0 : E) 2, F (φ₀ x) = φ₁ x := by
  obtain ⟨A₀, ε₀, F₀, -, hε₀, -, hF₀, -⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall φ₀ (by norm_num) h₀
      isOpen_univ (_root_.Set.subset_univ _)
  obtain ⟨A₁, ε₁, F₁, -, hε₁, -, hF₁, -⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall φ₁ (by norm_num) h₁
      isOpen_univ (_root_.Set.subset_univ _)
  have hε₀' : ε₀ ≠ 0 := ne_of_gt hε₀
  have hε₁' : ε₁ ≠ 0 := ne_of_gt hε₁
  refine ⟨(F₀.trans (modelAffineDiffeomorph A₀ A₁ ε₀ ε₁ hε₀' hε₁' (φ₀ 0) (φ₁ 0))).trans
    F₁.symm, ?_⟩
  intro x hx
  have key : modelAffineDiffeomorph A₀ A₁ ε₀ ε₁ hε₀' hε₁' (φ₀ 0) (φ₁ 0) (F₀ (φ₀ x)) =
      F₁ (φ₁ x) := by
    rw [modelAffineDiffeomorph_apply, hF₀ x hx, hF₁ x hx]
    have h1 : (ε₀ • A₀ x + φ₀ 0) - φ₀ 0 = ε₀ • A₀ x := by abel
    rw [h1]
    simp only [ContinuousLinearEquiv.map_smul, A₀.symm_apply_apply, smul_smul,
      inv_mul_cancel₀ hε₀', one_smul]
  simp only [Diffeomorph.coe_trans, Function.comp_apply]
  rw [key, F₁.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_closedBall_of_partialDiffeomorphs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_closedBall_of_partialDiffeomorphs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_closedBall_of_partialDiffeomorphs ``Submission.DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_closedBall_of_partialDiffeomorphs

abbrev ballChartModel : Type := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.ballChartModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.ballChartModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.ballChartModel ``Submission.DifferentialGeometry.Topology.Manifold.ballChartModel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ballChartModel M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace ballChartModel M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace ballChartModel M'']

def BallChartTransport (c : BallChart 3 (𝓡 3) M) (c' : BallChart 3 (𝓡 3) M') : Prop :=
  ∃ Φ : Diffeomorph (𝓡 3) (𝓡 3) M M' ∞,
    ∀ x ∈ Metric.closedBall (0 : ballChartModel) 2, Φ (c.chart x) = c'.chart x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.BallChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.BallChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.BallChartTransport ``Submission.DifferentialGeometry.Topology.Manifold.BallChartTransport

theorem BallChartTransport.refl (c : BallChart 3 (𝓡 3) M) : BallChartTransport c c :=
  ⟨Diffeomorph.refl (𝓡 3) M ∞, fun _ _ => rfl⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.Manifold.BallChartTransport
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.BallChartTransport.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.BallChartTransport.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.BallChartTransport.refl ``Submission.DifferentialGeometry.Topology.Manifold.BallChartTransport.refl

theorem BallChartTransport.symm {c : BallChart 3 (𝓡 3) M} {c' : BallChart 3 (𝓡 3) M'}
    (h : BallChartTransport c c') : BallChartTransport c' c := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨Φ.symm, fun x hx => by rw [← hΦ x hx, Diffeomorph.symm_apply_apply]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.BallChartTransport.symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.BallChartTransport.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.BallChartTransport.symm ``Submission.DifferentialGeometry.Topology.Manifold.BallChartTransport.symm

theorem BallChartTransport.trans {c : BallChart 3 (𝓡 3) M} {c' : BallChart 3 (𝓡 3) M'}
    {c'' : BallChart 3 (𝓡 3) M''} (h : BallChartTransport c c') (h' : BallChartTransport c' c'') :
    BallChartTransport c c'' := by
  obtain ⟨Φ, hΦ⟩ := h
  obtain ⟨Ψ, hΨ⟩ := h'
  exact ⟨Φ.trans Ψ, fun x hx => by
    simp only [Diffeomorph.coe_trans, Function.comp_apply, hΦ x hx, hΨ x hx]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.BallChartTransport.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.BallChartTransport.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.BallChartTransport.trans ``Submission.DifferentialGeometry.Topology.Manifold.BallChartTransport.trans

def BallChartIsotopic (c c' : BallChart 3 (𝓡 3) M) : Prop :=
  ∃ J : ℝ → Diffeomorph (𝓡 3) (𝓡 3) M M ∞,
    ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M => J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M => (J q.1).symm q.2) ∧
      J 0 = Diffeomorph.refl (𝓡 3) M ∞ ∧
      ∀ x ∈ Metric.closedBall (0 : ballChartModel) 2, J 1 (c.chart x) = c'.chart x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.BallChartIsotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.BallChartIsotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.BallChartIsotopic ``Submission.DifferentialGeometry.Topology.Manifold.BallChartIsotopic

theorem BallChartIsotopic.toTransport {c c' : BallChart 3 (𝓡 3) M}
    (h : BallChartIsotopic c c') : BallChartTransport c c' := by
  obtain ⟨J, -, -, -, hJ⟩ := h
  exact ⟨J 1, hJ⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.Manifold.BallChartIsotopic
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.BallChartIsotopic.toTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.BallChartIsotopic.toTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.BallChartIsotopic.toTransport ``Submission.DifferentialGeometry.Topology.Manifold.BallChartIsotopic.toTransport

theorem BallChartIsotopic.refl (c : BallChart 3 (𝓡 3) M) : BallChartIsotopic c c := by
  exact ⟨fun _ => Diffeomorph.refl (𝓡 3) M ∞, contMDiff_snd, contMDiff_snd, rfl,
    fun _ _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.BallChartIsotopic.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.BallChartIsotopic.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.BallChartIsotopic.refl ``Submission.DifferentialGeometry.Topology.Manifold.BallChartIsotopic.refl

theorem BallChartIsotopic.trans {c c' c'' : BallChart 3 (𝓡 3) M} (h : BallChartIsotopic c c')
    (h' : BallChartIsotopic c' c'') : BallChartIsotopic c c'' := by
  obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ := h
  obtain ⟨K, hK, hKi, hK0, hK1⟩ := h'
  refine ⟨fun t => (J t).trans (K t), ?_, ?_, ?_, ?_⟩
  · exact hK.comp (contMDiff_fst.prodMk hJ)
  · exact hJi.comp (contMDiff_fst.prodMk hKi)
  · change (J 0).trans (K 0) = Diffeomorph.refl (𝓡 3) M ∞
    rw [hJ0, hK0, Diffeomorph.refl_trans]
  · intro x hx
    simp only [Diffeomorph.coe_trans, Function.comp_apply, hJ1 x hx, hK1 x hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.BallChartIsotopic.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.BallChartIsotopic.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.BallChartIsotopic.trans ``Submission.DifferentialGeometry.Topology.Manifold.BallChartIsotopic.trans

theorem BallChartIsotopic.symm {c c' : BallChart 3 (𝓡 3) M} (h : BallChartIsotopic c c') :
    BallChartIsotopic c' c := by
  obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ := h
  refine ⟨fun t => (J t).symm, hJi, ?_, ?_, ?_⟩
  · exact hJ
  · change (J 0).symm = Diffeomorph.refl (𝓡 3) M ∞
    rw [hJ0, Diffeomorph.symm_refl]
  · intro x hx
    rw [← hJ1 x hx]
    exact (J 1).symm_apply_apply (c.chart x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.BallChartIsotopic.symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.BallChartIsotopic.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.BallChartIsotopic.symm ``Submission.DifferentialGeometry.Topology.Manifold.BallChartIsotopic.symm


omit [FiniteDimensional ℝ E] in
private theorem extendChartById_chartSymm
    (φ : PartialDiffeomorph 𝓘(ℝ, ballChartModel) (𝓡 3) ballChartModel M ∞)
    (f : ballChartModel → ballChartModel) {y : M} (hy : y ∈ φ.target) :
    extendChartById φ.symm.toOpenPartialHomeomorph f y = φ (f (φ.symm y)) := by
  rw [extendChartById]
  have hsrc : y ∈ φ.symm.toOpenPartialHomeomorph.source := hy
  rw [if_pos hsrc]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.extendChartById_chartSymm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.extendChartById_chartSymm target :: scope.openDecls } }

variable [T2Space M]

theorem ballChartTransport_of_modelDiffeomorph (c c' : BallChart 3 (𝓡 3) M)
    (D : Diffeomorph 𝓘(ℝ, ballChartModel) 𝓘(ℝ, ballChartModel) ballChartModel
      ballChartModel ∞)
    {K : Set ballChartModel} (hK : IsCompact K) (hKt : K ⊆ c'.chart.source)
    (hfix : ∀ z, z ∉ K → D z = z ∧ D.symm z = z)
    (hover : ∀ x ∈ Metric.closedBall (0 : ballChartModel) 2, c.chart x ∈ c'.chart.target)
    (hact : ∀ x ∈ Metric.closedBall (0 : ballChartModel) 2, D (c'.chart.symm (c.chart x)) = x) :
    BallChartTransport c c' := by
  obtain ⟨J, -, -, hJe, -, -, -⟩ :=
    exists_diffeomorph_extension_of_partial_chart_family
      (P := Unit) c'.chart.symm.toOpenPartialHomeomorph
      c'.chart.contMDiffOn_invFun c'.chart.contMDiffOn_toFun
      (fun _ : Unit => D)
      (D.contDiff.comp contDiff_snd) ((D.symm).contDiff.comp contDiff_snd)
      hK hKt (fun _ z hz => hfix z hz)
  refine ⟨J (), fun x hx => ?_⟩
  rw [(hJe () (c.chart x)).1, extendChartById_chartSymm c'.chart D (hover x hx), hact x hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.ballChartTransport_of_modelDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.ballChartTransport_of_modelDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.ballChartTransport_of_modelDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.ballChartTransport_of_modelDiffeomorph

def LocalizedModelTransportInput (c c' : BallChart 3 (𝓡 3) M) : Prop :=
  (∀ x ∈ Metric.closedBall (0 : ballChartModel) 2, c.chart x ∈ c'.chart.target) ∧
    ∃ (D : Diffeomorph 𝓘(ℝ, ballChartModel) 𝓘(ℝ, ballChartModel) ballChartModel
        ballChartModel ∞) (K : Set ballChartModel),
      IsCompact K ∧ K ⊆ c'.chart.source ∧
        (∀ z, z ∉ K → D z = z ∧ D.symm z = z) ∧
        ∀ x ∈ Metric.closedBall (0 : ballChartModel) 2, D (c'.chart.symm (c.chart x)) = x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.LocalizedModelTransportInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.LocalizedModelTransportInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.LocalizedModelTransportInput ``Submission.DifferentialGeometry.Topology.Manifold.LocalizedModelTransportInput

theorem ballChartTransport_of_localizedModelTransportInput {c c' : BallChart 3 (𝓡 3) M}
    (h : LocalizedModelTransportInput c c') : BallChartTransport c c' := by
  obtain ⟨hover, D, K, hK, hKt, hfix, hact⟩ := h
  exact ballChartTransport_of_modelDiffeomorph c c' D hK hKt hfix hover hact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.ballChartTransport_of_localizedModelTransportInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.ballChartTransport_of_localizedModelTransportInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.ballChartTransport_of_localizedModelTransportInput ``Submission.DifferentialGeometry.Topology.Manifold.ballChartTransport_of_localizedModelTransportInput

end DifferentialGeometry.Topology.Manifold
namespace DifferentialGeometry.Topology

universe u v u' v'

theorem nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport
    {M : ConnectedClosedOrientedManifold.{u} 3} {M' : ConnectedClosedOrientedManifold.{u'} 3}
    {N : ConnectedClosedOrientedManifold.{v} 3} {N' : ConnectedClosedOrientedManifold.{v'} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (c' : OrientedBallChart M'.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold)
    (d' : OrientedBallChart N'.toClosedOrientedManifold)
    (a : BoundaryAttachment)
    (hΦ : Manifold.BallChartTransport c.toBallChart c'.toBallChart)
    (hΨ : Manifold.BallChartTransport d.toBallChart d'.toBallChart) :
    letI := ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    letI := ConnectedSumQuotient.csChartedSpace c'.toBallChart d'.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c'.toBallChart d'.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    Nonempty (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ₘ⟮𝓡 3, 𝓡 3⟯
      ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) := by
  obtain ⟨Φd, hΦd⟩ := hΦ
  obtain ⟨Ψd, hΨd⟩ := hΨ
  exact csTransportDiffeomorph c c' d d' a Φd Ψd
    (fun x hx => by simpa only [Diffeomorph.coe_toHomeomorph] using hΦd x hx)
    (fun x hx => by simpa only [Diffeomorph.coe_toHomeomorph] using hΨd x hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport ``Submission.DifferentialGeometry.Topology.nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport

end DifferentialGeometry.Topology


namespace DifferentialGeometry.Topology

universe u v w

def OrientedBallChartTransport {M : ConnectedClosedOrientedManifold.{u} 3}
    {M' : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (c' : OrientedBallChart M'.toClosedOrientedManifold) : Prop :=
  ∃ Φ : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier,
    Φ.preservesOrientation M.orientation M'.orientation ∧
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        Φ (c.toBallChart.chart x) = c'.toBallChart.chart x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChartTransport ``Submission.DifferentialGeometry.Topology.OrientedBallChartTransport

theorem OrientedBallChartTransport.refl
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold) :
    OrientedBallChartTransport c c :=
  ⟨Diffeomorph.refl (𝓡 3) M.Carrier ∞, Diffeomorph.preservesOrientation_refl M.orientation,
    fun _ _ => rfl⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.OrientedBallChartTransport
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChartTransport.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChartTransport.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChartTransport.refl ``Submission.DifferentialGeometry.Topology.OrientedBallChartTransport.refl

theorem OrientedBallChartTransport.symm
    {M : ConnectedClosedOrientedManifold.{u} 3} {M' : ConnectedClosedOrientedManifold.{v} 3}
    {c : OrientedBallChart M.toClosedOrientedManifold}
    {c' : OrientedBallChart M'.toClosedOrientedManifold}
    (h : OrientedBallChartTransport c c') : OrientedBallChartTransport c' c := by
  obtain ⟨Φ, hΦo, hΦ⟩ := h
  exact ⟨Φ.symm, Diffeomorph.preservesOrientation_symm hΦo, fun x hx => by
    rw [← hΦ x hx, Diffeomorph.symm_apply_apply]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChartTransport.symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChartTransport.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChartTransport.symm ``Submission.DifferentialGeometry.Topology.OrientedBallChartTransport.symm

theorem OrientedBallChartTransport.trans
    {M : ConnectedClosedOrientedManifold.{u} 3} {M' : ConnectedClosedOrientedManifold.{v} 3}
    {M'' : ConnectedClosedOrientedManifold.{w} 3}
    {c : OrientedBallChart M.toClosedOrientedManifold}
    {c' : OrientedBallChart M'.toClosedOrientedManifold}
    {c'' : OrientedBallChart M''.toClosedOrientedManifold}
    (h : OrientedBallChartTransport c c') (h' : OrientedBallChartTransport c' c'') :
    OrientedBallChartTransport c c'' := by
  obtain ⟨Φ, hΦo, hΦ⟩ := h
  obtain ⟨Ψ, hΨo, hΨ⟩ := h'
  exact ⟨Φ.trans Ψ, Diffeomorph.preservesOrientation_trans hΦo hΨo, fun x hx => by
    simp only [Diffeomorph.coe_trans, Function.comp_apply, hΦ x hx, hΨ x hx]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChartTransport.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChartTransport.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChartTransport.trans ``Submission.DifferentialGeometry.Topology.OrientedBallChartTransport.trans

theorem OrientedBallChartTransport.toBallChartTransport
    {M : ConnectedClosedOrientedManifold.{u} 3} {M' : ConnectedClosedOrientedManifold.{v} 3}
    {c : OrientedBallChart M.toClosedOrientedManifold}
    {c' : OrientedBallChart M'.toClosedOrientedManifold}
    (h : OrientedBallChartTransport c c') :
    Manifold.BallChartTransport c.toBallChart c'.toBallChart := by
  obtain ⟨Φ, -, hΦ⟩ := h
  exact ⟨Φ, hΦ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChartTransport.toBallChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChartTransport.toBallChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChartTransport.toBallChartTransport ``Submission.DifferentialGeometry.Topology.OrientedBallChartTransport.toBallChartTransport

theorem nonempty_connectedSumQuotient_diffeomorph_of_orientedBallChartTransport
    {M : ConnectedClosedOrientedManifold.{u} 3} {M' : ConnectedClosedOrientedManifold.{v} 3}
    {N : ConnectedClosedOrientedManifold.{u} 3} {N' : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (c' : OrientedBallChart M'.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold)
    (d' : OrientedBallChart N'.toClosedOrientedManifold)
    (a : BoundaryAttachment)
    (hΦ : OrientedBallChartTransport c c') (hΨ : OrientedBallChartTransport d d') :
    letI := ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    letI := ConnectedSumQuotient.csChartedSpace c'.toBallChart d'.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c'.toBallChart d'.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    Nonempty (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ₘ⟮𝓡 3, 𝓡 3⟯
      ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) :=
  nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport c c' d d' a
    hΦ.toBallChartTransport hΨ.toBallChartTransport

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_connectedSumQuotient_diffeomorph_of_orientedBallChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_connectedSumQuotient_diffeomorph_of_orientedBallChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_connectedSumQuotient_diffeomorph_of_orientedBallChartTransport ``Submission.DifferentialGeometry.Topology.nonempty_connectedSumQuotient_diffeomorph_of_orientedBallChartTransport

end DifferentialGeometry.Topology
namespace DifferentialGeometry.Topology

universe u v

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M']

def BallChart.pullback (c' : BallChart 3 (𝓡 3) M')
    (Φ : Diffeomorph (𝓡 3) (𝓡 3) M M' ∞) : BallChart 3 (𝓡 3) M where
  chart := c'.chart.trans (Diffeomorph.toPartialDiffeomorph Φ.symm)
  closedBall_subset_source := by
    intro x hx
    change x ∈ (c'.chart.toOpenPartialHomeomorph.trans
      (Diffeomorph.toPartialDiffeomorph Φ.symm).toOpenPartialHomeomorph).source
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨c'.closedBall_subset_source hx, Set.mem_univ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.pullback ``Submission.DifferentialGeometry.Topology.BallChart.pullback

theorem BallChart.pullback_apply (c' : BallChart 3 (𝓡 3) M')
    (Φ : Diffeomorph (𝓡 3) (𝓡 3) M M' ∞) (x : EuclideanSpace ℝ (Fin 3)) :
    (BallChart.pullback c' Φ).chart x = Φ.symm (c'.chart x) := by
  change (c'.chart.toOpenPartialHomeomorph.trans
    (Diffeomorph.toPartialDiffeomorph Φ.symm).toOpenPartialHomeomorph) x = _
  rw [OpenPartialHomeomorph.trans_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.pullback_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.pullback_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.pullback_apply ``Submission.DifferentialGeometry.Topology.BallChart.pullback_apply

theorem BallChart.map_pullback (c' : BallChart 3 (𝓡 3) M')
    (Φ : Diffeomorph (𝓡 3) (𝓡 3) M M' ∞) (x : EuclideanSpace ℝ (Fin 3)) :
    Φ ((BallChart.pullback c' Φ).chart x) = c'.chart x := by
  rw [BallChart.pullback_apply, Diffeomorph.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.map_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.map_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.map_pullback ``Submission.DifferentialGeometry.Topology.BallChart.map_pullback

theorem exists_ballChart_pullback (c' : BallChart 3 (𝓡 3) M')
    (Φ : Diffeomorph (𝓡 3) (𝓡 3) M M' ∞) :
    ∃ c : BallChart 3 (𝓡 3) M,
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        Φ (c.chart x) = c'.chart x :=
  ⟨BallChart.pullback c' Φ, fun x _ => BallChart.map_pullback c' Φ x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_ballChart_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_ballChart_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_ballChart_pullback ``Submission.DifferentialGeometry.Topology.exists_ballChart_pullback

theorem exists_orientedBallChart_pullback {M : ConnectedClosedOrientedManifold.{u} 3}
    {M' : ConnectedClosedOrientedManifold.{v} 3}
    (c' : OrientedBallChart M'.toClosedOrientedManifold)
    (Φ : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier) :
    ∃ c : BallChart 3 (𝓡 3) M.Carrier,
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        Φ (c.chart x) = c'.toBallChart.chart x :=
  exists_ballChart_pullback c'.toBallChart Φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_orientedBallChart_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_orientedBallChart_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_orientedBallChart_pullback ``Submission.DifferentialGeometry.Topology.exists_orientedBallChart_pullback

end DifferentialGeometry.Topology
