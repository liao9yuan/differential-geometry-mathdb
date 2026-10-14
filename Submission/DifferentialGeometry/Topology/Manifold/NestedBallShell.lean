import Submission.DifferentialGeometry.Topology.Manifold.EmbeddedBallShell

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Manifold _root_.Module
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem transport_parametrization
    {G H P : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace P] [ChartedSpace H P]
    {I : ModelWithCorners ℝ G H}
    (e : PartialEquiv P E) (hes : e.source = _root_.Set.univ)
    (he : ContMDiff I 𝓘(ℝ, E) ∞ e) (hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hsub : e.target ⊆ φ.source) :
    ∃ d : PartialEquiv P E, d.source = _root_.Set.univ ∧ d.target = φ '' e.target ∧
      ContMDiff I 𝓘(ℝ, E) ∞ d ∧ ContMDiffOn 𝓘(ℝ, E) I ∞ d.symm d.target := by
  let d := e.trans φ.toPartialEquiv
  have hds : d.source = univ := by
    ext p
    constructor
    · exact fun _ ↦ _root_.Set.mem_univ _
    · intro _
      have hp : p ∈ e.source := hes ▸ _root_.Set.mem_univ p
      exact ⟨hp, hsub (e.map_source hp)⟩
  have hdt : d.target = φ '' e.target := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨φ.symm x, hy, φ.right_inv hx⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨φ.map_source (hsub hy), ?_⟩
      change φ.symm.toPartialEquiv (φ.toPartialEquiv y) ∈ e.target
      have hid : φ.symm.toPartialEquiv (φ.toPartialEquiv y) = y := φ.left_inv (hsub hy)
      exact hid.symm ▸ hy
  refine ⟨d, hds, hdt, ?_, ?_⟩
  · apply contMDiffOn_univ.mp
    exact φ.contMDiffOn_toFun.comp he.contMDiffOn
      (fun p _ ↦ hsub (e.map_source (hes ▸ _root_.Set.mem_univ p)))
  · exact hei.comp (φ.contMDiffOn_invFun.mono (fun _ hx ↦ hx.1)) (fun _ hx ↦ hx.2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.transport_parametrization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.transport_parametrization target :: scope.openDecls } }

theorem exists_smooth_nestedBallShell_parametrization
    {n : ℕ} [Fact (_root_.Module.finrank ℝ E = n + 1)]
    (outer inner : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {r R : ℝ} (hr : 0 < r)
    (houter : _root_.Metric.closedBall (0 : E) R ⊆ outer.source)
    (hinner : _root_.Metric.closedBall (0 : E) r ⊆ inner.source)
    (hnested : inner '' _root_.Metric.closedBall 0 r ⊆ outer '' _root_.Metric.ball 0 R)
    (v : _root_.Metric.sphere (0 : E) 1) :
    ∃ e : PartialEquiv (_root_.Metric.sphere (0 : E) 1 × unitInterval) E,
      e.source = _root_.Set.univ ∧ e.target = outer '' _root_.Metric.closedBall 0 R \ inner '' _root_.Metric.ball 0 r ∧
      ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ, E) ∞ e ∧
      ContMDiffOn 𝓘(ℝ, E) ((𝓡 n).prod (𝓡∂ 1)) ∞ e.symm e.target := by
  let ψ := inner.trans outer.symm
  have himem (x : E) (hx : x ∈ _root_.Metric.closedBall 0 r) : inner x ∈ outer.target := by
    obtain ⟨y, hy, heq⟩ := hnested ⟨x, hx, rfl⟩
    exact heq ▸ outer.map_source (houter (_root_.Metric.ball_subset_closedBall hy))
  have hψs : _root_.Metric.closedBall (0 : E) r ⊆ ψ.source := fun x hx ↦ ⟨hinner hx, himem x hx⟩
  have hψsub : ψ '' _root_.Metric.closedBall 0 r ⊆ _root_.Metric.ball 0 R := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, heq⟩ := hnested ⟨x, hx, rfl⟩
    change outer.symm.toPartialEquiv (inner.toPartialEquiv x) ∈ _root_.Metric.ball 0 R
    have hi : outer.symm.toPartialEquiv (inner.toPartialEquiv x) = z := by
      rw [← heq]
      exact outer.left_inv (houter (_root_.Metric.ball_subset_closedBall hz))
    exact hi.symm ▸ hz
  have hcancel (x : E) (hx : x ∈ _root_.Metric.closedBall 0 r) :
      outer.toPartialEquiv (ψ.toPartialEquiv x) = inner.toPartialEquiv x :=
    outer.right_inv (himem x hx)
  obtain ⟨e, hes, het, he, hei⟩ :=
    exists_smooth_embeddedBallShell_parametrization (n := n) ψ hr hψs hψsub v
  have hesub : e.target ⊆ outer.source := by
    rw [het]
    exact fun _ hx ↦ houter hx.1
  obtain ⟨d, hds, hdt, hd, hdi⟩ := transport_parametrization e hes he hei outer hesub
  refine ⟨d, hds, ?_, hd, hdi⟩
  rw [hdt, het]
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxn⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro ⟨z, hz, heq⟩
    apply hxn
    refine ⟨z, hz, ?_⟩
    apply outer.toPartialEquiv.injOn
      (_root_.Metric.ball_subset_closedBall (hψsub ⟨z, _root_.Metric.ball_subset_closedBall hz, rfl⟩) |> houter)
      (houter hx)
    exact (hcancel z (_root_.Metric.ball_subset_closedBall hz)).trans heq
  · rintro ⟨⟨x, hx, hxy⟩, hyn⟩
    refine ⟨x, ⟨hx, ?_⟩, hxy⟩
    rintro ⟨z, hz, hzx⟩
    apply hyn
    refine ⟨z, hz, ?_⟩
    exact (hcancel z (_root_.Metric.ball_subset_closedBall hz)).symm.trans
      ((congrArg outer.toPartialEquiv hzx).trans hxy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_smooth_nestedBallShell_parametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_smooth_nestedBallShell_parametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_smooth_nestedBallShell_parametrization ``Submission.DifferentialGeometry.Topology.Manifold.exists_smooth_nestedBallShell_parametrization

end DifferentialGeometry.Topology.Manifold
