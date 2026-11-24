import YM.QCD.Smoke.Shore

/-! # exposed width before path growth, same width after. Actual shells. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Lattice Wilson Finset Filter Function Metric Extra Iteration RG Placement Laurent Exterior Work.F08 Precision Bloch Matrix Tree Bid
open scoped Matrix BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {L n c f:Side}{I:Type*}{P Q:Bed}{η Ω Θ σ C v u A:ℝ}{G:Gauge}{s:ℕ}{S:StepData c f}{T:Towers S.patch.L}

abbrev installG (E:I→PairG G)[Countable I]: ℕ→Atom G 2:=padded (assembleP E)
structure DemandG (S:StepData c f)(p:Clip)(P Q:Bed)(T:Towers S.patch.L)(η Ω Θ:ℝ)(s:ℕ)(G:Gauge) where
 early : 1 ≤ s
 high : P.dual_diag.strip η Ω
 low : Q.diagonal.strip η Θ
 deep : T.Deep η Ω s
 tide : Harmonic T
 vows :Sworn P f G
 proofZ : ∃ u A:ℝ,0 < u ∧ Precision.Floor P p f u A
 trial : Towers.Diagonal S P Q T
 branch : S.patch.Branches S.kernel G

lemma transferReceipt (E:I→PairG G)(hs:0<η)(h:0<σ)(ht:σ≤η/2)(hh:Palisade E σ C){p:Clip}(d:DemandG S p P Q T η Ω Θ s G) [Countable I] :
    let V:= shootG (psi P Q T) E
    Palisade V σ (cashRegister 2 η (psiPrice Ω Θ) / (S.patch.L.val:ℝ)^2 * C) ∧ ∀ (H:Forest S.ratio)(ρ:Dir G c→AxisChart G H) (W:PathData G), Critical H p W (S:=S) ρ → Guessed H (installed S.ratio T.A0) (S:=S) ρ → ∀ j ≤ 2, SameJet j (fun x=> Iteration.action (installG E) (liftedTo H ρ x)) (fun x=> Iteration.action (installG V) (represent x)) :=by
  intro V; have hu : 0≤psiPrice Ω Θ:=by
    let x:PlaqAxes:=Classical.arbitrary _; have hA:=Cost.nonneg (d.high (plaquette x) (plaquette x)); have hB:=Cost.nonneg (d.low (plaquette x) (plaquette x)); unfold psiPrice; positivity
  have hv (v:Axis) :(psi P Q T (some v)).strip η (psiPrice Ω Θ / (S.patch.L.val:ℝ)^3):=psi_strip hs d.high d.low d.early d.deep (some v)
  have hp := shucks E hu hs h.le ht hv hh
  refine ⟨hp, fun F u W he hw => transmit u h h (padded_cost (assembled h.le hh.2.2)) (padded_cost (assembled h.le hp.2.2)) he hw (fun x w=>?_)⟩
  obtain ⟨U,M,hM,hV⟩:=d.proofZ
  have hR:=Inherited.supports (G:=G) (H:=F) d.early hs d.high d.low d.deep hM d.branch hV d.vows d.trial x w
  rw [installG,installG,total_padded (assembled h.le hp.2.2) h.le,total_padded (assembled h.le hh.2.2) h.le,assemble_at hh.2.2 h.le,assemble_at hp.2.2 h.le]
  exact (shoot_real hu hs h.le ht hv hh hR (psi_cancels hs d.high d.low d.early d.deep S.patch.odd_side d.tide)).symm
end YM.QCD.Smoke
