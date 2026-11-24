import YM.QCD.Hearth.Edges
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
namespace Project
open Revolve Flume Quarry
open Entr Port AnalyticBridge.VerifiedReset
open Entr Port AnalyticBridge.VerifiedReset
variable {o x:Site c}{t u δ ε K A B v' α θ:ℝ}{p:BudgetPoint}{I:Type}
variable {a:ℝ}
variable (b:Flavor N)
open Lunar
variable {L:Side}{T g:ℝ→ℝ}
open Hearth Pressure ConnectedActivityE6
lemma passB (j:Bool)(h:Rate su L t (fun x=> (T x)⁻¹))(he: Rate su L u g):∀ᶠ x in atTop,∀ (c:Side)(p:BudgetPoint), 0<T x→ p.B=radiusB (betaF su x L)→vizR (betaF su x L)≤ c.val→∀ (I:Type)(E:Gem c N I), Licence p 2 (g x) (T x) E→ Crossing E→ Quanta E b →|unitF j c (meter b (Patron.total E p.threshold 1))| ≤ Φ p.B (-7/4) c:=by
     filter_upwards [axesPanel b j (θ:=2) (by norm_num) L he h] with x hx c B ha hp hK I X hL hE hQ; have hp':=hx c B (t:=T x) hp hK rfl ha I X hL hE; rw [silence hQ, map_zero,sub_zero,show -(2-1/4:ℝ)= -7/4 from (by ring)] at hp'; exact hp'
include b
lemma organK (hu:1 < θ)(h:Rate su L t (fun x=> (T x)⁻¹))(he: Rate su L u T)(x:ℝ):∃ W:ℝ,∀ᶠ y in atTop,∀ (c:Side)(p:BudgetPoint), p.B=radiusB (betaF su y L)→0<T y→vizR (betaF su y L)≤ c.val →∀ (I:Type)[Fintype I] (E: Gem c N I)(U:St c),SlotT E p (T y) θ x U →1/4 ≤ Project.unitF true c (U 1) ∧|Project.unitF false c (U 1)| ≤ W:=by
     let s:= θ-1/4; have hh:0<s:=by unfold s; linarith
     obtain ⟨K,hK,H⟩:=Entr.hauteur N
     have hv:=(he.pow 2).mul_left x; refine ⟨K*|x|+1,?_⟩; filter_upwards [axesPanel b true hu L hv h,axesPanel b false hu L hv h, wonderful (Rate.const (L:=L) (G:=su) 1) s (1/4) 0 hh (by norm_num)] with y h1 h2 h c p ha hp hK I hI E U hL
     have h :Φ p.B (-s) c ≤1/4:=by rw [ha]; simpa only [pow_zero,mul_one,abs_one] using! h c hK
     have hX : meter b (Patron.total E p.threshold 1)=U 1:=by
          unfold Patron.total; rw [tsum_fintype,sum_congr rfl (show ∀ i∈univ, letters E p.threshold 1 i=(fun i=> E.view i 1) i from fun i _=>masked_eq _ _ _ _ (flat_ok ..))]; rw [hL.trunk]; exact forceP (U 1) b
     obtain hp' := h1 c p ha hK rfl hp I E hL.warp.law hL.moveG; rw [hX,show valueB true (till E b 0)=qWave (till E b 0) from awake ..] at hp'; let z':= qMass (till E b 0)
     have hv := hL.earn b; have ht:= h2 c p ha hK rfl hp I E hL.warp.law hL.moveG; rw [hX,show valueB false (till E b 0)= z' from rfl] at ht
     have hz':|z'| ≤ K*|x|:=by apply le_of_mul_le_mul_left _ (sq_pos_of_pos hp); apply (H c I E p θ (x*(T y)^2) _ hL.warp.law hp (by linarith) b).1.trans; rw [mul_left_comm ((T y)^2), mul_comm ((T y)^2)]; gcongr; exact le_abs_self _ -- hp
     refine ⟨by linarith only [hv,(abs_le.mp (hp'.trans h)).1], le_trans (show |unitF false c (U 1)|= _ from (show _ = _ from ?_ )).le ((abs_add_le (unitF false c (U 1)-z') z').trans (by linarith only [ht.trans h,hz']))⟩
     rw [sub_add_cancel]
end Project
end YM.QCD.Stew
#print axioms YM.QCD.Stew.Project.orient
