import YM.Cape.Fuel
/-!
# Switching poses and costs. Single-tile boosts recovered by choosing an asset ∀V.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cape
open ConnectedActivityE6 QCD Lattice Finset Wilson RG Pressure Function Filter MeasureTheory NormedSpace
open Sway OrbitG Ruby Kites Grass Lat Cove Push Push.AbsoluteSums Patron
open Cupola Ribbon Loom Loom.Fleet Plate Twist Stitch Creek SC FlareV
open QCD.Acre Rails Struck Struck.Library Carrier
open QCD.Jets.Touch
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}{I D Z U J R:Type} [Fintype I]
variable (p:I→Site c)(q:I→Bool) (F: Film c N I D)(M: Patron.Rail c N U) (E: Reel c N I J)
variable {t v α s h u κ a A b m:ℝ} (X:Lake (c:=c) (I:=I) (J:=J) R t)
local notation "K"=> Keys c N
local notation "Xk"=> Ribbon.Spine I
local notation "L₀"=> brightP E X
local notation "W"=> reelShot E X
local notation "Kᴿ"=> unitR E X
variable {ξ:J→ℝ}{u':R→ℝ} {n:ℕ} (hz:SC.Valve E p q v t n α s ξ)(hp:X.Pillar p E)
-- basic tactics upstream
variable (w:I→ℝ)
local notation "Φ!"=> volume_up E w
open QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby
local notation "j0"=> (3/32:ℝ)
local notation "ΓN"=> (7/64:ℝ)
variable (L:Side) (x θ r S:ℝ)(P:BudgetPoint)(l m0 C:ℕ)
variable (hY: FoilV L x θ r l m0 C S)
local notation "V'"=>fan L θ x
local notation "S₁"=>taxK L x 1
local notation "r₁"=>C*P.B
local notation "B'"=> P.B
local notation "Kid"=> ((r₁+r₁+1)^4*l*m0:ℕ)
local notation "A1"=> ((C+C+1)^4:ℕ)
-- Sector.F costs. callable doesn't specify valuation reprojection.
local notation "Φ+"=> volume_F F w
variable (φ: R→I)(htC:∀ i: R,(X.addr i).support⊆ halo (C*P.B) {p (φ i)})(he:∀ (i:I)(Y:Finset R),(∀ j∈Y,φ j=i)→ Y.card≤ m0)
include hp hY htC he
-- repriced lane either Arch.E counts.X as chosen.
local notation "Lc"=> lured Φ! X
local notation "Oc"=> unitR Φ! X
local notation "Kc"=> coverP p (lured Φ! X) Φ+ M V' t
variable [Finite R] [Countable J]
lemma warrants (hh:∀ i,|w i|≤r)(hA:∀ i,w i ≠0)(hB:P.B=highR L x) (hv:SC.Valve E p q V' t B' j0 1 ξ) (ht':∀ i,1≤ ξ i) (hc: F.Beat N p q t)(hV:F.Stock N B' S₁ ΓN V' A w) (hz:M.Reg t)(h':∀ i,Cove.shadeG (M.warp i))(hK:Quits M B' b S₁ ΓN V')(hf:b+A ≤ S)(hF:Fires p l) (G: Grid c→EvenA c N): SC.Valve (Oc) p q V' t B' j0 (budgetV L x) (Sum.elim (fun _=>1) (fun i=> ξ i.val)) ∧ Film.Beat N p q Kc t ∧ Film.Stock N Kc B' (taxK L x (31/32)) j0 V' (taxK L x (1/64))⁻¹ (fun _=>1) ∧ ∀ (V:Grid c), relativeE N Oc Kc M G t V= capstone K w (relativeE N E F M G t V):=by
    let T:= Kc; let M':= torah p Φ+ M V'; have hf':= filmBoost F q p w t hc hV
    have hV0 := hY.spread; have hτ:= hY.tax; have hv':= zero_lt_one.trans_le hV0
    have hq:= renews F q p w t hc; have hU:=unitedQ p q Φ+ M hq hv' hK hf'; have h1: 0≤r:= hY.spark.le; have hz':0≤ ξ:=fun i=>zero_le_one.trans (ht' i)
    have hj0:0≤j0:=by norm_num
    have hS(i): ‖give w (E.z i)‖≤ r:=by
         unfold give; rw [norm_prod]; exact (by
            refine (prod_le_prod (fun _ _=>norm_nonneg _) (g:=fun _=>r) (fun i _=>?_)).trans ?_
            · exact (Complex.norm_real (w _)|>.trans (Real.norm_eq_abs _)).trans_le (hh _)
            rw [prod_const]; exact pow_le_of_le_one h1 (hY.budget.trans hY.tolls.tiny) (card_pos.mpr (hv.book.stays i)|>.ne'))
    have hm : Valve Φ! p q V' t B' j0 r ξ:= mul_one r ▸ valBoost E q p w t ξ r h1 hz' hS hv; have hk:=scalesLake p E X w hp; have hs:= flyer p q Φ! hm hj0 ht' hV0
    have hq':∀ i,coverNumber P.B (X.addr i).support ≤ A1:=fun i=>(Corona.cover_mono (htC i) _).trans (Corona.tile (p (φ i)) C B' P.B_pos)
    have hW:=glebe p (fun i=>(X.addr i).support) φ htC hF he
    have h0:= towers p q Φ! X hm hk A1 Kid ht' hj0 hV0 hj0 hq' hW; have wg:∀ i,Tablet.credits V' (Reel.mist (brightP Φ! X) t i 1) ≤ r:=fun i=>h0.2.2.1 i 1
    let f: R→ℝ:= fun _=> Real.log (1+r); let A₀ (a:ℝ):= Kid*r*Real.exp (a*A1)
    have hW':Quits M' B' S S₁ ΓN V':= by obtain ⟨f,hk,ht⟩:=hU.cost; exact ⟨f,fun i=>budget_loosen (hk i) hf,ht⟩
    have hp':Lure.On p q Lc t:= summerC p q Φ! hm.book X hk hs
    have hl a:A₀ a=r*leaseV L x a l m0 C:=by unfold A₀ leaseV; dsimp only; rw [show P.B = radiusB (run L x) from hB]; ring -- highR defeq simp
    have ht := (receiptsR p q Φ! X hm hk ht' hj0 hV0 (u':=fun _=>r) (b:=A₀ j0) h0.2.2.1 h0.2.2.2.2.2) -- typo m Named b
    have hY' :0 ≤ Sum.elim (fun _ :R=> (1:ℝ)) (fun i: Gate X none => ξ i.val):=by rintro (i|i); exact zero_le_one; exact hz' _
    refine ⟨valve_quote _ hY' ht (?_) le_rfl, glowP p q Lc Φ+ M hp' hq hz h' hv', hY.soft B' hB.le c N _ _ _ _ p q Lc Φ+ M t V' f hp' hq hz hv' (fun _=>Real.log_nonneg (by linarith)) h0.2.2.2.1 (fun i=>?_ ) hW',fun V=>?_⟩
    · exact le_trans (add_le_add_left (hl j0).le r) hY.low -- arg orientation
    · apply budget_loosen ((towers p q Φ! X hm hk A1 Kid ht' hj0 hV0 (show 0 ≤ ΓN+1 by norm_num) hq' hW).2.2.2.2.1 i); refine le_trans ?_ ((hl _).le.trans hY.lease); unfold A₀; gcongr; exact (Real.log_le_sub_one_of_pos (by linarith)).trans_eq (by ring) -- maybe order
    exact (momentumQ p q Φ+ M Φ! X hk G V hs hm.book hz hq hv' (profits M' V hV0 hτ hW' (by norm_num) t)).symm.trans (cashInV E F V M w t hA G).symm
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.warrants
