import YM.Cape.Mem
import YM.Mills.Pearls
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
lemma glowMap (i:J) (V:Grid c): Reel.mist Φ! t i V = capstone K w (Reel.mist E t i V):=by
   unfold Reel.mist; by_cases he:Healthy t (E.addr i).support V; rw [masked_eq _ _ _ _ (show Healthy t ((Φ!).addr i).support V from he),masked_eq _ _ _ _ he]; rfl
   rw [masked_ne _ _ _ _ he, masked_ne _ _ _ _ (show ¬Healthy t ((Φ!).addr i).support V from he),map_zero] -- direction
lemma scalesLake (hp: X.Pillar p E): X.Pillar p Φ!:=by
    refine ⟨hp.zU,hp.stamp,hp.tapes,?_⟩
    intro i j h; rcases hp.brim i j h with hv|hv; exact Or.inl hv; exact Or.inr (funext fun V=>by rw [glowMap,hv,Pi.zero_apply,map_zero])
lemma winds (i:R)(V:Grid c)(hp:Summable (fun j=> Reel.mist E t j V)): riseP Φ! X i V = capstone K w (riseP E X i V):=by
    let L:= (capstone K w).toLinearMap.toContinuousLinearMap; have hv:Summable (fun j:Gate X (.some i)=> Reel.mist E t j.val V):= hp.comp_injective Subtype.val_injective
    unfold riseP; change _= L _; rw [L.map_tsum hv]; exact tsum_congr fun j=>glowMap E w j.val V
lemma frond (hA:SC.Valve E p q v t n α s ξ)(w':J→ℝ)(hw:0≤w')(hp: ∀ i,1 ≤ ξ i)(he:∀ i,Reel.mist E t i≠0 → w' i ≤ ξ i): SC.Valve E p q v t n α s w':=by
    obtain ⟨f,hf,hV⟩:=hA.back
    let v' i:= if Reel.mist E t i=0 then 0 else f i; have h₀(i V): Tablet.credits v (Reel.mist E t i V)≤v' i:=by unfold v'; split; rename_i h; unfold Tablet.credits; rw [h,Pi.zero_apply,map_zero,Cove.load_zero]; exact hf _ _
    refine ⟨hA.book,v',h₀, Labels.raise_prices _ _ (fun i=>mul_nonneg (hw _) ((Creek.load_nn ..).trans (h₀ i 1))) hV ?_⟩
    intro i; have hh:= (Creek.load_nn ..).trans (hf i 1); unfold v'; split; rw [mul_zero]; exact mul_nonneg (zero_le_one.trans (hp _)) hh; next h=> exact mul_le_mul_of_nonneg_right (he _ h) hh
lemma paySmall (Y:Code c N) (P:BudgetPoint)(L:Side)(x:ℝ)(K₁:Flavor N)(z:ℂ)(h:Desk Y P K₁ L x α): (Y.EvalK z).Reg P.threshold ∧ ∀ i,Cove.shadeG ((Y.EvalK z).warp i):=by
   have hk:=closureK Y.top (fun i=>z^(Y.up i)) _ h.high
   refine ⟨Cart _ _ (paysReg _ h.base) (Cart _ _ (closureK _ (fun _=>z) _ h.low) hk),?_⟩
   rintro (i|i|i); exact (sym _ h.base).2.gauge i; exact shadeColor _ z (h.warm.tone i).gauge; exact shadeColor _ (z^(Y.up i)) (h.wish.tone i).gauge
include hp
variable [Finite R]
lemma momentumQ (v0:Grid c→EvenA c N) (V:Grid c)(h:∀ V,Summable (fun i=>Reel.mist E t i V))(hz: Reel.Book p q E)(hM:M.Reg t)(hf:F.Beat N p q t)(hv:0<v)(ht:Summable (Ruby.tK (torah p F M v) t V)) [Countable J]: relativeE N E F M v0 t V = relativeE N (unitR E X) (coverP p (lured E X) F M v t) M v0 t V:=by
    unfold relativeE; rw [gladdened p q (lured E X) F M (summerC p q E hz X hp h) hf hM hv V ht, reportOptions E X h V, ← add_assoc,exp_add,mul_right_comm]; ring
omit hp [Finite R]
-- Civic scheduling block. choose single theta for next width; DCHECK h0 unmarked.CAMP.F. include Quits budget generous enough. K₁ output stronger than 7/8; spare restoration. Slate uniform also allows later ℓ.3 soft.
variable (L:Side) (x:ℝ)
def leaseV (L:Side)(x:ℝ)(Z:ℝ)(E N n:ℕ):= let M:=n*radiusB (run L x); let R:ℕ:=((M+M+1)^4*E*N); (R:ℝ)*Real.exp (Z*((n+n+1)^4:ℕ))
local notation "sV"=> Stratum.MarchQ.Suburb.Melt.Lobby.ratioCostV
local notation "Bv"=> Stratum.MarchQ.Suburb.Melt.Lobby.budgetV
open QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby
local notation "j0"=> (3/32:ℝ)
local notation "ΓN"=> (7/64:ℝ)
-- renew using input charges already paid (scaled path picks qχ). allow extra K₁ desires.
structure FoilV (L:Side)(x θ w:ℝ)(E N K₁:ℕ)(S:ℝ): Prop where
    tolls : ShelfY L θ x E
    spark : 0<w
    budget : w ≤ sV L x
    spread : 1 ≤ fan L θ x
    low : (w:ℝ)*leaseV L x j0 E N K₁+w ≤ Bv L x
    tax : 1 ≤ taxK L x 1
    lease : w* leaseV L x (ΓN+1) E N K₁ ≤ ash L x -- for log(1+w) bound same
    soft : ∀ (n:ℕ), n≤ highR L x →∀ (c:Side)(N:ℕ)(D Z I U:Type)[Fintype I] (p:I→ Site c) (q:I→Bool) (Y:Lure c N I Z)(F:Film c N I D) (M:Patron.Rail c N U)(t v:ℝ)(w:Z→ℝ),Y.On p q t→F.Beat N p q t→M.Reg t→0<v→0≤w→(∀ i V,Tablet.credits v (Y.wick i V) ≤ wig w i)→Ac.Hit Y.spot n w (ΓN+1) (ash L x)→ Quits (torah p F M v) n S (taxK L x 1) ΓN v → Film.Stock N (coverP p Y F M v t) n (taxK L x (31/32)) j0 v (taxK L x (1/64))⁻¹ (fun _=>1) -- Expenditure scaling ask INPUT exactly at tax1; paired margin if S.Met.Static. post alpha.Act
lemma quarry (θ:ℝ)(hθ:0<θ)(E N K₁:ℕ)(S:ℝ)(hS:0<S):∀ᶠ x:ℝ in atTop, FoilV L x θ (sV L x) E N K₁ S:=by
    let s:=sV; let M x:= K₁*radiusB (run L x); let D x:=((M x+M x+1)^4*E*N:ℕ)
    -- degreeC.Is: transfer via sale at running clock. avoid after through exact Seat x expansion. radiusB(βF) cost same Nap.Kite.h.
    have hr: Seat L 0 (fun x=> (D x:ℝ)):=by
       have h: Seat L 0 (fun x=> (highR L x:ℝ)):=by -- inspect
          intro b hb; filter_upwards [Delay.monitor_pays su L 1 (D:=1) zero_le_one hb] with x hx; refine le_trans ?_ hx; unfold highR radiusB Delay.bill; rw [abs_of_nonneg (by positivity),one_mul,pow_one]; have h := Nat.ceil_lt_add_one (sq_nonneg (Real.log (betaF su x L))); linarith only [h,Nat.cast_nonneg (α:=ℝ) (Nat.ceil (Real.log x ^2))]
       have hm :Seat L 0 (fun x=>(M x:ℝ)):=by unfold M; push_cast; exact h.timesL _
       unfold D; push_cast; exact ((hm.comb hm|>.comb (Seat.numbers 1)).powered 4|>.times E|>.times N).above (by linarith)
    have hk (r): Seat L 0 (fun x=> leaseV L x r E N K₁):= hr.times _
    have hg: Seat L (-4) (sV L):=by
        intro r h; filter_upwards [Finch.dim L (-4),(Seat.keeps (L:=L) (a:=-4)).timesL 2 r h] with x hx he; rw [abs_of_pos (show 0 < sV L x from fan_pos ..)]; exact hx.trans ((le_abs_self _).trans he) -- dim factor 2
    have hp:=hg.ponies (hk j0) |>.above (show (-(4:ℝ))+0≤ -4 by linarith) |>.comb hg |>.timesL 2
    have hv:∀ᶠ x in atTop, 1 ≤ fan L θ x:= ((Seat.your L).eventually_ge_atTop 1).mono fun i hi=> Real.one_le_rpow hi hθ.le
    filter_upwards [budgetsY L θ E,hv,teases L j0 (ΓN-j0)  (31/32) (1/64) 1 S (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hS,hp (-2) (by norm_num),(hg.ponies (hk (ΓN+1))) (1/8) (by norm_num)] with x h ht hz hx hK
    rw [show j0+(ΓN-j0) = ΓN by ring] at hz
    have hX' := (le_abs_self _).trans hx; have hG:Bv L x=fan L (-2) x/2:=rfl; refine ⟨h,fan_pos ..,le_refl _,ht,?_ ,Real.one_le_exp (mul_nonneg zero_le_one (fan_pos ..).le),?_,hz⟩
    · rw [hG]; linarith only [hX'] -- adjust
    exact (le_abs_self _).trans hK
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.quarry
