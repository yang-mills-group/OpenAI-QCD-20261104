import YM.Talis.Fork
import YM.Talis.Leech
import YM.Vest.Star
import YM.Bloom.Shrimp
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{hBP:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K hBP)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Stratum.MarchQ
open Rails
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
open Track Depot
namespace Talis
open MintV Suburb.Affair.Nimbus Counter
variable (L:Side)
local notation "EV"=> measureV L
local notation "τ"=>distV L
local notation "Bp"=>run L
open YM.Bloom.TreeP YM.Arise QCD.Bloom.Buzz QCD.Bank
variable (ν a δ H D:ℕ)
open Vest QCD.Bera Next.Rank.Normal
local notation "w"=> EV ν
local notation "W!"=> WTop L ν H
local notation "Ω"=> cutOffV L
local notation "Φ"=> freshS L 5
local notation "U!"=> (ν+1)
-- cardinal expense fields independent of actual volume. query EK from cutoff after L.
noncomputable def topC (x:ℝ) :ℕ:= Nat.ceil (measureV L 3 x)
noncomputable def BetaLeak (x:ℝ):= cutOffV L 1 x* measureV L ((ν+1)+2) x
-- margin factor: r' x=4*g. proof `gemmaV` through Canon.
lemma chopR {H t C₁:ℝ}(hp:0≤C₁)(hx:0≤ t)(he:0≤ η)(hr:0 ≤ H)(hv:k≤ i) :crop su H C₁ t η D k ≤crop su H C₁ t η D i:=by
    unfold YM.Bloom.TreeP.crop; dsimp only
    have hn:0 ≤ billN H D*(C₁*t*(fareV su 1 1 *4))+C₁*η:=by unfold billN fareV; positivity
    have hm: fareV su 1 (k+1) ≤ fareV su 1 (i+1):=by unfold fareV; exact Nat.cast_le.mpr (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _))
    exact add_le_add_right (mul_le_mul_of_nonneg_right hm hn) _
lemma cuffR {H t C:ℝ}(hp:0≤C)(hx:0≤ t)(he:0≤ η)(hr:0 ≤ H)(hv:k≤ i) :pocketV H C t η D k ≤pocketV H C t η D i:=by
    unfold pocketV; dsimp only
    have hh: 0≤billN H D*(C*t)+C*η:=by unfold billN; positivity
    have hk: audit k 6 ≤ audit i 6:=by unfold audit; exact Nat.cast_le.mpr (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) _))))
    exact add_le_add_right (mul_le_mul_of_nonneg_right hk hh) _
lemma cap_top : PageP L (fun x=>(topC L x:ℝ)) 3:=by
    refine (PageP.harm L (PageP.loan L 3) (PageP.just L 1 3)).takes L ?_; filter_upwards with x; rw [abs_of_nonneg (Nat.cast_nonneg ..)]
    exact (Nat.ceil_lt_add_one (χone L x 3|>.le)).le.trans (le_abs_self _)
variable (B:ℕ)(C C':ℝ)
local notation "Jx"=> fun x=> B*topC L x
local notation "G0!"=> fun x=> billN (W! x) D*(C*BetaLeak L ν x*(fareV su 1 1*4))
local notation "Sx"=> fun x=> billN (W! x) D*(C'*BetaLeak L ν x)
lemma fond : PageP L (fun x=> (B*topC L x:ℝ)) 3:=by
     exact PageP.timesL L (cap_top L) (B:ℝ)
lemma fundF :PageP L (fun x=> fareV su 1 (B*topC L x+1)) 3 :=by
    have hp:PageP L (fun x=> (↑(B*topC L x+1):ℝ)) 3:= by push_cast; exact (fond L B).harm L (PageP.just L 1 3)
    exact hp.careG L su 1
lemma fundE :PageP L (fun x=> audit (B*topC L x) 6) 3:=by
    have hp:PageP L (fun x=>(↑(B*topC L x):ℝ)) 3:= by push_cast; exact fond ..
    exact hp.careS L 6
lemma leakG : Rate su L (-1) (fun x=> billN (WTop L ν H x) D * (C*BetaLeak L ν x*(fareV su 1 1*4))) :=by
    have hP:= PageP.rate L (PageP.liftNat L ((PageP.loan L ν).liftNat L H) (4+2*D)); have ht:= Rate.power (G:=su) (L:=L) (a:=(-1:ℝ))
    exact ((Rate.mul hP (((Rate.mul ht (rateMeasure L ((ν+1)+2))).mul_left C).mul_right _)).weaken (by norm_num)) -- unwrap billN
lemma leakS : Rate su L (-1) (fun x=> billN (WTop L ν H x) D*(C'*BetaLeak L ν x)):=by
    have h:= PageP.rate L ((PageP.loan L ν|>.liftNat L H).liftNat L (4+2*D)); have hp:= Rate.power (G:=su) (L:=L) (a:=(-1:ℝ)); exact (Rate.mul h ((Rate.mul hp (rateMeasure L ((ν+1)+2))).mul_left C')|>.weaken (by norm_num))
-- AFTER-L tolls. aperture restore root.V. leech.E.S.Note leak hypotheses no need βmon.
variable (K:ℕ→ℝ) {q v b1 b2:ℕ}
local notation "Hk"=> PageP.just L
local notation "ℳ"=>EV a
local notation "Λ"=> EV q
lemma magicF (z:ℝ)(hp:0< Bp z): 2*gemmaV L z*freshS L 5 z=4*measureV L 5 z:=by unfold gemmaV freshS cutOffV; rw [Real.rpow_neg hp.le]; field_simp; all_goals ring -- syntax
lemma arcsA (hL:1<L.val)(hq:q<a)(hv:q<ν)(ht:5 ≤ q) :∀ᶠ x in atTop, let z:=topC L x; let t:=BetaLeak L ν x; let η:=(EV a x)⁻¹; let V:=(EV q x)⁻¹;
                 (2*gemmaV L x*freshS L 5 x*crop su (W! x) C t η D (B*z)≤V) ∧ (pocketV (W! x) C' t η D (B*z) ≤V) ∧ C / EV ν x + C*η^2 ≤ V ∧ C'/EV ν x+C'*η^2≤ V :=by
     let F:=fun x=> fareV su 1 (B*topC L x+1); let E:=fun x=>audit (B*topC L x) 6; let U:=fun x=> (4:ℝ)*EV 5 x; have hr:PageP L U q := PageP.timesL L (PageP.budget_lo L ht) 4
     have hF:=fundF L B|>.out L (by omega:3 ≤ q); have hE:= fundE L B|>.out L (by omega:3 ≤ q); have hW:= PageP.loan L q
     let Gv:=fun x=>billN (W! x) D * (C*BetaLeak L ν x*(fareV su 1 1*4)); let Sv:=fun x=> billN (W! x) D*(C'*BetaLeak L ν x)
     let O:= fun x=> Λ x
     have h₁: Rate su L (-1) (fun x=> Λ x* (U x *(Gv x + F x * Gv x))) :=by
            have hp:= leakG L ν H D C; exact (Rate.mul (rateMeasure L q) (Rate.mul (PageP.rate L hr) (Rate.add hp (Rate.weaken (Rate.mul (PageP.rate L hF) hp) (by norm_num)))) |>.weaken (by norm_num))
     have h₂: Rate su L (-1) (fun x=> Λ x*(Sv x+ E x*Sv x)):=by have hp:= leakS L ν H D C'; exact (Rate.mul (rateMeasure L q) (Rate.add hp (Rate.weaken (Rate.mul (PageP.rate L hE) hp) (by norm_num)))|>.weaken (by norm_num))
     have h₃: PageP L (fun x=> Λ x*(U x*(F x*C))) q:= hW.times L (hr.times L (hF.times L (PageP.just L C _)))
     have h₄: PageP L (fun x=> Λ x*(E x*C')) q:= hW.times L (hE.times L (Hk C' _))
     have h₅(A:ℝ):∀ᶠ x in atTop, A/EV ν x+A*((EV a x)⁻¹)^2 ≤ (Λ x)⁻¹:=by
            have hx:PageP L (fun x=> O x*A*((EV a x)⁻¹)) q:= (hW.times L (Hk A _)).times L (PageP.seed ..)
            filter_upwards [(hW.times L (Hk A _)).absorb L hL hv (1/2) (by norm_num),hx.absorb L hL hq (1/2) (by norm_num)] with x hx hy
            set Y:=Λ x; have ht:0<Y:=χone ..
            change Y * A / _ ≤ _ at hx; change Y*A*(EV a x)⁻¹/_ ≤ _ at hy; have hL':Y*(A/EV ν x+A*((EV a x)⁻¹)^2)≤1:=by rw [show Y*(A/EV ν x+A*((EV a x)⁻¹)^2)= Y * A/ EV ν x + Y*A*(EV a x)⁻¹/ EV a x from by ring]; linarith only [hx,hy]
            rw [inv_eq_one_div Y]; exact (le_div_iff₀ ht).mpr ((mul_comm _ Y).le.trans hL')
     filter_upwards [h₁.below (by norm_num) (1/2) (by norm_num),h₂.below (by norm_num) (1/2) (by norm_num),h₃.absorb L hL hq (1/2) (by norm_num),h₄.absorb L hL hq (1/2) (by norm_num),h₅ C,h₅ C',Delay.shift_pos su L] with x hx hy hu hs hC hC' he; intro z t η V
     have hp:0<Λ x:=χone ..
     refine ⟨?_,?_,hC,hC'⟩
     · rw [magicF L x he]; unfold V; rw [inv_eq_one_div]; apply (le_div_iff₀ hp).mpr -- V defin? inv=1/
       change U x * (Gv x+F x*(Gv x+C*η)) * Λ x ≤ 1
       rw [show U x * (Gv x+F x*(Gv x+C*η)) * Λ x = Λ x *(U x*(Gv x+ F x*Gv x))+ Λ x*(U x*(F x*C))/EV a x from by unfold η; ring]; exact le_trans (add_le_add ((le_abs_self _).trans hx) hu) (by norm_num)
     · unfold V; rw [inv_eq_one_div]; apply (le_div_iff₀ hp).mpr; change (Sv x+ E x*(Sv x+C'*η))*_≤_
       rw [show (Sv x+ E x*(Sv x+C'*η))*Λ x= Λ x*(Sv x+E x*Sv x)+Λ x*(E x*C')/EV a x from by unfold η; ring]; exact le_trans (add_le_add ((le_abs_self _).trans hy) hs) (by norm_num)
lemma arcsB (hL:1<L.val)(hd:5≤q)(hq:q<v):∀ᶠ x in atTop, let z:=topC L x; let t:=BetaLeak L ν x; let η:=EV q x; let V:=EV v x;
                 (2*gemmaV L x*freshS L 5 x*crop su (W! x) C t η D (B*z)≤V) ∧ (pocketV (W! x) C' t η D (B*z) ≤V) ∧ C / EV ν x + C*η^2 ≤ V ∧ C'/EV ν x+C'*η^2≤ V:=by
     let F:=fun x=> fareV su 1 (B*topC L x+1); let E:=fun x=>audit (B*topC L x) 6; let U:=fun x=> (4:ℝ)*EV 5 x; have hr:PageP L U q:= PageP.timesL L (PageP.budget_lo L hd) 4
     have hF:=fundF L B|>.out L (by omega:3 ≤ q); have hE:= fundE L B|>.out L (by omega:3 ≤ q); have hW:= PageP.loan L q
     let Gv:=fun x=>billN (W! x) D * (C*BetaLeak L ν x*(fareV su 1 1*4)); let Sv:=fun x=> billN (W! x) D*(C'*BetaLeak L ν x)
     have hG:PageP L Gv q:=(PageP.hush L (leakG L ν H D C) (by norm_num)).out L (Nat.zero_le _); have hS:PageP L Sv q:=(PageP.hush L (leakS L ν H D C') (by norm_num)).out L (Nat.zero_le _)
     have hp : PageP L (fun x=> U x * crop su (WTop L ν H x) C (BetaLeak L ν x) (measureV L q x) D (B*topC L x)) q:= hr.times L (hG.harm L (hF.times L (hG.harm L (hW.timesL L C))))
     have hx: PageP L (fun x=> pocketV (WTop L ν H x) C' (BetaLeak L ν x) (measureV L q x) D (B*topC L x)) q:= hS.harm L (hE.times L (hS.harm L (hW.timesL L C')))
     have hh (A:ℝ): PageP L (fun x=> A/ EV ν x + A*(Λ x)^2) q:=by simp_rw[div_eq_mul_inv]; exact (PageP.timesL L (PageP.seed ..) A).harm L ((hW.liftNat L 2).timesL L A)
     filter_upwards [hp.cheaper L hL hq,hx.cheaper L hL hq,(hh C).cheaper L hL hq,(hh C').cheaper L hL hq,Delay.shift_pos su L] with x hx hv hC hC' ht; intro Z Pu Ωg Un; rw[magicF L x ht]; exact ⟨hx,hv,hC,hC'⟩
end Talis
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.arcsA
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Talis.arcsB
