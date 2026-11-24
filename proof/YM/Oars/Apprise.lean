import YM.Oars.Treads
import YM.Oars.Orders
import YM.Oars.Comfort
import YM.Parishes.BudgetH
/-!
 # Support budget desks.Fuel.K requirement
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
open Stags QCD.Kites Acre Acre.Rails
variable {c:Side}{a H C V W v x y:ℝ}{J E I K:Type}[Fintype I] {Pt:BudgetPoint} {i m k:ℕ}
variable (p:I→Site c)(q:I→Bool)(F: Reel c 6 I E)(hf:E→ℝ)
variable (L:Side)(T: Teller su) -- pre lens extras
namespace Sail
-- constant thresholds for evolution.Truth.Hv supply parameters selected per path by Calls.A.AP.
-- use exponent .αOutput~3/16 before Tkv.Accord.spare.K from To.M.Roots.Rollen
-- choosing δ reduces to v' ; K stack needs exponent =v₂+ 2epsilon +1 . αL >1... use:
--   pre tip seed v0=48/256 . Tκ after rebase to 46/256, tax3.
--   stack input =**46/256**, output 42/256. nutrients v₁=46/256+1. F powers.Moter access αL=48/256+1; Hike.loan → after threshold t'.
--   publication to Film price η0=40/256 cost *ζ* (4 step decoal). Next Persona X' funded v at **μ0=32/256**. Ficus & Axis.Pay.Mixture.C
local notation "iC"=> (42/256:ℝ)
local notation "i₀"=> (46/256:ℝ)
local notation "k₀"=> (1/256:ℝ)
local notation "W₀"=> (1/8:ℝ)
local notation "G!"=> (40/256:ℝ)
-- v coverage.B. Price hΘ=Ϛ*g. All eps.Post-L heat.Reward
variable {B:ℕ}
open QCD.Ruby Push.AbsoluteSums.Trees
lemma pulseMotion (L:Side)(r v y θ:ℝ)(hr:0≤r)(hw:r < v)(hθ:0 ≤ y)(ht:0 < θ) :∀ᶠ x in atTop,StackK (highR L x) (taxK L x v) (taxK L x r) (y+θ) y (y+θ+1) 1 :=by
    let t:=(v-r)/2; have hw':0<t:=div_pos (sub_pos.mpr hw) (by norm_num); let f x:=taxK L x t; let u x:=(f x)⁻¹; let g x:ℝ:=16*(1+(highR L x:ℝ))^4; let m x:= u x+u x*g x; have hU:Rate su L (-1) u:=couplings _ hw'; have hV:Rate su L 0 g:=(radH L).mul_left 16; have hM: Rate su L (-1) m:=by apply hU.add; simpa only [add_zero] using hU.mul hV
    have hJ:= (((hV.mul hM).mul_right θ⁻¹).mul_left 4).below (by norm_num) (1/2) (by norm_num)
    filter_upwards [(show Tendsto (fan L (1/3)) atTop atTop from (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp (Seat.your L)).eventually_ge_atTop (1/t),hJ, (hM.mul_right ((1-1/2:ℝ)⁻¹)).below (by norm_num) 1 zero_lt_one] with x hx ht' hn c N I V Y X s a he hp
    obtain ⟨f',hf,hE⟩:=hp.cost; obtain ⟨b,hQ,hb⟩:=he; have hZ :1 ≤ f x:= Real.one_le_exp (mul_nonneg hw'.le (fan_pos ..).le); have hu:= zero_lt_one.trans_le hZ
    have hm : (Animals.ballCost (highR L x):ℝ) ≤ g x:=by unfold g Animals.ballCost; push_cast; have h0 := pow_le_pow_left₀ (show 0 ≤ (↑(highR L x):ℝ)+↑(highR L x)+1 by positivity) (show (↑(highR L x):ℝ)+↑(highR L x)+1≤2*(1+↑(highR L x)) by linarith) 4; linarith only [h0]
    have hg :0 ≤ g x:=by unfold g; positivity
    have hm':0 < m x:=by unfold m; have h: 0<u x:= inv_pos.mpr hu; positivity
    have hv : 0≤ f':=fun i=>(norm_nonneg _).trans (hE i 1)
    obtain ⟨h₀,h₁⟩:=Ruby.renowned Y X (t:=s) (fun i=>(norm_nonneg _).trans (hb i 1)) hv hb hE (show 1 ≤ taxK L x r from Real.one_le_exp (mul_nonneg hr (fan_pos ..).le)) hm' ht hθ (by norm_num : (1/2:ℝ)<1) (show degreePrice (highR L x) (m x) θ ≤1/2 from (by unfold degreePrice Push.AbsoluteSums.Trees.stretch; refine le_trans ?_ ((le_abs_self _).trans ht'); rw [div_eq_mul_inv]; gcongr )) hQ (Ruby.scopes X hu (Real.exp_pos _).le hv hf (show 1≤ taxK L x r from Real.one_le_exp (mul_nonneg hr (fan_pos ..).le)) (by unfold f taxK; rw [← Real.exp_add, ←Real.exp_add]; apply Real.exp_monotone; have hf:=(div_le_iff₀ hw').mp hx; unfold t at hf ⊢; linarith only [hf]) hZ) (by rw [mul_one]; exact add_le_add_right (mul_le_mul_of_nonneg_left hm (inv_pos.mpr hu).le) _)
    exact ⟨_,fun i=>budget_loosen (h₁ i) ((le_abs_self _).trans hn),h₀⟩
lemma convoy (H:ℕ) (u:ℝ→ℝ)(σ:ℝ)(hu:Rate su L σ u): ∀ᶠ x in atTop, DeckT L H x (u (run L x)):=by
   let a:=(1/256:ℝ); have ha:0<a:=by unfold a; norm_num
   let D t:=1+Film.allowance H (radiusB t) a (|u t|); let e':=max σ 0; have he:Rate su L e' D:=by
      have hx:Rate su L σ fun t=> |u t|:=fun V h=> (hu V h).mono (fun i h=>  le_trans (abs_abs (u i)|>.le) h); let K t:=(radiusB t+radiusB t+1:ℝ); have hk:Rate su L 0 K:= (Rate.radius_price.add Rate.radius_price).add (Rate.const 1)
      have hf:Rate su L σ fun i=>|u i| *(K i)^4*H/a:=by simpa only [div_eq_mul_inv,zero_mul,add_zero] using (((hx.mul (hk.pow 4)).mul_right (H:ℝ)).mul_right a⁻¹)
      exact Rate.add ((Rate.const 1).weaken (le_max_right ..)) (Rate.add (hf.weaken (le_max_left ..)) ((Rate.const 1).weaken (le_max_right ..)))
   filter_upwards [(Work.E09.betaF_growth su L).eventually (upperTax L (1/2) (by norm_num) D e' he),(Work.E09.betaF_growth su L).eventually (Cupola.exsteam L ha H hu), Finch.dim L (1/3), pulseMotion L 2 3 (42/256) (4/256) (by norm_num) (by norm_num) (by norm_num) (by norm_num),Film.Surplus.grantK L (1/256) 2 1 H (by norm_num) (by norm_num) (by norm_num) (fun _=>1) (Rate.const 1) (40/256)] with i hi hW hzF hg hQ
   refine ⟨?_,?_,?_⟩
   · intro c I _ p S X hp hx; let B:= radiusB (run L i); have hv:= Film.totalFuel p a S X H hp hx ha (abs_nonneg _) (hW c I p X.place hp)
     let Z:=taxK L i; calc
       _≤ D (run L i)*Z 3:= mul_le_mul_of_nonneg_right (add_le_add_right hv 1) (Real.exp_nonneg _)
       _≤ Z 1*Z 3:= mul_le_mul_of_nonneg_right (hi.trans (Real.exp_monotone (by change (1/2:ℝ)*fan L (1/3) (run L i) ≤1*_; linarith only [hzF]))) (Real.exp_nonneg _)
       _=_:=by unfold Z taxK; rw [← Real.exp_add]; congr 1; ring
   · convert hg using 1 <;> first| rfl | norm_num
   intro c I _ E P p q W F σ hf hp hΓ hz he
   have h := hz.tilt; rw [hf]; have ht:Pill F P.threshold σ (radiusB (run L i)) (40/256+2*(1/256)) (taxK L i 2):=by rw [←hf,show 40/256+2*(1/256:ℝ)=42/256 from by norm_num]; exact h
   exact hQ σ 6 c _ _ _ _ _ _ _ (fun _=>1) hp hΓ ht hz.fits (fun i=> le_rfl) he
end Sail
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Sail.convoy
