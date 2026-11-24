import YM.Eole.Logs
import YM.Clays.Silo
import YM.Profiles.Posts
import YM.Clays.Gale
/- Post clocks enough for knitting.Clays transfer ALL options live. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Kuna
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
open Sail Kites Plate.Card QCD.Calm Acre Rails.Reference Rails Bank.Hike Stags Bank
open QCD.Acre.Rails.Bank QCD.Acre.Rails.Bank.Hike MassiveQCD.Twist Basal Eole Eole.Gain
variable (L:Side)(n k m h r Fo Fx U0 i H D:ℕ)(θ Mξ A B T₀:ℝ)
local notation "ε"=> (1/256:ℝ)
local notation "α"=> (24/256:ℝ)
local notation "V"=> Sail.roomAt L θ
local notation "βd"=>highR L
noncomputable abbrev pond (L:Side)(k:ℕ)(n:ℕ)(x:ℝ):=Basal.riseP k n (highR L x) (1/256) (24/256)*soldE L x
local notation "Uε"=> pond L m h
noncomputable abbrev heightP (L:Side)(k n:ℕ)(a b x:ℝ):= (1+b*a) * pond L k n x
local notation "Pv"=> heightP L m h A B
lemma pond_nonneg (x:ℝ):0≤Uε x:=by unfold pond Basal.riseP soldE taxK polyPrice; positivity
lemma pivot (hA:1≤ A)(hB:1≤ B)(x:ℝ): A*Uε x ≤ Pv x:=by apply mul_le_mul_of_nonneg_right _ (pond_nonneg ..); nlinarith only [hA,hB]
structure Seems (j:ℕ)(x:ℝ) : Prop where
    tune : Gain.Docket L x (highR L x) n j Fo (youngF L j x) (bonus Fo (highR L x) (1/256)*T₀+Sail.roomAt L θ x) (perchF L x) (soldE L x)
    high : Basal.Dough L Fx x
    spot : rentM (highR L x) n k ε*(perchF L x*(1-1/2)⁻¹) ≤ soldE L x
    estate : soldE L x ≤ V x
    altar : Stags.bonus Fx (highR L x) ε*(Uε x+B*(A*Uε x)) ≤ 1
variable (j:ℝ→ℕ)(hj:Rate su L 0 fun x=>(j x:ℝ))
lemma raised : Rate su L 0 (fun x=>Basal.riseP m h (highR L x) ε α):=by unfold Basal.riseP; exact (((((base_rate L).mul_left 4).add (Rate.const 2)).pow (m*h)).weaken (by ring_nf; try rfl)).mul_right _ |>.mul_right _
lemma sold (b:ℝ): Rate su L b (soldE L):=couplings L (by norm_num)
lemma riseX (b:ℝ): Rate su L b (Uε):= ((raised L m h).mul (sold L b)).weaken (le_of_eq (zero_add b))
local notation "εK"=> fun x=>Ivy.crawl L 1 x
include hj
set_option maxHeartbeats 680000 in
lemma assembles : ∀ᶠ x in atTop, Seems L n k m h Fo Fx θ A B T₀ (j x) x:=by
     have hF: Rate su L 0 (fun x=>bonus Fo (highR L x) ε*T₀+V x):= Rate.add (((bumpedH L Fo ε).ruled).mul_right _) ((slotR L θ).weaken (by norm_num)) -- bumped API inspect
     have hB:= Eole.Gain.minted L j _ hj hF n k Fo
     have hV:Rate su L (-1) (fun x=> bonus Fx (highR L x) ε*(Uε x+B*(A*Uε x))):= (((bumpedH L Fx ε).ruled).mul ((riseX L m h (-1)).add (((riseX L m h (-1)).mul_left A).mul_left B))).weaken (by norm_num)
     have hz:= (sold L (-2)).mul (inverseSlot L θ)
     filter_upwards [hB, lump L Fx,shuttle L θ,hz.below (by norm_num) 1 zero_lt_one,hV.below (by norm_num) 1 zero_lt_one] with x h hh hQ ht hl
     refine ⟨h.1,hh,h.2,?_, (le_abs_self _).trans hl⟩; apply (div_le_one hQ.1).1; rw[div_eq_mul_inv]; exact (le_abs_self _).trans ht
omit hj
local notation "eμ"=>Mξ*Real.exp ((1/16:ℝ)*81)*B
local notation "Fs"=> Kit.slope L
noncomputable abbrev cranes (L:Side)(x:ℝ):= Ivy.crawl L 1 x
local notation "Cd"=> cranes L
local notation "pl" x:arg=> cranes L x* (Kit.slope L)^(D+1)
local notation "Z0" x:arg =>eμ * (Pv x) + ((Fs ^(D+1)*Mξ)* (Pv x) + (pl x)*V x)
-- Q= run? x=input. all terms evaluate at x+=run L x.Crawl used there. H.K. stock. Issue permitting.B arrival constraints.
structure Herbs (x:ℝ) : Prop where
    owns : Seems L n k m h Fo Fx θ A B T₀ (j (run L x)) (run L x)
    purse : Monthly L i Fo U0 H k n m h D θ A B Mξ 1 1 1 x
    glaze : Ivy.CareL L H i D n k r m h θ Mξ B A (cranes L (run L x)) x
    support: r+1 ≤ highR L (run L x)
    fit : Pv (run L x) ≤ V (run L x)
    sideA : (1+B*A)*(Z0 (run L x)) ≤ V x
    sideB: (pl (run L x)) * V (run L x) + (A*eμ)*(Pv (run L x)) ≤ V x
lemma cranes_low : Tendsto (Cd) atTop (𝓝 0):=by
     let f(x:ℝ):ℝ:=1+highR L x; have hy: Tendsto (fun x:ℝ=>(highR L x:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp (Work.E01.radiusB_tendsto.comp (Work.E09.betaF_growth su L)); have hp : Tendsto f atTop atTop:= tendsto_atTop_add_const_left _ 1 hy; have hh:cranes L=fun x=>(f x)⁻¹:=funext (fun x=>by simp[f,Ivy.crawl,cranes]); rw [hh]; exact tendsto_inv_atTop_zero.comp hp
lemma jinx (f:ℝ→ℝ)(hF:Tendsto (fun t=> f t/(V t)) atTop (𝓝 0)):∀ᶠ t:ℝ in atTop, f (run L t) ≤ V t:=by
      have h:= hF.eventually_le_const (by norm_num:(0:ℝ)<1/4); filter_upwards [(Work.E09.betaF_growth su L).eventually h, (Work.E09.betaF_growth su L).eventually (shuttle L θ), shuttle L θ] with t hv ht hp; have hh:= (div_le_iff₀ ht.1).1 hv; exact hh.trans ((show (1/4)*(V (run L t))≤_ from by linarith only[hp.2.2]))
lemma lowV {f:ℝ→ℝ}{a:ℝ}(h:Rate su L a f)(hv:a<0): Tendsto f atTop (𝓝 0):=by rw [Metric.tendsto_nhds]; intro εx he; filter_upwards [h.below hv (εx/2) (by positivity)] with i hi; rw[Real.dist_eq,sub_zero]; exact hi.trans_lt (by linarith only [he])
lemma step_dim : Tendsto (fun x=> Pv x /V x) atTop (𝓝 0):=by
     simp_rw [div_eq_mul_inv]; exact lowV L (((riseX L m h (-2)).mul_left (1+B*A)).mul (inverseSlot L θ)) (by norm_num)
include hj
set_option maxHeartbeats 700000 in
lemma permits (ha:1≤A)(hb:1≤B)(hM:1≤Mξ)(ht:0 < θ):∀ᶠ x in atTop, Herbs L n k m h r Fo Fx U0 i H D θ Mξ A B T₀ j x:=by
     let F (x:ℝ):= cranes L x * Fs^(D+1); have hF:Tendsto F atTop (𝓝 0):=(by simpa only [zero_mul] using (cranes_low L).mul_const (Fs^(D+1))); have hu:= step_dim L m h θ A B -- adjust
     have hz: ∀ᶠ x in atTop,V x≠0:=(shuttle L θ).mono fun _ h=>h.1.ne'; have hn:Tendsto (run L) atTop atTop:= Work.E09.betaF_growth su L
     have hg:Tendsto (fun x=>(Z0 x) /V x) atTop (𝓝 0):=by
          refine Tendsto.congr' ?_ (show Tendsto (fun x=> eμ*(Pv x/V x)+(Fs^(D+1)*Mξ*(Pv x/V x)+F x)) atTop (𝓝 0) from (by simpa only [mul_zero,add_zero] using (hu.const_mul (eμ)).add ((hu.const_mul (Fs^(D+1)*Mξ)).add hF)))
          filter_upwards [hz] with x hx; field_simp <;> (unfold F; ring)
     have hB:Tendsto (fun x=>(F x*V x+(A*eμ)*(Pv x))/V x) atTop (𝓝 0):=by refine Tendsto.congr' ?_ (show Tendsto (fun x=>F x + (A*eμ)*(Pv x/V x)) atTop (𝓝 0) from (by simpa only [mul_zero,add_zero] using hF.add (hu.const_mul (A*eμ)))); filter_upwards [hz] with x hx; field_simp
     have hA0:Tendsto (fun x=> (1+B*A)*(Z0 x)/V x) atTop (𝓝 0):=by simp_rw [mul_div_assoc]; exact (mul_zero (1+B*A)) ▸ hg.const_mul _
     filter_upwards [hn.eventually (assembles L n k m h Fo Fx θ A B T₀ j hj),collects L i Fo U0 H k n m h D θ A B Mξ 1 1 1 ht ha hb (zero_le_one.trans hM) zero_le_one zero_le_one zero_le_one,Ivy.scrutiny L i H D n k r m h θ Mξ B A 1 ht hM hb ha,hn.eventually ((Work.E01.radiusB_tendsto.comp hn).eventually_ge_atTop (r+1)), hn.eventually ((step_dim L m h θ A B).eventually_le_const (by norm_num : (0:ℝ)<1)),hn.eventually (Sail.shuttle L θ), jinx L θ (fun x=>(1+B*A)*(Z0 x)) hA0,jinx L θ _ hB] with x h0 hY hk hp hv hnG hx hx'
     exact ⟨h0,hY,hk,hp,(div_le_one hnG.1).1 hv,hx,hx'⟩
end YM.MassiveQCD.Sample.Kuna
#print axioms YM.MassiveQCD.Sample.Kuna.permits
