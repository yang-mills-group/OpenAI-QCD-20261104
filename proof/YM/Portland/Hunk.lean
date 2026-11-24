import YM.QCD.Ruby.Tickets
import YM.Oars.Apprise
import YM.QCD.Ruby.Barge
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Trees
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {t:ℝ} {ι β:Type}{a u v w A:ℝ} {B:ℕ}
variable (Y:Hue c N ι) (X:Rail c N β)
variable {p :ι→ℝ} {q:β→ℝ}
variable (h:Ac.Hit Y.bud B p a A)(hv:0≤p)(hp:0 ≤ q)(ht: 0≤a)
variable (hr: Ac.Hit (home X) B ((metal X A)*q) a u)
include ht h hv hp hr
lemma tonedE {A':ℝ} (H:Ac.Hit Y.bud B p (a+1/256) A') :Ac.Hit (Car.vat (Y:=Y) (X:=X)) B (money Y X p q) a (u+u* Animals.ballCost B*256*A'):=by
    have hU:= budget_nonneg (hr 0)
    intro x
    let m:=money Y X p q; have hm (i:Car Y X): 0 ≤ m i:=mul_nonneg (hp _) (prod_nonneg fun _ _=>wig_nn hv _)
    let w i:=routing Y X i q p B a
    apply budget_of_sum; · intro i; split; exact mul_nonneg (hm _) (Real.exp_pos _).le; exact le_rfl
    intro Z
    rw [← sum_filter]; let V:= Z.filter fun i=> x∈Car.vat i
    let U:=V.filter fun i => x∈ home X i.site
    let S:=V\U; have he(i)(hi:i∈S):∃ j∈Car.bag i,x∈Y.bud j:=by
       obtain ⟨hj,hH⟩:=mem_sdiff.mp hi; obtain ⟨p,hy,hx⟩:=mem_biUnion.mp ((mem_filter.mp hj).2); cases p
       next p=> rw [mem_singleton.mp (inl_mem_disjSum.mp hy)] at hx; exact False.elim (hH (mem_filter.mpr ⟨hj,hx⟩))
       next p=> exact ⟨p,inr_mem_disjSum.mp hy,hx⟩
    change ∑ i∈V,m i*_ ≤ _; apply (sum_le_sum (s:=V) (fun i _=> cabs Y X hv hp ht i)).trans
    change ∑ i∈V,w i ≤ _; rw [← sum_sdiff (filter_subset _ _ : U⊆V)] -- replace
    have hZ : ∑ i∈U,w i≤u:=fromhome Y X h hv hp ht hr U x fun i hi=>(mem_filter.mp hi).2
    change (∑ i∈S,w i)+ ∑ i∈U,w i≤_
    rw [add_comm _ (∑ i∈U,w i)]
    apply add_le_add hZ
    let T:=(S.biUnion Car.bag).filter fun i=>x∈Y.bud i; let P j:=S.filter fun i=> j∈Car.bag i; let C:ℝ:=Animals.ballCost B
    have hx j (hj:j∈T): (∑ i∈P j,w i) ≤ (u*C*256) * (if x∈Y.bud j then p j*currency B (a+1/256) (Y.bud j) else 0):=by
       have he':=fromspur Y X h hv hp ht hr j (P j) (fun j hj=>(mem_filter.mp hj).2); rw [if_pos (mem_filter.mp hj).2]; apply he'.trans
       let V:=Y.bud j; let v:=coverNumber B V
       have h':(V.card:ℝ) ≤ v*C:= by unfold C; rw [← Nat.cast_mul]; exact Nat.cast_le.mpr (Corona.pays V B)
       have hh':(v:ℝ) ≤256*Real.exp ((1/256:ℝ)*v):=by linarith only [Real.add_one_le_exp ((1/256:ℝ)*v)]
       have he'':(V.card:ℝ)≤ C*256*Real.exp ((1/256:ℝ)*v):=h'.trans ((mul_comm _ C).le.trans ((mul_le_mul_of_nonneg_left hh' (Nat.cast_nonneg _)).trans_eq (by ring)))
       refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he'' (mul_nonneg (hv _) (Real.exp_pos _).le)) hU) (le_of_eq ?_)
       unfold currency; rw [add_mul, Real.exp_add]; unfold v V; ring
    calc _≤∑ j∈T,∑ i∈P j,w i:=by
            simp_rw [P,sum_filter]; rw [sum_comm]; apply sum_le_sum; intro i hi; obtain ⟨j,hj,hT⟩:=he i hi; apply le_trans _ (single_le_sum (f:=fun k=> if k∈i.bag then w i else 0) (a:=j) (fun i _=>ite_nonneg (routing_nn Y X hv hp ht _) le_rfl) (mem_filter.mpr (And.intro (mem_biUnion.mpr ⟨i,hi,hj⟩) hT))); rw [if_pos hj]
         _≤_:= (sum_le_sum hx).trans (budget_sum (budget_scale (mul_nonneg (mul_nonneg hU (Nat.cast_nonneg _)) (by norm_num : (0:ℝ)≤256)) (H x)) _)
end YM.QCD.Ruby

namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Trees
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {t:ℝ} {ι β:Type}{a u v w A R m k σ B' v' ht q':ℝ} {B:ℕ}
variable (Y:Hue c N ι) (X:Rail c N β)
variable {p :ι→ℝ} {q:β→ℝ}
variable (hP : 0 ≤ p)(hQ : 0 ≤ q)
variable (h: ∀ i V, ‖token c N w (Y.mean i V)‖ ≤ p i) (hp : ∀ i V, ‖token c N w (X.warp i V)‖ ≤ q i)
include hP hQ h hp
lemma renownedE (he:1≤R)(hm:0 < m)(hk:0<k)(hD:0≤a)(hσ:σ<1)(ht: degreePrice B m k ≤σ)
    (hh:Ac.Hit Y.bud B p (a+k+1/256) A) (hx:Ac.Hit (home X) B ((metal X A)*taxed (oriD X) q R) (a+k) u)(hv:u+u*Animals.ballCost B*256*A≤ m):
   (∀ i V, ‖token c N w ((Trail Y X t).warp i V)‖ ≤ fair Y X p q i) ∧ Ac.Hit (home (Trail Y X t)) B (taxed (oriD (Trail Y X t)) (fair Y X p q) R) a (m*(1-σ)⁻¹):=by
   refine ⟨haloP Y X hP hQ h hp,?_⟩; have hs:(0:β→ℝ) ≤ taxed (oriD X) q R:=fun j => mul_nonneg (pow_nonneg (zero_le_one.trans he) _) (hQ j); refine priceV Y X (k:=k) hP hQ he ?_ hD; refine ⟨hm,hk,ht,hσ,fun i=> mul_nonneg (hs i.site) (prod_nonneg fun _ _=> wig_nn hP _),fun i=> budget_loosen (tonedE Y X ?_ hP hs (by linarith) hx hh i) hv⟩
   intro i; refine budget_mono (hh i) (fun j=> ?_) (fun j=> ?_)
   · split; exact mul_nonneg (hP _) (Real.exp_pos _).le; exact le_rfl
   split; next h=> refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (hP _); exact mul_le_mul_of_nonneg_right (by linarith : a+k≤a+k+1/256) (Nat.cast_nonneg _)
   next _=> exact le_rfl
end YM.QCD.Ruby
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
lemma pulseBottle (L:Side)(r v y θ:ℝ)(hr:0≤r)(hw:r < v)(hθ:0 ≤ y)(ht:0 < θ) :∀ᶠ x in atTop,StackK (highR L x) (taxK L x v) (taxK L x r) (y+θ) y (y+θ+1/256) 1 :=by
    let t:=(v-r)/2; have hw':0<t:=div_pos (sub_pos.mpr hw) (by norm_num); let f x:=taxK L x t; let u x:=(f x)⁻¹; let g x:ℝ:=16*(1+(highR L x:ℝ))^4; let m x:= u x+u x*g x*256; have hU:Rate su L (-1) u:=couplings _ hw'; have hV:Rate su L 0 g:=(radH L).mul_left 16; have hM: Rate su L (-1) m:=by apply hU.add; simpa only [add_zero] using (hU.mul hV).mul_right 256
    have hJ:= (((hV.mul hM).mul_right θ⁻¹).mul_left 4).below (by norm_num) (1/2) (by norm_num)
    filter_upwards [(show Tendsto (fan L (1/3)) atTop atTop from (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp (Seat.your L)).eventually_ge_atTop (1/t),hJ, (hM.mul_right ((1-1/2:ℝ)⁻¹)).below (by norm_num) 1 zero_lt_one] with x hx ht' hn c N I V Y X s a he hp
    obtain ⟨f',hf,hE⟩:=hp.cost; obtain ⟨b,hQ,hb⟩:=he; have hZ :1 ≤ f x:= Real.one_le_exp (mul_nonneg hw'.le (fan_pos ..).le); have hu:= zero_lt_one.trans_le hZ
    have hm : (Animals.ballCost (highR L x):ℝ) ≤ g x:=by unfold g Animals.ballCost; push_cast; have h0 := pow_le_pow_left₀ (show 0 ≤ (↑(highR L x):ℝ)+↑(highR L x)+1 by positivity) (show (↑(highR L x):ℝ)+↑(highR L x)+1≤2*(1+↑(highR L x)) by linarith) 4; linarith only [h0]
    have hg :0 ≤ g x:=by unfold g; positivity
    have hm':0 < m x:=by unfold m; have h: 0<u x:= inv_pos.mpr hu; positivity
    have hv : 0≤ f':=fun i=>(norm_nonneg _).trans (hE i 1)
    obtain ⟨h₀,h₁⟩:=Ruby.renownedE Y X (t:=s) (fun i=>(norm_nonneg _).trans (hb i 1)) hv hb hE (show 1 ≤ taxK L x r from Real.one_le_exp (mul_nonneg hr (fan_pos ..).le)) hm' ht hθ (by norm_num : (1/2:ℝ)<1) (show degreePrice (highR L x) (m x) θ ≤1/2 from (by unfold degreePrice Push.AbsoluteSums.Trees.stretch; refine le_trans ?_ ((le_abs_self _).trans ht'); rw [div_eq_mul_inv]; gcongr )) hQ (Ruby.scopes X hu (Real.exp_pos _).le hv hf (show 1≤ taxK L x r from Real.one_le_exp (mul_nonneg hr (fan_pos ..).le)) (by unfold f taxK; rw [← Real.exp_add, ←Real.exp_add]; apply Real.exp_monotone; have hf:=(div_le_iff₀ hw').mp hx; unfold t at hf ⊢; linarith only [hf]) hZ) (by rw [mul_one]; exact add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (inv_pos.mpr hu).le) (by norm_num:0≤(256:ℝ))) _)
    exact ⟨_,fun i=>budget_loosen (h₁ i) ((le_abs_self _).trans hn),h₀⟩
end Sail
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Sail.pulseBottle
