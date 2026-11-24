import YM.QCD.Page.Story
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
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
lemma prolong (t c:ℝ)(ht : -(1/2:ℝ)< t)(he:t<0)(h:0≤c) (P:Teller su): ∃ Q:Target su P, Q.rate=t∧ Q.exp=c∧ Q.halo=500:=by
   let i:=P.top.supportExponent; let j:= P.top.width; let k:= P.below.width; let hE:= min i (min j k)
   have hv:= lt_min P.top.price_pos (lt_min P.top.width_pos P.below.width_pos)
   have hx : hE≤ i:=min_le_left ..; have hp : hE≤j:=(min_le_right ..).trans (min_le_left ..); have hu : hE≤k:=(min_le_right ..).trans (min_le_right ..); change 0<hE at hv
   let A:=Next.Foundations.chart su; have hA:=Next.Foundations.chart_ok su
   exact ⟨⟨hE/16,c,1,t,500,le_rfl,A,hA,by positivity,by norm_num,h,ht,he,by change 4*(hE/16) < i∧ 8*(hE/16) < j∧8*(hE/16) < k; refine ⟨?_,?_,?_⟩<;> linarith⟩,rfl,rfl,rfl⟩
open Oasis
lemma oversees (j:ℕ)(ζ:ℝ)(hv:0<ζ): ∃ ξ θ v:ℝ, θ<1/8∧ Font j ξ θ v ζ:=by
   let f t:=amass (j+1) t (2*(t/8*2+t*2)); have he:f 0=0:=by simp [f,amass,Oasis.heron]
   have h : Continuous f:=by unfold f amass Oasis.heron; fun_prop
   have hb : ∀ᶠ x in 𝓝[>](0:ℝ), f x<ζ:= (h.continuousAt.continuousWithinAt (x:=0)).eventually (gt_mem_nhds (he.trans_lt hv)) -- edit
   have hp : ∀ᶠ x in 𝓝[>](0:ℝ), 0<x:= self_mem_nhdsWithin (a:= (0:ℝ)) (s:=Set.Ioi 0)
   obtain ⟨z,⟨hz,he⟩,hI⟩:= ((hp.and hb).and (nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0:ℝ)<1)))).exists; change 0 < z at hz; exact ⟨z,z/8,z/2,by linarith,by unfold Font; exact ⟨by positivity,by linarith,by linarith,hI,he⟩⟩

namespace Rails
variable (P₀:Plan j)(S:Stage)(N:ℕ)
lemma starsG (v:ℝ)(he:4 ≤ j) : ∃ (i:ℕ)(Y M u₀ v₀ s₀ Λ:ℝ), 0 < i ∧ 0<Y ∧0≤ M ∧ 0<Λ ∧∀ E:Patch,E.J=j → Charter P₀ S E.L N i Y M u₀ v₀ s₀ Λ v:=by
   obtain ⟨A,Q,δ',u,v',p,n,hN,h0,h1,h2,h3⟩:= Shard.pagoda P₀ S N v he he
   refine ⟨n,A,Q,u,v',p,δ',hN,h0,h1,h2,fun E hE=>?_⟩
   subst j
   refine ⟨?_,?_⟩; · obtain ⟨d,hD,h⟩:=h3 (Pike E 0); exact hD
   intro F hF; obtain ⟨K,hL,hP⟩:= h3 F
   let X:=Shard.balanced K n u v' -- stray
   -- type equality pack alias. rw L
   rw [← hF]; exact ⟨X,rfl,rfl,fun c=>
     let H:= hP c; ⟨H.choose,H.choose_spec.1,fun q h=>(H.choose_spec.2 q h).2⟩⟩
-- Precinct may not tie χ independence choose χ.
lemma atlasQ (B:Teller su) (r:ℝ)(h:0≤r):∃ (Q:ConnectedActivityE6.Target su B)(a:ℝ), 0≤ a ∧ (a+1)+1+1 ≤ Q.exp ∧ Q.rate ≤ -(3/8:ℝ) ∧ B.top.supportExponent+3≤ a ∧ r+1≤ a+1∧ ((B.top.supportExponent+1)+1+1)*frostQ Q.halo≤a+1:=by
    let s:=B.top.supportExponent+3; let z:=((B.top.supportExponent+1)+1+1)*frostQ 500; let A:=max (max s r) z; have hv:= h.trans ((le_max_right s _).trans (le_max_left _ z)); obtain ⟨Q,h,hm,ht⟩:=prolong (-(3/8:ℝ)) (A+1+1+1) (by norm_num) (by norm_num) (by linarith) B;
    have hp:s≤A:= (le_max_left s r).trans (le_max_left _ z); refine ⟨Q,A,hv,hm.symm ▸ le_rfl,h.le,hp,add_le_add_left ((le_max_right s r).trans (le_max_left _ z)) _,ht.symm ▸ ?_⟩; exact (le_max_right ..).trans (le_add_of_nonneg_right zero_le_one)
variable {l' k₁ o':ℕ} {ν' s K₀ b b₀ b₁ b₂ X₀ κ W' Λ r A' U' e ε t Y' σ' u₀ v₀ s₀Q s₀ u₁ u₂ u' v₁ v₂ v₃ Z β ξ x' Γ:ℝ}
variable {N} (F₀:Flavor N)(T':Teller su)(χ:Chi)
noncomputable def creditΓ (L:Side)(s D M:ℝ)(N:ℕ):= s* Real.log L.val+D+N*M
lemma punctuate (α B C:ℝ)(hp:|α+B| ≤ C) : |α| ≤ |B|+C:=by
   rw [show α=(α+B)+ -B from (by ring)] -- rewrite both sides? α RHS not.
   apply (abs_add_le ..).trans; rw [abs_neg, add_comm]; exact add_le_add_right hp _
noncomputable def betaFare (L:Side)(D:ℝ):ℝ:= creditΓ L su.slopeConstant D 0 0 -- phys.N
noncomputable def tallyFare (L:Side)(D W:ℝ)(N:ℕ):ℝ:= |betaQ N* Real.log L.val|+D+N*W+1
lemma fare_pos (L:Side) (H:ℝ)(h:0≤ D)(hp:0≤H):0 < tallyFare L D H N:=by unfold tallyFare; positivity
-- `Campaign` marching cost predictor potential. Count enters policy.
structure Campaign (F₀: Flavor N)(T': Teller su)(P:ConnectedActivityE6.Target su T') (J:Patch)(P':Plan J.J)(B:T'.below=T'.top)(a d ε u X D Γ:ℝ)(χ:Chi): Prop where
    -- Column extends Actual quote χ. κ and θ need global choose BEFORE x! binder
    capital : ∀ (T:ℕ→Towers J.L)(η M σ W' α:ℝ),0 < η→ 0<M→1 ≤ W'→0<α→∀ (Q':ParcelR), Q'.Rates T'.η → ∃ (κ H W z μ Z A':ℝ) (o:Target.Order su W) (l' k' n' n:ℕ)(τ:Policy P T'.top N),0<κ∧ H=u ∧0<τ.t∧ (∀ᶠ x in atTop,Tall J P.halo l' k' n' n x) ∧ ∀ᶠ x in atTop, Column τ P' F₀ Q' a η d x T'.C W' T'.η ε σ X D H κ B T l' k' n' n χ o α M μ z (betaFare J.L D) A' Z
-- shorthand t ε'=Sits.credit; ν M.
end Rails
end YM.QCD.Acre
