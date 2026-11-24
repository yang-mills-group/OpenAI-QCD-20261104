import YM.Massive.Reference.Prototype
import YM.QCD.Rain.Majesty
import YM.Push.BETA_TRANSPORT.Noise
import YM.QCD.Fall.Clan
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
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
-- canonical REAL all layers with UV uniform log.F. boundary.T. Needs Even.
open Rain
variable (F₀:Flavor N)
open IV Globe Next.Rank
namespace Reference
variable (L':HaarBudget su)

-- usable scheduling and target compatibility, precursor to splitting trajectory
lemma founder (χ:Chi) (hw:Order4 L' χ J F₀ Q a d D)
    (hJ: J.J=4)(hk:J.Branches T'.bind su)(he:T'.bind.penalty=1)(hL:3≤J.L.val)(hv:0<ε)(hE:D+2 ≤ ε/2*Real.log J.L.val) :
    ∃ (V:ℕ→Bed) (T:ℕ→Towers J.L) (σ γ δ s η:ℝ)(Ω:ParcelR)(b κ:ℝ)(τ:Policy Q T'.top N)(A K:ℝ),0<η∧0<κ∧0< τ.t∧ Soil T'.bind T'.top.clip J T'.η η T'.C V T ∧ ReadyR Ω (passportM J.J J.order_cut) J T'.bind T'.top.clip a d T'.η T'.C T'.C ∧ ∀ᶠ x in atTop, ∃ (B:SparkMesh), (∀ i, B.n i=B.n 0*J.L^i) ∧∀ prec:ℕ→ℝ,(∀ i,0 < prec i) → ∃ rec:Favorite (fixed J T'.bind hk) N, Goalpost J.L _ N rec (positiveAnswer J x κ τ.t) (run J.L x) ε prec ∧ Track L' T' Q J hk F₀ V T σ γ δ a d D s x B Ω τ A K κ b rec:=by
    obtain ⟨V,T,σ,γ,δ,s,η,Ω,b,κ,τ,W,H,z,μ,Z,A',o,A,K,hη,hκ,ht,hs,hb,hV,hR,l,hX⟩:=hw.source
    refine ⟨V,T,σ,γ,δ,s,η,Ω,b,κ,τ,A,K,hη,hκ,ht,hV,hR,?_⟩; filter_upwards [hX,demand F₀ Ω J.L (passportM J.J J.order_cut) (by rw [hJ]) hκ ht] with x hx hy -- order
    obtain ⟨B₀,B,hB,h4,hY,hx,hc,hF,hX⟩:=hx; let U := positiveAnswer J x κ τ.t; refine ⟨B,hF,fun p hp=>?_⟩
    apply favorite (Q:=Q) (Ω:=Ω) (τ:=τ) (hw:=hk) B F₀ hL he L' hR hx hF h4 _ hy p hp hv hE
    intro n hn; obtain ⟨S,g,U,Y,P,hg,hH,hs⟩:= hX n hn; exact ⟨S,g,U,P,fun i=>g.costP i+(N:ℝ)* Y i,hg,fun i=> hs i (1/2) (by norm_num)⟩

-- all sufficiently large beta as written in Physics problem
noncomputable abbrev clockX (L: Side) (β : ℝ) := β-su.slopeConstant*Real.log L.val
lemma halt (t:ℝ)(L:Side): run L (clockX L t)=t:=by unfold run clockX betaF; ring

lemma readjust (χ:Chi) (hw:Order4 L' χ J F₀ Q a d D)
    (hJ: J.J=4)(hk:J.Branches T'.bind su)(he:T'.bind.penalty=1)(hL:3≤J.L.val)(hv:0<ε)(hE:D+2 ≤ ε/2*Real.log J.L.val) :
    ∃ (V:ℕ→Bed) (T:ℕ→Towers J.L) (σ γ δ s η:ℝ)(Ω:ParcelR)(b κ:ℝ)(τ:Policy Q T'.top N)(A K:ℝ),0<η∧0<κ∧0< τ.t∧ Soil T'.bind T'.top.clip J T'.η η T'.C V T ∧ ReadyR Ω (passportM J.J J.order_cut) J T'.bind T'.top.clip a d T'.η T'.C T'.C ∧ ∀ᶠ β in atTop, ∃ (B:SparkMesh), (∀ i, B.n i=B.n 0*J.L^i) ∧∀ prec:ℕ→ℝ,(∀ i,0 < prec i) → ∃ rec:Favorite (fixed J T'.bind hk) N, Goalpost J.L _ N rec (positiveAnswer J (clockX J.L β) κ τ.t) β ε prec ∧ Track L' T' Q J hk F₀ V T σ γ δ a d D s (clockX J.L β) B Ω τ A K κ b rec:=by
    obtain ⟨V,T,σ,γ,δ,s,η,Ω,b,κ,τ,A,K,hη,hκ,ht,hV,hR,hX⟩:= founder F₀ L' χ hw hJ hk he hL hv hE; have hp : Tendsto (clockX J.L) atTop atTop := by unfold clockX; simp_rw [sub_eq_add_neg]; exact tendsto_atTop_add_const_right _ _ tendsto_id -- name?
    refine ⟨V,T,σ,γ,δ,s,η,Ω,b,κ,τ,A,K,hη,hκ,ht,hV,hR,?_⟩; filter_upwards [hp.eventually hX] with β hx; rwa [halt] at hx

lemma odd_ready (he:0< ε) (c:ℕ) (C:ℝ) : ∀ᶠ n : ℕ in atTop, c ≤ 2*n+1 ∧ C≤ ε* Real.log (2*n+1):=by
    have ht : Tendsto (fun n:ℕ=>(2*n+1:ℝ)) atTop atTop:= by exact tendsto_atTop_add_const_right _ _ ((tendsto_natCast_atTop_atTop (R:=ℝ)).const_mul_atTop (by positivity))
    filter_upwards [eventually_ge_atTop c, ((Real.tendsto_log_atTop.comp ht).const_mul_atTop he).eventually_ge_atTop C] with n hx hy; exact ⟨by omega,hy⟩

lemma odd_now (he:0< ε)(c:ℕ) (C:ℝ) : ∃ J:Patch,J.J=4∧ c≤J.L.val ∧ C ≤ ε*Real.log J.L.val:=by
    obtain ⟨n,⟨hn,hM⟩⟩:= (odd_ready he (max c 512) C).exists
    let L:Side:= ⟨2*n+1,by omega⟩; refine ⟨⟨L,4,le_rfl,?_,n,rfl⟩,rfl,(le_max_left ..).trans hn,?_⟩
    · change 3 ≤ 2*n+1; omega
    change C ≤ ε*Real.log (((2*n+1:ℕ):ℝ)); push_cast; exact hM

theorem positive_common {ε:ℝ} (he:0< ε) :
  ∃ (T':Teller su)(Q:ConnectedActivityE6.Target su T')(L':HaarBudget su)(s t D:ℝ) (J:Patch), T'.bind.penalty=1 ∧ J.J=4 ∧ 512≤ J.L.val ∧ D+2 ≤ ε/2 * Real.log J.L.val ∧ ∃ (hJ:J.Branches T'.bind su),
    Order4 L' Chi.canonical J (0:Flavor 6) Q s t D ∧ Massive.betaSlope=betaQ 6 ∧ 0 < betaQ 6 ∧
    ∃ (V:ℕ→Bed) (T:ℕ→Towers J.L) (σ γ δ A η:ℝ)(Ω:ParcelR)(b κ:ℝ)(τ:Policy Q T'.top 6)(A0 K:ℝ),0<η∧0<κ∧0< τ.t∧ Soil T'.bind T'.top.clip J T'.η η T'.C V T ∧ ReadyR Ω (passportM J.J J.order_cut) J T'.bind T'.top.clip s t T'.η T'.C T'.C ∧ ∀ᶠ β in atTop, ∃ (B:SparkMesh), (∀ i, B.n i=B.n 0*J.L^i) ∧ ∀ prec:ℕ→ℝ,(∀ i,0 < prec i) → ∃ rec:Favorite (fixed J T'.bind hJ) 6, Goalpost J.L _ 6 rec (positiveAnswer J (clockX J.L β) κ τ.t) β ε prec ∧ Track L' T' Q J hJ (0:Flavor 6) V T σ γ δ s t D A (clockX J.L β) B Ω τ A0 K κ b rec:=by
   obtain ⟨L'⟩ := Next.Rank.exists_budget su
   obtain ⟨K,hK,hJ⟩:= YM.Axial.viable su 1 zero_lt_one
   obtain ⟨T,rfl,hδ,hV,Q,s,t,D,m,h0,h1,h2,h3,h4⟩:= repeats (0:Flavor 6) L' Chi.canonical (by decide) (by decide) K
   obtain ⟨J,h,hv,hp⟩:= odd_now (half_pos he) m (D+2); have ht := (h4 J h (hJ J) hv).2
   exact ⟨T,Q,L',s,t,D,J,hK,h,h3.trans hv,hp,hJ J,ht,SIX.1,(ultraviolet _).2 (by decide),readjust _ L' _ ht h (hJ J) hK (by omega) he hp⟩
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.positive_common
