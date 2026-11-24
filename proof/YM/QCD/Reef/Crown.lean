import YM.QCD.Reef.Oaken
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
open IV Globe
structure PanelsIV (J:Patch)(F':Flavor N)(Q:ConnectedActivityE6.Target su T')(a d D:ℝ):Prop where
    source : ∃ (V:ℕ→Bed)(T:ℕ→Towers J.L)(σ γ δ s η:ℝ)(Ω:ParcelR)(b κ:ℝ)(τ:Policy Q T'.top N),0<η∧0<κ ∧0<τ.t ∧1 ≤ s∧0≤b ∧ Soil T'.bind T'.top.clip J T'.η η T'.C V T ∧ReadyR Ω (passportM J.J J.order_cut) J T'.bind T'.top.clip a d T'.η T'.C T'.C ∧∃ l:ℕ,∀ᶠ x in atTop,∃ (B:SparkMesh)(M R:ℕ→ℝ), (∀ j,0<R j)∧(∀ y,x≤y→Shade J.L τ.t y)∧Even (B.n 0).val ∧B.n 0=sFirst J.L l (run J.L x)  ∧(∀ i,B.n i=B.n 0*J.L^i)∧∀ n:ℕ,0<n→∃ (S:ℕ→SparkMesh)(g:PulseRide T'.bind T'.top.clip J a d S n)(U:ℕ→SunR Ω)(Y:ℕ→ℝ)(P:ℕ→BudgetPoint),Invoice g Q.table V T σ γ δ D s ∧∀ k:ℕ,∃ v u w A,Stargate T' B F' g P U Y κ x τ.t D b k v u w A∧∀ i≤n,Continuous (A i)∧Rain.realP (A i)∧ (0<(Cvol (A i)).re ∧(∀ j,n=i+(j+1)→R j≤w i)∧ ∀ V,‖A i V‖≤(Cvol (A i)).re*expo (M (n-i)) (towerQ J B n i k))
variable {t : ℝ}
lemma drinkH (Y:ParcelR)(T':Teller su)(B₀:Side)(he:J.J=4)(hY:Y.Rates η)(h:0<t)(hz:Globe.DomainF (passportM 4 le_rfl) N J.L B₀ z) : ∀ᶠ x in atTop,∃ Z,Sipping J.L B₀ t Y (passportM J.J J.order_cut) F₀ x Z T'.top.clip a A Λ:=by
   -- η in scope? t?
   suffices hf:∀ (j:ℕ)(h:4≤j),j=4→∀ᶠ x in atTop,∃ Z,Sipping J.L B₀ t Y (passportM j h) F₀ x Z T'.top.clip a A Λ by exact hf _ _ he
   intro j h1 h2; subst j; exact nectar F₀ Y _ hY _ _ _ _ _ h hz
set_option maxHeartbeats 680000 in
lemma optic (h:T'.top.clip.direct≤1)(hp:T'.top.supportExponent=2)(hx₀:T'.top.width=a)(hd:d ≤T'.top.paths)(he:PressIR J T' Q F₀ χ a d D)(hx:0≤D)(hv:2*(D+3) ≤ subG N*Real.log J.L.val)(hk:J.Branches T'.bind su)(hN:Even N)(hJ:J.J=4)(hs:3 ≤J.L.val)(hX': ∀ c:Side,n≤ c.val→∃ A:ℝ,0≤A∧ Globe.DomainF (passportM 4 le_rfl) N J.L c A) : PanelsIV J F₀ Q a d D:=by
   constructor
   obtain ⟨V,T,Y,σ,γ,δ,v,η,W',κ,H,W,z,μ,Z,A',o,τ,hv',hη,hh,hR,hW,hκ,hH,ht,l,hG⟩:= he.value
   let β:PlaqAxes:= ⟨(0,1),by decide⟩; obtain ⟨r,hr⟩:= eventually_atTop.mp (High.PrismT.coverE F₀ β T'.top Z (roofsK J.L κ τ.t) hp τ.t ht) -- args
   obtain ⟨B₀,hℓ,hm⟩:= IV.whole J.L l hs n; obtain ⟨p,hp',he'⟩:=hX' B₀ hℓ
   refine ⟨V,T,σ,γ,δ,v,η,Y,W',κ,τ,hη,hκ,ht,hv',hW,hh,hR,l,?_⟩; filter_upwards [hG,fruitful (L:=J.L) F₀ h hκ ht,eventually_ge_atTop r, asks J D W' hx hv,summerR J.L τ.t ht, hm, drinkH (Λ:=v) (a:=a) (A:=d) F₀ Y T' B₀ hJ hR.1 ht he'] with x hx hy hr' hPw hU' hBase hOh -- syntax
   obtain ⟨B,hB,hX,hT,hC,he⟩:= hx; obtain ⟨Z₀,hZ⟩:= hOh; obtain ⟨k₀,hk₀⟩:=hBase; have hψ y hy:= (hU' y hy).2; obtain ⟨K,he'⟩:=surfing F₀ Y J T' 0 τ.t κ a d v hR.1 hU'; obtain ⟨G,hψ'⟩:=reb τ hψ;
   let U:= 16*(2*run J.L (run J.L x))*(T'.bind.penalty*2)+Z₀
   obtain ⟨Z₂,hΓ⟩:=sailsK Q τ K G hψ' o U
   refine ⟨B,(fun i=> K i - Z₂ i),(fun j=> fern τ o J K Z₂ G x j),fun _=> Real.exp_pos _,hψ,hB,hX,hT,fun n hn=>?_⟩; obtain ⟨S,g,P₀,Y',hg,hE⟩:= he n; obtain ⟨P,hP⟩:= readsX _ F₀ g hE (⟨(0,1),by decide⟩:PlaqAxes) hy hg hp hx₀ hd hC (fun y k=> hr y (hr'.trans k))
   let L:=fun i=> g.costP i+N*Y' i
   refine ⟨S,g,P₀,L,P,hg,fun k=>?_⟩; obtain ⟨A,W,V₀,X,hQ⟩:= evoke T' B F₀ g _ (hP k) (fun i hi=> hPw _ _ _ hi (hP k).tale) hk
   refine ⟨A,W,V₀,X,hQ,fun i hi=> ⟨(firms _ _ _ X hQ hk hN i hi).1,(firms _ _ _ X hQ hk hN i hi).2,?_⟩⟩
   have hX': B.n k=B₀*J.L^(k₀+k):= calc
      _ = _ := hT k
      _ = _ := by rw [hX,hk₀,mul_assoc,pow_add]
   have hε:towerQ J B n n k=finC J B 0 k:=by unfold towerQ; rw [feetM,Nat.sub_self]
   have h₁ : TokenZ (τ':=τ) (P':=P) (X:=P₀) (V:=A) (U:=W) (x:=x) B F₀ g X n (expo U (finC J B 0 k)):= (congr_arg (expo U) hε) ▸ (shipped B F₀ g X hQ hJ hZ hX'.symm hn hg hN hk hψ)
   obtain ⟨hD,H⟩:= empowered B F₀ g X hQ hE hg hψ hk hN _ _ _ (fun _=> Real.exp_pos _) (hΓ B k) (he' B k) h₁ hi
   refine ⟨hD,fun j hp=> prairieR B F₀ g X hQ hE hg hψ hk hN h₁ _ _ _ (hΓ B k) (he' B k) (by omega) hp,fun V=> (H V).trans_eq ?_⟩
   congr 1; unfold TourV; rw [show towerQ J B n i k=finC J B (n-i) k from (by unfold towerQ; rw [feetM])]; unfold expo; rw [mul_sub,Real.exp_sub]
variable (χ:Chi)
include χ
lemma gemsIV (h:N ≤ 8)(he:Even N)(K:KernelChoices): ∃ (T': Teller su), T'.bind=K ∧ T'.top.supportExponent=2 ∧ T'.top.clip.direct≤1∧∃ (Q:ConnectedActivityE6.Target su T')(s t D:ℝ)(m:ℕ), s=T'.top.width ∧t ≤T'.top.paths∧ 0 ≤ D∧512 ≤ m ∧∀ J:Patch,J.J=4→ J.Branches K su→ m ≤J.L.val→ 2*(D+3) ≤ subG N*Real.log J.L.val∧ PanelsIV J F₀ Q s t D:=by
    obtain ⟨T,hk,hδ,hV,Q,s,t,D,m,h0,h1,h2,h3,h4⟩:= canopyIR F₀ χ (le_refl 4) K h; obtain ⟨r,p,H⟩:=Globe.coreP (passportM 4 le_rfl) F₀
    subst K; refine ⟨T,rfl,hδ,hV,Q,s,t,D,max m r,h0,h1,h2,h3.trans (le_max_left ..),fun J hv hp hx=>?_⟩; have hh:= h4 J hv hp ((le_max_left ..).trans hx); exact ⟨hh.1, optic F₀ hV hδ h0.symm h1 hh.2 h2 hh.1 hp he hv (by omega) (fun c hθ=> H J.L c ((le_max_right ..).trans hx) J.odd_side (by omega) hθ)⟩
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.gemsIV
