import YM.Mills.Buds
import YM.VStages.Precedence
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
namespace Stratum.MarchQ
open Rails
variable (χ:Chi)(F₀:Flavor N)
lemma beyondV (B:Teller su) (hkP:B.below.order≤B.top.order) (hp:B.below.power≤B.top.power)(hBT:B.below.supportExponent=B.top.supportExponent)(hΩ:1≤B.C)(hv:B.below.supportExponent=2)(hD:B.below.clip.direct≤1)(a s D γ:ℝ)(hx:B.below.width=a)(hk:s≤ B.below.paths)(hz:0 < γ) (hj:B.j=j)(he:4 ≤ j)(vwidth vpower:ℝ)(hAB:B.top.width=vwidth)(hBq:vpower≤B.top.paths)(k0:ℕ)(st:4≤k0)(hV:Font B.below.order u w v (1/2))(hq:w<1/8) (J:Plan j)(J':Plan k0) :∃ (A3 a3 a4 h κ Z X:ℝ)(Q:ConnectedActivityE6.Target su B)(n:ℕ),0≤A3 ∧ 0<a3 ∧ 0<h ∧ 0<κ ∧
    ∀ tol:ℝ,0<tol→∀ S:Flight j k0,S.patch.Branches B.bind su→ n ≤ S.L.val →∀ (η M σ Λ α:ℝ),0<η→0<M→ 1 ≤ Λ →0<α→∀ (p:ParcelR),p.Rates B.η→∃ (W C μ:ℝ)(o:Target.Order su W)(l k' n' m:ℕ)(τ:Policy Q B.below N), MicroPay τ μ a3 a4 ∧ τ.t=w ∧ 0 < τ.η ∧ (∀ᶠ x in atTop, VoucherSet J J' Q S.patch p W μ C o χ τ x) ∧(∀ Jq Kq:ℕ,∀ᶠ x in atTop,VoucherInk J J' Q S.patch p W μ C o χ τ Jq Kq x) ∧(∀ᶠ x:ℝ in atTop,Tall S.patch Q.halo l k' n' m x)∧∀ᶠ x in atTop, ScreenBeam τ J J' S F₀ p a s vwidth η vpower x B.C Λ B.η (1/8) σ γ D h κ l k' n' m χ o α M μ C (betaFare S.L D) X Z tol A3:=by
   let θ:=w
   obtain ⟨U,hU,hW,n,H⟩:=heraldW B B.η B.C B.width hΩ hkP hp -- field? check
   obtain ⟨i,Y,M,u,v,k,h,hi,hY,hMstored,hh,hC⟩:=astronomy J J' N 0 B.below he st
   have hθ:=hV.1
   obtain ⟨G,K,ν,ε,hG,hK,hν,hε,h'⟩:=appalV B.below J J' 1 θ h N hh zero_lt_one hθ (by rw [hv]; norm_num) he st hD
   let z:=turnCost B.below.order B.below.power; have hz':0<z:=by unfold z turnCost; positivity
   let r:=ε/(2*z); have hr:0<r:=by unfold r; positivity
   obtain ⟨Q,A,hA,hP,hQ,hL,hR,hS⟩:=atlasQ B 1 zero_le_one
   rw [← hBT] at hL hS
   obtain ⟨A3,l,hξP,ht⟩:=restartV Q J J' U he st hA hP hQ N (by norm_num : (1/16:ℝ)≤1/8) (earns N) hθ hq hr χ
   refine ⟨A3,r,A,h,ν,G,K,Q,max n l+512,hξP,hr,hh,hν,fun tol hΔ S hp' hι η M₁ σ W' α hη hB hW' hα p hm=>?_⟩
   let E:=S.patch; have hE : E.J=j:=rfl
   have hp₁:= hC S; change _ ≤ E.L.val at hι
   obtain ⟨y,hy⟩:= H E hp' (by omega)

   obtain ⟨W,μ,hμ,H⟩:= (ht E.L (by omega)).exists
   obtain ⟨C,o,τ,hu,hr',hτ₁,hτ₂,hΦt,hτ⟩:=H E hp' rfl rfl y hy.litL p B.η hm
   obtain ⟨A',u₁,Y₁,d₁,ht₁,hZ⟩:=eraρ hm.hr B.below 1 N 0; obtain ⟨K₁,u₂,Y₂,d₂,ht₂,hZ'⟩:=eraρ hm.hs B.below 2 N 0
   obtain ⟨M0,h₀⟩:= h' E.L (by omega) α μ p.r p.c p.s p.d tol hΔ hα hμ hm.hr hm.hs
   obtain ⟨Zq,l,m,hm',hM⟩:= highest E Q.halo M0 (by omega)
   refine ⟨W,C,μ,o,Zq,l,m,M0,τ,⟨hτ₁.symm ▸ hθ,hτ₁.symm ▸ hq,hτ₂,hr',hu,hu.symm ▸ hL,hu.symm ▸ hS,hμ,hτ.first,hτ.fareP⟩,hτ₁,hτ.law,hΦt,hτ.marked,hM,?_⟩
   have hz₀ := stationBeam J F₀ U J' S τ o χ (betaFare E.L D) hp₁ y hy hD hτ hB (hU.symm ▸ hm) U.width (hr'.symm ▸ hr) hμ hτ₂ (hτ₁.symm ▸ hV) (by norm_num) (hτ₁.symm ▸ (by linarith : 2*w < (1/2:ℝ))) hν hU.symm hW.symm hp' hj hAB hBq hx hk st hW' hα (by norm_num : (0:ℝ)<1/8) hMstored hY hz hi (hZ p.c) (hZ' p.d) ht₁ ht₂ (hu.symm ▸ hL) (hu.symm ▸ hR) (hu.symm ▸ hS) (D:=D) (show _ ≤ ε from (by change 2*z*τ.price≤_; rw [hr']; unfold r; field_simp; rfl)) (Z:=G) (A':=K) (by rw [hτ₁]; exact h₀.mono fun i hi c f p S V ht hp hc hP hV W W'=>hi _ _ _ _ _ _ ht hp hc hP hV W W') hm' hM (η₀:=η) (t:=σ) -- edit duplicated he
   rw [hU,hW] at hz₀; exact hz₀
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.beyondV
