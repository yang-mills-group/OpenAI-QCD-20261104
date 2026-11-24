import YM.Mural.PithQ
import YM.Mills.Buds
import YM.Mills.Evert
import YM.VStages.Coolant
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
variable {S:Flight j k}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local
variable {t :ℝ}
variable {p' U₁ :ℝ} {M':ParcelR}{U':SunR M'}
abbrev MarketSet (P:Plan j)(Pr:Plan k)(Q:ConnectedActivityE6.Target su T')(J: Patch)(X:ParcelR)(W μ C:ℝ)(o:Target.Order su W)(_χ:Chi)(τ: Policy Q T'.below N) (x:ℝ):= LicenseQ Q P Pr J.L W μ J o C X.r X.s X.t X.c X.d (QCD.Smoke.expPrice 2 X.t*X.e) τ.t τ.k ((1/16)/2) τ.X.c (τ.alpha+1) τ.X.r τ.X.b τ.X.a τ.X.Q τ.X.Y τ.X.w τ.η τ.p τ.j τ.X.i τ.X.j N x
-- caps before or after
variable {ε C' σ' A' s:ℝ}(Q:ConnectedActivityE6.Target su T')
set_option maxHeartbeats 800000 in
lemma alleyO (P:Plan j)(Pr:Plan k)(U:Libretto su T'.below.order) (hJ:4 ≤ j)(hJ₂:4 ≤ k)(hQ:0≤α)(he:(α+1)+1+1≤Q.exp)(hq: Q.rate≤-(3/8:ℝ)) (N:ℕ)(ht: (1/16:ℝ) ≤ t)(hv:1 ≤ v)(ha:0<a)(hx:a < 1/8) (hε:0<ε) (χ:Chi) :∃ (A3:ℝ)(n:ℕ),0≤ A3∧∀ L:Side,n ≤ L.val →∀ᶠ W:ℝ in atTop,∃ μ,0<μ∧∀ J:Patch,J.Branches T'.bind su → J.J=j → J.L=L →∀ D:Record,D.ε≤1/4 →∀ (V:ParcelR)(η:ℝ),Rates V η → ∃ (C:ℝ)(o:Target.Order su W)(τ:Policy Q T'.below N), τ.alpha=α ∧ τ.price=ε ∧ τ.t=a ∧ τ.k=v∧ (∀ᶠ x in atTop,VoucherSet P Pr Q J V W μ C o χ τ x) ∧ (∀ᶠ x in atTop,MarketSet P Pr Q J V W μ C o χ τ x) ∧ CedarQ A3 P Pr U C D Q J V t W μ C o χ τ:=by
   obtain ⟨ηP,A,p,hvP,H,hZ⟩:= Loom.banner Pr (Policy.ξP Q) (Policy.ξP_pos Q).le -- order
   obtain ⟨K'⟩:=Hera.authority su T'.below.order
   obtain ⟨Va,A3,n,hA,h⟩:= Loom.mountsV Q P Pr A p ηP hvP H α hq T'.below.order T'.below.power χ hQ he hJ hJ₂ N a 1 v (1/16) ε U K' (by have h:= T'.below.order_ge; omega) ha hx zero_lt_one (by norm_num) hv hε
   refine ⟨A3,n,hA,fun L hl=>?_⟩
   filter_upwards [h L hl] with W hW; obtain ⟨hp0,μ,hμ,hp⟩:=hW
   refine ⟨μ,hμ,?_⟩; intro Hq hD hL hL' D hd V Y hT; obtain ⟨o,C,H⟩:= hp Hq hD hL' hL D hd
   obtain ⟨r,z,σ,B,Y',v₁,t',b,hr,hΦq,hMar,hNq,hY⟩:= H V.r V.s V.t V.c V.d (QCD.Smoke.expPrice 2 V.t*V.e) hT.hr hT.hs hT.ht hT.hc hT.hd -- blank infer?
   let τ: Policy Q T'.below N:=⟨A,p,ηP,α,ε,a,v,⟨t',b,r,z,σ,1,B,Y',v₁⟩⟩
   refine ⟨C,o,τ,rfl,rfl,rfl,rfl,(by subst L; exact hΦq),(by subst L; exact hMar),hvP,by norm_num [τ],rfl,hr,fun c Z=>?_,?_,?_⟩
   · obtain ⟨Γ,S,hS,hU⟩:= candor (hZ c Z); exact ⟨Γ,S,hU,hS⟩
   · subst L; exact hNq
   subst L; filter_upwards [hY] with x hx₀; refine ⟨hx₀.1,?_⟩; intro B₀ B₁ hX hB hz Z c f S K H' T hU hM hY hF hL hT' hP m β hv hC he
   rw [← hM] at hx₀
   obtain ⟨⟨⟨Yv,hΥ⟩⟩,⟨Y₁⟩,⟨hq⟩,X',V',hx⟩:= hx₀.2 Z.X Z.Y Z.Z.page (Z.Z.cost hT.ht) (Z.Z.permit hT.ht).2 c f S H' K B₀ m β 0 T rfl hY hF (hM.symm ▸ hL) hT' (hM.symm ▸ hX.baseG) (hM.symm ▸ hX.ball) hX.era.2.2 (hM.symm ▸ hP) (hM.symm ▸ hC) (hM.symm ▸ he) (hM.symm ▸ hv)
   -- issue.E q, rewrite S.L. Need rebase Manifest dependencies. `hM` definitional? S generic; sunset aux distort. handle subst=h' s? From pack operation. use trick hY target: cast x before with lift.W.. 
   have h₀: TaxW T P Pr τ Z B₁ B₀ χ x t m β X' V':=by
      constructor; intro D J G W hD hT hQ I J₀ hi hj P' g d he
      obtain ⟨hY',hPor,hG,hH⟩:= hx D J hD G W hQ hT P' g d he.centsP (fillF he.centsP he.fillP ht (by norm_num)) he.waveP he.pan.refr
      refine ⟨hPor he.pan,?_,(hH B₁ hB hz.1 hU).1 he.pan⟩; simp_rw [hz.1,hz.2.1]; exact hG
   let B:= Manifest.mk (P₀:=P) (τ:=τ) (R:=B₀) (P:=B₁) X' V' hq Yv hΥ Y₁ h₀
   refine ⟨B,⟨fun p Γ H hQ hD=>?_⟩⟩; constructor; intro I J' hI hJ' X g k he hΨ hρ hRe; obtain ⟨h1,h2,h3,h4⟩:= hx Yv p hΥ Γ H hQ hD X g k he hΨ hρ hRe
   refine ⟨h1,?_,?_⟩
   · simp_rw [hz.1,hz.2.1]; exact h3
   intro U' hw; obtain ⟨-,hp,hC,hE,hF⟩:= h4 B₁ hB hz.1 hU; exact ⟨U,K',Va,hp U' hw,hC,hE,hF⟩
end YM.QCD.Acre
#print axioms YM.QCD.Acre.alleyO
