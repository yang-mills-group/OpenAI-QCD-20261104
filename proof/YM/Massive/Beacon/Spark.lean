import YM.QCD.Disc.Pre
import YM.Massive.Horizon.Castle
/-! # Heritage budget made available at fixed pre-budget sizes via the boosted port. -/
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
open Footprint Push.Local
variable {t :ℝ}
lemma fillF {g:I→ℝ}{k:J'→ℝ} {X:Rise f N I J'} (hp:Cents X g k t W)(he:Fill X g k v v A u M i)(hf:q≤v)(hQ:0≤q): Fill X g k q q A u M i:=by
     refine ⟨hQ,he.cap,fun i' => budget_mono (he.χ i') (fun i=>?_) (fun i=>?_),fresh _ _ he.ε hf (fun i=>mul_nonneg (hp.non i) (pow_nonneg he.cap _))⟩
     · split; exact mul_nonneg (hp.pos _) (Real.exp_pos _).le; exact le_rfl
     split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hf (by positivity))) (hp.pos _)
     exact le_rfl
-- sidetask. stored as EXISTS even though in fact same Libretto. Retain A3 quote in budgets. Matter label underges. Trace reused only for the Boot0.Schedule. For Hearth property Marquee.R build from SparkRec.Inc convene respects ALL Loot inputs.`Silo` pack etc at same p.
variable {p' U₁ :ℝ} {M':ParcelR}{U':SunR M'}
structure BeamBeacon (A3:ℝ)(P₀:Plan j)(τ:Policy Q G N)(χ:Chi)(B: Badge P₀ τ R P o χ T U' w x q M μ Y)(p: duskM (h:=h) P₀ U' τ x w)(Γ: Silo c):Prop where
    lit (I J:Type)[Countable I][Countable J](X:Rise f N I J)(w':I→ℝ)(g:J→ℝ) (h₁:Cents X w' g (fan S.L τ.t x) R.threshold)(h₂:Fill X w' g (1/16) (1/16) (taxK S.L x 1) 1 (Jets.Touch.chip S.L x) (highR S.L x)) (h₄:X.Wave R.threshold)(h₅:X.Reframe) :
      PortSparse S K h B.Pq B.D p X Γ τ.t (wage S.L τ x) (τ.alpha+1) ∧ Gosh (tableau S h K X B.Pq B.D p Γ) χ (τ.alpha+1) (wage S.L τ x) P.order P.power ∧ (∀ (i:I→Bool), (∀ j, Spice.Worth X j R (fan S.L τ.t x) (w' j) ∧ (Nonwrapping (X.row j).support (X.row j).site → Dust.Fleck R (X.row j).support (X.row j).site (i j) (X.main j) (fan S.L τ.t x) (w' j))) → ∃ (U₀:Libretto su T'.below.order)(U₂:Hera.Rights su T'.below.order)(Vₐ:ℝ), Warmlet.Boost S h K B.D B.Pq X (united (VarnC B.Pq p N) (sailP B.Pq Γ N)) U₀ U₂ Vₐ w' i B.Vq χ P (wage S.L τ x) τ.alpha (τ.price*Jets.Touch.chip S.L x) ∧ Capstone S.L (Q.halo+8) P.power (1/16) τ.alpha (A3*Brick.fern S.L) U₀ U₂ Vₐ ∧ radiusB x+1 ≤ R.B+R.B ∧ R.B ≤ 2*radiusB x)
structure SparkRec (A3:ℝ)(P₀:Plan j)(τ:Policy Q G N)(χ:Chi)(B: Badge P₀ τ R P o χ T U' w x q M μ Y): Prop where
    poll (p:duskM (h:=h) P₀ U' τ x w)(Γ:Silo c)(X:BankP c) (hR:Run.Pack id id τ.η (Policy.ξP Q) τ.j (wood P₀ 0 S.land) τ.p Γ X)(hD:Torch Γ): BeamBeacon A3 P₀ τ χ B p Γ
structure CedarX (A3:ℝ)(P:Plan j)(U:Libretto su T'.below.order) (Ξ:ℝ)(D:Heir.Record) (Q:ConnectedActivityE6.Target su T') (J:Patch)(X:ParcelR)(t W μ C:ℝ) (o:Target.Order su W)(χ:Chi) (τ:Policy Q T'.top N):Prop where
  law:0<τ.η
  wool:0 ≤ τ.X.c
  fareP :0 < τ.X.r
  gamma (c:Side) (Z:Train j):∃ (Γ:Silo c)(Y:BankP c), Torch Γ ∧ Run.Pack id id τ.η (Policy.ξP Q) τ.j (wood P 0 Z) τ.p Γ Y
  lit :∀ᶠ x in atTop,0 < lowK J.L x T'.top.supportExponent ∧∀ (B B':BudgetPoint), Kites.Now J.L B T'.top x→ B'.B=radiusB x→Same T'.below B' → ∀ (Z:SunR X)(c f:Side)(S:Flight j j)(K:KernelChoices)(h:f.val=c.val*S.L.val)(Y:Tube su (S.visit K h)), Plays U D B' B T' Y x→ S.L=J.L→ (S.visit K h).patch=J→2*(radiusB x+1)<f.val→ Works T' J.L x (S.visit K h) Y →SliceRows.Stamp Y→ Y.up.Bounds Y.high T'.top.width T'.top.paths (loopBill su J.L x)→∀ m β,|m|≤wink J.L x → betaF su x J.L/2 ≤ β → β ≤ 2*betaF su x J.L → ∃ M:Badge P τ B B' o χ Y Z m x t β μ C,SparkRec A3 P τ χ M
-- caps before or after
variable {ε C' σ' A' s:ℝ}(Q:ConnectedActivityE6.Target su T')
set_option maxHeartbeats 800000 in
lemma coolantX (P:Plan j)(U:Libretto su T'.below.order) (hJ:4 ≤ j)(hQ:0≤α)(he:(α+1)+1+1≤Q.exp)(hq: Q.rate≤-(3/8:ℝ)) (N:ℕ)(ht: (1/16:ℝ) ≤ t)(hv:1 ≤ v)(ha:0<a)(hx:a < 1/8) (hε:0<ε) (χ:Chi)(_hm:T'.top=T'.below) :∃ (A3:ℝ)(n:ℕ),0≤ A3∧∀ L:Side,n ≤ L.val →∀ᶠ W:ℝ in atTop,∃ μ,0<μ∧∀ J:Patch,J.Branches T'.bind su → J.J=j → J.L=L →∀ D:Record,D.ε≤1/4 →∀ (V:ParcelR)(η:ℝ),Rates V η → ∃ (C:ℝ)(o:Target.Order su W)(τ:Policy Q T'.top N), τ.alpha=α ∧ τ.price=ε ∧ τ.t=a ∧ τ.k=v∧ CedarX A3 P U C D Q J V t W μ C o χ τ:=by
   obtain ⟨ηP,A,p,hvP,H,hZ⟩:= Loom.banner P (Policy.ξP Q) (Policy.ξP_pos Q).le -- order
   obtain ⟨K'⟩:=Hera.authority su T'.below.order
   obtain ⟨Va,A3,n,hA,h⟩:= Loom.summitR Q P P A p ηP hvP H α hq T'.below.order T'.below.power χ hQ he hJ hJ N a 1 v (1/16) ε U K' (by have h:= T'.below.order_ge; omega) ha hx zero_lt_one (by norm_num) hv hε
   refine ⟨A3,n,hA,fun L hl=>?_⟩
   filter_upwards [h L hl] with W hW; obtain ⟨hp0,μ,hμ,hp⟩:=hW
   refine ⟨μ,hμ,?_⟩; intro Hq hD hL hL' D hd V Y hT; obtain ⟨o,C,H⟩:= hp Hq hD hL' hL D hd
   obtain ⟨r,z,σ,B,Y',v₁,t',b,hr,hY⟩:= H V.r V.s V.t V.c V.d (QCD.Smoke.expPrice 2 V.t*V.e) hT.hr hT.hs hT.ht hT.hc hT.hd -- blank infer?
   let τ: Policy Q T'.top N:=⟨A,p,ηP,α,ε,a,v,⟨t',b,r,z,σ,1,B,Y',v₁⟩⟩
   refine ⟨C,o,τ,rfl,rfl,rfl,rfl,hvP,by norm_num [τ],hr,fun c Z=>?_,?_⟩
   · obtain ⟨Γ,S,hS,hU⟩:= candor (hZ c Z); exact ⟨Γ,S,hU,hS⟩
   subst L; filter_upwards [hY] with x hx₀; refine ⟨hx₀.1,?_⟩; intro B₀ B₁ hX hB hz Z c f S K H' T hU hM hY hF hL hT' hP m β hv hC he
   rw [← hM] at hx₀
   obtain ⟨⟨⟨Yv,hΥ⟩⟩,⟨Y₁⟩,⟨hq⟩,X',V',hx⟩:= hx₀.2 Z.X Z.Y Z.Z.page (Z.Z.cost hT.ht) (Z.Z.permit hT.ht).2 c f S H' K B₀ m β 0 T rfl hY hF (hM.symm ▸ hL) hT' (hM.symm ▸ hX.baseG) (hM.symm ▸ hX.ball) hX.era.2.2 (hM.symm ▸ hP) (hM.symm ▸ hC) (hM.symm ▸ he) (hM.symm ▸ hv)
   -- issue.E q, rewrite S.L. Need rebase Badge dependencies. `hM` definitional? S generic; sunset aux distort. handle subst=h' s? From pack operation. use trick hY target: cast x before with lift.W.. 
   have h₀: Sponsor T P τ Z B₁ B₀ χ x t m β X' V':=by
      constructor; intro D J G W hD hT hQ I J₀ hi hj P' g d he
      obtain ⟨hY',hPor,hG,hH⟩:= hx D J hD G W hQ hT P' g d he.centsP (fillF he.centsP he.fillP ht (by norm_num)) he.waveP he.pan.refr
      refine ⟨hPor he.pan,?_,(hH B₁ hB hz.1 hU).1 he.pan⟩; simp_rw [hz.1,hz.2.1]; exact hG
   let B:= Badge.mk (P₀:=P) (τ:=τ) (R:=B₀) (P:=B₁) X' V' hq Yv hΥ Y₁ h₀
   refine ⟨B,⟨fun p Γ H hQ hD=>?_⟩⟩; constructor; intro I J' hI hJ' X g k he hΨ hρ hRe; obtain ⟨h1,h2,h3,h4⟩:= hx Yv p hΥ Γ H hQ hD X g k he hΨ hρ hRe
   refine ⟨h1,?_,?_⟩
   · simp_rw [hz.1,hz.2.1]; exact h3
   intro U' hw; obtain ⟨-,hp,hC,hE,hF⟩:= h4 B₁ hB hz.1 hU; exact ⟨U,K',Va,hp U' hw,hC,hE,hF⟩
end YM.QCD.Acre
#print axioms YM.QCD.Acre.coolantX
