import YM.QCD.Agate.Limbs
import YM.QCD.Corn.Green
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
open Rain PulseRide
variable {O:Patch} {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{U V Wv Y:ℕ→ℝ}
variable {τ':Policy Q T'.top N}(B:SparkMesh){S':ℕ→SparkMesh}(b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n)
variable {T₁:ℕ→Towers O.L}{V₁:ℕ→Bed}{b₀:ℕ→ℝ}
variable (A0:∀ i,Pixel (towerQ O B n i k) N) (hG: Stargate T' B b' g P' X Y κ x τ'.t D W' k V U Wv A0)
namespace IV
open Globe
open Land Plum Agate
variable (Y U W T:ℕ→ℕ→ℝ)(X₀:∀ i k:ℕ,Pixel (finC O B i k) N)(M Z:ℕ→ℝ)(hh:Evokes Q b' O a d D B Y U W T X₀ M Z κ x τ')
noncomputable def origin (c:Side):Site c:=fun _=> (c.val/2:ℕ)
lemma finH (P:Patch)(i:ℕ):Tendsto (fun k=> (finC P B i k).val) atTop atTop:=by
   exact Filter.tendsto_atTop_mono' atTop (Eventually.of_forall fun k=>Nat.le_mul_of_pos_right (B.n k).val (P.L^i:Side).property) B.cofinal
variable (hB:Even (B.n 0).val)(hE:∀ i,B.n i=B.n 0*O.L^i)
include hB hE
lemma finEv(i k:ℕ): Even (finC O B i k).val:=by unfold finC; rw [hE k,PNat.mul_coe, PNat.mul_coe]; exact Even.mul_right (Even.mul_right hB _) _
omit hB hE
noncomputable def songR (s:Lot)(p:Malt s N)(i k:ℕ):ℂ:= Tide.fresh (X₀ i k) (Agate.visit (origin _) p)
structure ScaleF (F:ℕ) where
   mass(A:Lot): Malt A F→ₗ[ℂ]ℂ
   coast(A:Lot): ∃ v:ℝ,0≤v∧∀ (p:Malt A F)(u:ℝ), Coast u p→ ‖mass A p‖≤v*u
   withL{A G:Lot}(h:A⊆G)(p:Malt A F): mass G (wheel h p)=mass A p
   port(A:Lot):mass A 1=1
include hh hB hE
lemma sine (s:Lot)(i:ℕ):∃ K:ℝ,0≤ K∧∀ᶠ k in atTop,∀ (p : Malt s N) (u:ℝ), Coast u p→ ‖songR B X₀ _ p i k‖≤K*u:=by
    obtain ⟨V,hv,hP⟩:= ner s (finC O B i) (finH B O i) (finEv B hB hE i) (M i) O N
    refine ⟨V,hv,?_⟩; filter_upwards [hP,eventually_ge_atTop i] with k h hk p u hu; have hx:i≤k+1:=by omega
    obtain ⟨hc,hL,hQ,hX,H⟩:=(hh.candor k).capital i hx; exact h _ _ (hh.ocean k i hx) hc hQ hX p u hu
variable (Ω':Ultrafilter ℕ)(he:(Ω':Filter ℕ)≤ atTop)
include he
omit hh hB hE in
lemma mantic {X:Type*}[TopologicalSpace X](F:Set X)(hp:IsCompact F)(f:ℕ→X)(h:∀ᶠ i in atTop,f i∈ F): ∃ x∈F,Tendsto f (Ω':Filter ℕ) (𝓝 x):=by
     have he: ∀ᶠ i in Ω', f i∈F:=he h -- prop filter?
     have H: Ultrafilter.map f Ω' ≤ 𝓟 F:= (le_principal_iff).2 he
     exact (isCompact_iff_ultrafilter_le_nhds.mp hp) (Ultrafilter.map f Ω') H -- syntax
lemma spot (i:ℕ):∃ V:ScaleF N,∀ (S:Lot)(x:Malt S N),Tendsto (fun k=>songR B X₀ _ x i k) (Ω': Filter ℕ) (𝓝 (V.mass _ x)):=by
    choose V hV hv using fun S=> sine B b' Y U W T X₀ M Z hh hB hE S i
    have ht (S:Lot)(p:Malt S N):∃ z:ℂ,Tendsto (fun k=>songR B X₀ _ p i k) (Ω':Filter ℕ) (𝓝 z):=by
        obtain ⟨u,hu⟩:= (staysP p).bounded; obtain ⟨z,-,H⟩:= mantic Ω' he (Metric.closedBall (0:ℂ) (V S*u)) (isCompact_closedBall ..) (fun k=>songR B X₀ _ p i k) ((hv _).mono fun k h=>Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact h p u hu)); exact ⟨z,H⟩
    choose w H using ht; have hv': ∀ᶠ k:ℕ in (Ω':Filter ℕ),i ≤ k+1:= he ((eventually_ge_atTop i).mono fun k h=>by omega)
    have ha(S:Lot)(x y:Malt S N) : w S (x+y)=w S x+w S y:=by
         apply tendsto_nhds_unique (H _ _) (((H S x).add (H S y)).congr' (hv'.mono fun k h=> ?_)); change songR B X₀ S x i k + songR B X₀ S y i k=songR B X₀ _ (x+y) i k; unfold songR; rw [map_add]; exact (Plum.spell ((hh.candor k).capital i h|>.1) (palps _ x).hp (palps _ y).hp).symm
    have hq(S:Lot)(x:Malt S N)(t:ℂ):w S (t • x)= t • w S x:=by
         apply tendsto_nhds_unique (H _ _) ((tendsto_const_nhds.smul (H S x)).congr fun k=>?_); change t • songR B X₀ _ x i k=songR B X₀ _ (t • x) i k; unfold songR; rw [map_smul]; exact (Plum.spend _ _).symm
    let V' (S:Lot): Malt S N→ₗ[ℂ]ℂ := { toFun:=w S, map_add':=ha S, map_smul':=fun z x=> hq S x z }
    refine ⟨⟨V',fun S=>⟨V S,hV S,fun p u h=> le_of_tendsto (H _ p).norm (he ((hv _).mono fun k h'=> h' p u h))⟩,?_,?_⟩,H⟩
    · intro A S h p; refine tendsto_nhds_unique (H _ _) ((H _ p).congr fun k=> ?_); change songR B X₀ A p i k=songR B X₀ S (wheel h p) i k; unfold songR; rw [wheeling]
    intro A; refine tendsto_nhds_unique (H _ _) (tendsto_const_nhds.congr' (hv'.mono fun k h=>?_)); change 1=songR B X₀ A 1 i k; unfold songR; rw [map_one,Plum.fresh1]; exact ((hh.candor k).capital i h).2.2.1.symm
end IV
end Rails
end YM.QCD.Acre
