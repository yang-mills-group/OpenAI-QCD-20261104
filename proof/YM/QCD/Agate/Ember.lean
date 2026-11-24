import YM.QCD.Agate.Concur
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
open Tide
-- variable look compatibility: does not presume sequential all bounded Borel
variable (hB:Even (B.n 0).val)(hE:∀ i,B.n i=B.n 0*O.L^i)
variable {D':Lot}
variable (Ω':Ultrafilter ℕ)(he:(Ω':Filter ℕ)≤ atTop)
lemma food (i k:ℕ)(H:Wings O B i k D')(hk: O.Branches K su) (x:Malt D' N)(T W:ℕ→ℝ)(u v:ℝ)(ht:Tendsto T (Ω': Filter ℕ) (𝓝 u))(hV:v≠0)(hw:Tendsto W (Ω':Filter ℕ) (𝓝 v)):
  ∃ (f:ℕ→ℝ),Tendsto f (Ω': Filter ℕ) (𝓝 0) ∧∀ j:ℕ, Coast (f j) (soared B H K hk (T j) (W j) x-soared B H K hk u v x):=by
   let c:=finC O B i k; let A:= finC O B (i+1) k; let V(p q:ℝ):= soared B H K hk p q x; let L:=Agate.visit (origin A) (D:=rimH D' O) (F:=N); let Y:= Agate.visit (origin c) x
   obtain ⟨g,hg,hG⟩:= loomed (P:=Pike O 0) (powerV B O i k) Y (palps _ x).hp _ _ ht hV hw hk
   let F:= ((Agate.gather (pens (D:=rimH D' O) (F:=N) (origin A))).toLinearMap.toContinuousLinearMap)
   have hx(P:Malt (rimH D' O) N)(p:Trace (rimH D' O)): F (L P (starlet (origin A) p))=P.val p:= by change _ = _; unfold F L; change Agate.gather _ (pass _ (P.val (crest _ _)))= _; rw [spar (origin A) H.large p, garner (origin A) H.large]
   refine ⟨fun i=> ‖F‖*g i,by simpa only [mul_zero] using hg.const_mul ‖F‖,fun j U=>?_⟩; rw [← hx]; apply (F.le_opNorm _).trans; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
   have hy(T Z:ℝ): L (V T Z)= Tide.look (Pike O 0) K (powerV B O i k) T Z (Agate.visit (origin (finC O B i k)) x):= (flying B hk H H T Z x).symm
   change ‖L (V _ _-V _ _) _‖ ≤ _; rw [map_sub, hy,hy,Pi.sub_apply]; exact hG _ _
lemma songD (A:Lot)(p q:Malt A N)(i k:ℕ)(hx:Continuous (X₀ i k)): songR B X₀ A (p-q) i k = songR B X₀ A p i k-songR B X₀ A q i k:=by
    unfold songR Tide.fresh; simp only [map_sub,Pi.sub_apply,mul_sub]; apply MeasureTheory.integral_sub
    · exact ((((Tide.stays ((Cove.lightC _).comp hx))).mult (palps _ p).hp).flows ((ber _).continuous_of_finiteDimensional)).intg _
    exact ((((Tide.stays ((Cove.lightC _).comp hx))).mult (palps _ q).hp).flows ((ber _).continuous_of_finiteDimensional)).intg _
variable (V M' W₀:ℕ→ℝ)(X:ℕ→ScaleF N)(hV:Skates B Y U W X₀ Ω' V M' W₀ X)
include hh hB hE he hV
lemma warm (i:ℕ)(p : Malt D' N)(h : O.Branches T'.bind su)(q : Malt (rimH D' O) N)(hZ:0<Z i)(ht:TrackF O T'.bind B (V (i+1)) (W₀ i) i p q): (X i).mass D' p= (X (i+1)).mass _ q:=by
   obtain ⟨K,hK⟩:= (flightH B hB hE D' i).exists
   let T₀(k:ℕ):=Y (k+1-(i+1)) k; let T₁(k:ℕ):= W (k+1-(i+1)) k; let Q₀:=fun k:ℕ=>soared B hK _ h (T₀ k) (T₁ k) p
   have hv:0 < W₀ i:= hZ.trans_le ((leapJ B b' Y U W T X₀ M Z hh Ω' he V M' W₀ X hV).2.2 i).2.2.2.1
   obtain ⟨g,hg,hG⟩:=food B Ω' i K hK h p T₀ T₁ _ _ ((continuous_fst.tendsto _).comp (hV.stature (i+1))) hv.ne' ((continuous_snd.tendsto _).comp ((continuous_snd.tendsto _).comp (hV.stature i)))
   let S:=rimH D' O; obtain ⟨w,hw,H⟩:= sine B b' Y U W T X₀ M Z hh hB hE S (i+1)
   have hp:=flightH B hB hE D' i
   rw [unic B p (soared B hK T'.bind h _ _ p) q (V (i+1)) (W₀ i) (hp.mono fun k hj=> flying B h hK hj _ _ p) ht] at hG
   let f₀:= fun k=>songR B X₀ _ p i k; let f₁:=fun k=>songR B X₀ _ q (i+1) k
   have hz:∀ᶠ k in atTop, ‖f₀ k - f₁ k‖ ≤ w*g k:=by
       filter_upwards [hp,H,eventually_ge_atTop i] with k hx hX hk; have hi:i<k+1:=by omega
       obtain ⟨hu,hL,hM⟩:= (hh.candor k).vocals i hi; have hc:=((hh.candor k).capital (i+1) hi).1
       have HH:f₀ k =songR B X₀ _ (Q₀ k) (i+1) k:=by
          change Tide.fresh (X₀ i k) _=Tide.fresh _ _; change _= Tide.fresh _ (Agate.visit _ (soared B hK T'.bind h (T₀ k) (T₁ k) p)); rw [← flying B h hK hx (T₀ k) (T₁ k) p]; exact pov (Pike O 0) (powerV B O i k) _ _ h (hZ.trans_le hL) hM (Agate.visit _ p) (palps _ p).hp hc
       rw [HH]; change ‖songR B X₀ _ (Q₀ k) _ k - songR _ _ _ q _ k‖ ≤ _; rw [← songD B X₀ _ (Q₀ k) q (i+1) k hc]; exact hX _ (g k) (hG k)
   have hT:= ((hV.mass i _ p).sub (hV.mass (i+1) _ q)).norm; let a := ‖(X i).mass _ p-(X (i+1)).mass _ q‖; have hi:a ≤ w*0:= le_of_tendsto_of_tendsto hT (hg.const_mul w) (he hz); rw [mul_zero] at hi; exact sub_eq_zero.mp (norm_le_zero_iff.mp hi) -- syntax
end IV
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.IV.warm
