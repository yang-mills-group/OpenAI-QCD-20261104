import YM.VStages.Icicle
import YM.VStages.ExposureY
import YM.VStages.Thin
import YM.Massive.Sharp.Spectrum
import YM.VStages.Yarn
import YM.VStages.RegisterY
import YM.VStages.Wardpost
import YM.VStages.Foster
import YM.VStages.PonderY
import YM.VStages.VistaW
import YM.Massive.Aperture.Calendar
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
namespace Stratum.MarchQ
open Rails
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor N}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
open MeasureTheory Rails.Reference Next.Rank IV Rain
open Finset NormedSpace Grass
open Cairn
open YM.Massive.Pressure (noiseZ)
open YM.SectorNext.Vacuum (rich spare)
variable {κ:ℝ}
open YM.Massive (transfer joint Density Regulator Stiffness.Window Scheme)
open Affair
namespace Melt
open Weft Fibre Sway OrbitG Conductor Conductor.Quant Struck Struck.Library Aperture -- Weft
variable {Pt:ℕ→BudgetPoint}{Δ:PlaqAxes}
variable (B:SparkMesh) (T:Affair P₀ A X B x n) (Z:Sheltered P₀ A X B T k Pt Δ)
set_option quotPrecheck false
local notation "Pq"=> J (A.level i)
local notation "S'"=> T.W.state
local notation "TZ"=> (P.stage (A.level i)).clip
local notation "Kz"=> K
variable (V U W:ℕ→ℝ)(F:∀ i,Pixel (A.ring (B.n k) i) N)
variable (hp:Tavern P₀ A X B T κ Z V U W F)(hX:entire P₀ A x Pt)(hc:Suburb.Calm P₀ A X x)
variable (E:RiseBook P₀)
open Rails.Kin Massive.Filament
variable (M₀:Arrow N) {M₃:ℝ} (he:Views P₀ A X E x)
variable (Y:Precinct P₀ A B k n) (hh: Keeps P₀ A X B T V W F Y)
local notation "ζi"=> (clockQ P₀ A x i)
local notation "θ₀"=> θ
local notation "Fz0"=>family P₀ A B Y
local notation "Fz"=>family P₀ A B Y M₀.tip


open Rails.Reference.Sharp Meridians Ruby High High.PrismT
open Massive.Pressure
variable {r:ℝ} (hs:Shot P₀ A X B T V U E M₀ Y Pt v r) {L1:HaarBudget su} {O:Paved P₀ A X x}(hO:Campus P₀ A X O B k n)
local notation "Yz"=>HatWalk P₀ A B Y
open Massive.Transfer
variable {W₀:ℕ→ℝ}
open scoped ComplexOrder

include hh
lemma volume_ray (hi:i < n)(q:Flavor N→ℝ)(v:ℝ)(s:ℂ) : Cvol (family P₀ A B Y q v i s)= (↑(Rain.gain (W i) (A.ring (B.n k) i) N):ℂ)* Cvol (family P₀ A B Y q v (i+1) s):=by
     have he : Massive.Transfer.growth (A.ring (B.n k) i) N (W i)=(↑(Rain.gain (W i) (A.ring (B.n k) i) N):ℂ):=(Complex.ofReal_pow ..).symm
     have ht:= trailPath P₀ A X B T V W F Y hh q v hi s
     change Massive.joint (Cove.light _ ∘ family P₀ A B Y q v i s)=_; rw [ht,Massive.Transfer.conserves (P:=A.flight i) _ _ _ _ (A.ticket i).owns _ (Massive.Transfer.soften_pay _ _ ((Cove.lightC _).comp ((show Continuous (family P₀ A B Y q v (i+1) s) from (Y (i+1) _).continuous)))),he]; rfl
include hp
lemma real_ray (hi:i ≤ n)(q:Flavor N→ℝ)(v:ℝ):∃ p:ℝ,0 < p∧∀ z:ℂ, Cvol (family P₀ A B Y q v i z)= (p:ℂ) * Cvol (family P₀ A B Y q v n z):=by
    induction hi using Nat.decreasingInduction with
    | self=> exact ⟨1,zero_lt_one, by simp⟩
    | of_succ i hi ih=> obtain ⟨p,hp',hY⟩:=ih; let P:=Rain.gain (W i) (A.ring (B.n k) i) N; refine ⟨P*p,mul_pos (pow_pos (hp.relay i hi).real _) hp',fun z=>?_⟩; rw [volume_ray P₀ A X B T V W F Y hh hi,hY z,Complex.ofReal_mul,mul_assoc]
include hO hc hX
lemma earth_ray (hi:i≤n)(q: Flavor N→ℝ)(v w:ℝ) : 0≤ Cvol (family P₀ A B Y q v i (w:ℂ)):=by
    obtain ⟨F',h,hq⟩:= real_ray P₀ A X B T Z V U W F hp Y hh hi q v; rw [hq (w:ℂ)]; apply mul_nonneg (Complex.zero_le_real.mpr h.le); rw [Sharp.massC _ (starts P₀ A X B T Z V U W F hp hX hc Y hh q v w)]; exact Sharp.shown _ (zero_le_one.trans (hp.window n le_rfl).2.2.1) (hO.1.trans (orbitTall P₀ A _ _)) (orbitEven P₀ A _ _ hO.2.1)
omit hh hp hc hX hO

abbrev coinC (x:ℝ)(i:ℕ)(z:ℂ):ℂ:= z/(dial P₀ A x i:ℂ)
abbrev cashR (x:ℝ)(i:ℕ)(z:ℝ):ℝ:= z/dial P₀ A x i
lemma classicR (i:ℕ) (t:ℝ): coinC P₀ A x i (t:ℂ)=(cashR P₀ A x i t:ℂ):= (Complex.ofReal_div ..).symm
include he
lemma leaseC (i:ℕ)(v:ℂ): ‖coinC P₀ A x i v‖≤ ‖v‖:=by
   let r:=dial P₀ A x i; have h:=realX P₀ A X E he i
   unfold coinC; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg h.le]; exact div_le_self (norm_nonneg _) (scalePay P₀ A (realY P₀ A X E he) i)
lemma marge (i:ℕ)(q: Flavor N→ℝ)(v:ℝ)(z:ℂ): family P₀ A B Y q v i z= HatWalk P₀ A B Y q v x i (coinC P₀ A x i z) :=by
   unfold HatWalk Library.grow coinC; have h:= realX P₀ A X E he i; field_simp [h.ne']
lemma capR (i:ℕ)(q:ℝ)(h:0≤q): 0 ≤ cashR P₀ A x i q∧ cashR P₀ A x i q ≤ q:=by
   refine ⟨div_nonneg h (realX P₀ A X E he i).le,div_le_self h (scalePay P₀ A (realY P₀ A X E he) i)⟩
omit he

variable (Ht: Uptax P₀ A E x)
structure SnowT (Pt:ℕ→BudgetPoint)(L:HaarBudget su)(O:Paved P₀ A X x)(i:ℕ)(M: Code (A.ring (B.n k) i) N)(C:ℂ→ℂ)(s v w:ℝ) :Prop where
     plank :Shelf_R P₀ A X B T V U E M₀ Y Ht O i M C s v Pt L
     polish : 0 < Cvol (family P₀ A B Y M₀.tip v i (w:ℂ))
     pressure : ‖C (coinC P₀ A x i (w:ℂ))‖ * Audience (A.ring (B.n k) i) L (twist (P:=P) (A.node i)) (A.flight i).patch (clockQ P₀ A x i) (Ht.cost i) (O.Y i) ≤ (Cvol (family P₀ A B Y M₀.tip v i (w:ℂ))).re
structure StormT (Pt:ℕ→BudgetPoint) (L:HaarBudget su)(O:Paved P₀ A X x)(v w:ℝ) :Prop where
    weight : w∈ Set.Icc (1/2:ℝ) 1
    storm : ∀ i≤ n, ∃ M C s,SnowT P₀ A X B T V U E M₀ Y Ht Pt L O i M C s v w

include hO hc hX hs hp he hh
set_option maxHeartbeats 740000 in
theorem winter (L1:HaarBudget su)(hN:Even N):∃ w:ℝ, StormT P₀ A X B T V U E M₀ Y Ht Pt L1 O v w:=by
   let Q:= Fin (n+1); let z0:Q:=⟨n,by omega⟩; let τ(i:ℕ):= clockQ P₀ A x i; let σ(i:ℕ):= coinC P₀ A x i; let G(i:ℕ):=family P₀ A B Y M₀.tip v i; let ℒ(i:ℕ):= A.spacing i; let L(i:ℕ):=A.ring (B.n k) i; let m:=Ht.cost; let y:=O.Y
   have h(i:Q):i.val≤n:= Nat.le_of_lt_succ i.isLt
   choose L' C shUt H using fun i:Q=> rent P₀ A X B T Z V U W F hp hX hc E M₀ he Y hh hs hO Ht L1 (h i) hN -- order
   let Y₁(i:Q):= C i ∘ σ i.val; let Ce(i:Q):= fun z:ℂ=> Cvol (family P₀ A B Y M₀.tip v i.val z)
   let Max(i:Q):= ζMax L1 (twist (P:=P) (A.node i.val)) (L i.val) (ℒ i.val) (τ i.val) (m i.val); let Min(i:Q):=ζMin L1 (twist (P:=P) (A.node i.val)) (L i.val) (ℒ i.val) (τ i.val) (y i.val+2)
   choose p hp' hΨ using fun i:Q=> real_ray P₀ A X B T Z V U W F hp Y hh (h i) M₀.tip v
   have hP(i:ℕ):0 < gaugeSize (ℒ i) (τ i):=((Ht.bill i).pos _ le_rfl).1
   have hC(i:Q):= (H i).2.2.2.2.1 -- n fields 6. Tera. 
   have hv(i:Q)(z:ℂ): Ce i z= Cvol (HatWalk P₀ A B Y M₀.tip v x i.val (σ i.val z)):=congr_arg Cvol (marge P₀ A X B E he Y i.val M₀.tip v z) -- arg B order
   have hA(i:Q)(z:ℂ)(hz:‖z‖≤2):=(hC i).clean _ ((leaseC P₀ A X E he i.val z).trans hz)
   obtain ⟨w,hv',hQ⟩:= Gravity.align z0 Ce Y₁ Max Min p (fun i=>Sharp.inspects (Y i.val) M₀.tip (v:=v)) (fun i=>⟨(hC i).holo.1.comp (by unfold σ coinC; fun_prop (disch:=first | exact_mod_cast (realX P₀ A X E he i.val).ne' | intros; exact_mod_cast (realX P₀ A X E he _).ne')) (fun z h=> opened.mpr (lt_of_le_of_lt (leaseC P₀ A X E he i.val z) (opened.mp h))), (hC i).holo.2.comp (by unfold σ coinC; fun_prop (disch:=first | exact_mod_cast (realX P₀ A X E he i.val).ne' | intros; exact_mod_cast (realX P₀ A X E he _).ne')) (fun z h=> closed.mpr ((leaseC P₀ A X E he i.val z).trans (closed.mp h)))⟩) hp' hΨ (fun i z hz=> (hA i z (closed.mp hz)).1) (fun i=> Sharp.maxP _ _ (hP i.val)) (fun i=> Sharp.minP _ _ (hP i.val)) (fun i=> (by
          have heq: σ i.val 0=0:= zero_div _; rw [hv i 0,show Y₁ i 0=C i (σ i.val 0) from rfl,heq]; exact (hC i).lower.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _)))) (fun i z hz=> (by
          rw [hv]; exact (Sharp.peak (Y i.val _)).trans (hA i z (closed.mp hz)).2.2.2  -- may metavars
   ))
   refine ⟨w,hv',fun i hi=>?_⟩; let t':Q:=⟨i,by omega⟩; have he' :0≤ Ce t' w:= earth_ray P₀ A X B T Z V U W F hp hX hc Y hh hO hi M₀.tip v w; have hd':w∈Set.Icc (1/2:ℝ) 1:=hv'
   let y':=Ce t' (w:ℂ); obtain ⟨h_w,hτ⟩:= Complex.le_def.mp he'; have hr:y'=(y'.re:ℂ):=Complex.ext (by simp) (by exact hτ.symm); have hx: ‖y'‖= y'.re:= (congr_arg Norm.norm hr).trans (normS _ h_w)
   have hC':0 < ‖Y₁ t' (w:ℂ)‖:= norm_pos_iff.mpr ((hA t' (w:ℂ) (by rw [normS w (by linarith only [hv'.1])]; linarith only [hv'.2])).1)
   let I:= Sharp.Audience (L i) L1 (twist (P:=P) (A.node i)) (A.flight i).patch (τ i) (m i) (y i)
   have hg: ‖Y₁ t' (w:ℂ)‖ * I ≤ y'.re:=(hQ t').trans_eq hx
   have h_p:0< y'.re:=(mul_pos hC' (Sharp.paid _ (hP i))).trans_le hg -- Patch issue
   exact ⟨L' t',C t',shUt t',H t', lt_of_le_of_ne he' (Ne.symm (norm_pos_iff.mp (hx.symm ▸ h_p))), hg⟩

-- operational use: positivity in every chapter. true Massive.Run.
omit hO hc hX hs he hh hp
private lemma along (S:Scheme)(R:Side)(β w:ℕ→ℝ)(Z: ℕ)(he:∀ m,m ≤ Z→0<β m)(hw:∀ m,m<Z→0<w m)(u:Flavor N→ℝ)(hz:0<Massive.joint ((S.run R β w u Z).density Z)): (S.run R β w u Z).Actual:=by
    let X:=S.run R β w u Z; let U:= S.wilson R β u Z; have H: X.Carried X.density 0:= S.carried R β w U.density _; have h (i) : X.density i=⇑(S.toStop R β w Z i U.density):= rfl; have hu:X.density Z= ⇑U.density :=by rw [h,Massive.Scheme.entrance]; rfl
    change X.Actual; refine ⟨hu,H,fun {i} hi=>he i hi,fun {i} hi=> hw i hi,fun {i} hi x=>?_,fun {i} hi x k=>?_, fun {i} hi=> ?_⟩
    · refine S.parity R β w U.density false (fun x=>?_) hi x
      change Grass.Plus _; rw [Massive.Regulator.density_apply]; exact Grass.Hom.smul (p:=false) (gauss_plus _) _
    · rw [h i]; exact DFunLike.congr_fun (S.transport_gauge R β w U.density U.invariant hi k) x
    rw [Massive.Scheme.conservation S R X.density _ H hi (by omega)]; apply mul_pos _ hz; exact S.positive R w hw hi _
variable (hS:StormT P₀ A X B T V U E M₀ Y Ht Pt L1 O v w)
include hc hX hs he hh hp hS
omit hs he in
lemma real_story : (covering (n:=n) (k:=k) P₀ A B V U W M₀.tip v w).Actual:=by
   apply along _ _ _ _ _ (fun i hi=>zero_lt_one.trans_le (hp.window i hi).2.2.1) (fun i hi=>(hp.relay i hi).real); obtain ⟨m,p,H,h⟩:= hS.storm n le_rfl; suffices H:∀ f c:Side,∀ (h:f=c)(G:Density f N),0<Massive.joint G→ 0 <Massive.joint (transit h G) by
      change 0 < Massive.joint ((covering (n:=n) (k:=k) P₀ A B V U W M₀.tip v w).density _); rw [exact_cov P₀ A X B T Z _ _ _ F hp hX hc Y hh _ _ _ _ le_rfl]; exact H _ _ _ _ h.polish
   intro f c h; subst c; exact fun _=>id
omit hc hX he hh hp in
lemma distinct_t (hA:Function.Injective M₀.tip): Function.Injective (covering (n:=n) (k:=k) P₀ A B V U W M₀.tip v w).u :=by
   have hw:0<w:=by linarith only [hS.weight.1];
   intro i j h; change _+v*w*M₀.tip i= _+v*w*M₀.tip j at h; exact hA (mul_left_cancel₀ (mul_pos hs.beam hw).ne' (add_left_cancel h))
end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.winter
