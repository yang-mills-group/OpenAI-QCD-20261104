import YM.QCD.Glass.Major
import YM.QCD.Sq.Axis
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
namespace Rails
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q T'.top N}
open High PrismT MeasureTheory
open High PrismT MeasureTheory Sq
open Grass
open Sq Stew.Project
variable (T':Teller su)(B:SparkMesh) (b': Flavor N)
lemma primeT {rv rv': Twin→ℝ}(h:Continuous rv)(hp:Continuous rv'): Reach (c:=c) Set.univ (fun i=> CodeG c N (rv i) (rv' i)):=by
   let F(p:Twin×Grid c):= primalD c N (rv p.1) (rv' p.1) p.2
   have hU : Continuous F :=by unfold F primalD Wilson.bare; unfold Lat.bareD singleHop; fun_prop
   exact ((levit c N).continuous.comp hU).continuousOn
noncomputable def TideD (B:SparkMesh)(J:Patch)(n k j:ℕ)(N:ℕ):=Pixel (towerQ J B n j k) N -- use abbrev
variable {S':ℕ→SparkMesh}{Y:ℕ→ℝ}{P':ℕ→BudgetPoint}{E:ℕ→ SunR Ω}(D':PulseRide T'.bind T'.top.clip J a d S' n)
variable (O:PlaqAxes)(hD:Storyboard n k T' B b' D' P' E Y κ x r D W' O)(hPay:∀ i≤n,RightsT J n N x (run J.L x) W' Y i)(ht:J.Branches T'.bind su)
-- sequential potential.D.Entry equals prior.True not circuit clothed.M.Curried.
structure Litmus (K:St c)(b:Flavor N)(X:Pixel c N)(m:ℝ) :Prop where
   clean : 1/4 ≤ Stew.Project.unitF true c (K 1)
   aliveT: PrismT.tollM true b (X 1)=unitF true c (K 1)
   mellow: PrismT.tollM false b (X 1)=unitF false c (K 1)+m
structure ChartQ (l:ℕ)(Z:Set Twin)(V U:ℕ→Twin→ℝ)(S0:∀ i,Twin→Pixel (towerQ J B n i k) N)(F:Twin→Twin) :Prop where
   live : MapL (centerG Y (run J.L x) n l) (sideG n l) (rangeG J n l κ r x) Z (V l) (U l) F
   chargeP: ContinuousOn (V l) Z
   walk : Reach Z (S0 l)
   birth (i:Twin): i∈Z→ S0 0 i=CodeG (towerQ J B n 0 k) N (V 0 i) (U 0 i)
   vogue (t:Twin)(hv:t∈Z)(j:ℕ)(hp:j≤l):Cashroom J n j x (V j t)∧ |U j t|≤ rangeG J n j κ r x ∧ Trek T' B b' D' (E j) (P' j) j k x r (V j t) (U j t) (S0 j t) -- projection canonical maybe include.W Ω need later spectral.G.Canon at outputs. add β recurrence bound now
   cost (t:Twin)(hv:t∈Z)(j:ℕ)(hq:j<l)(hy:j<n): ∃ w:ℝ, 0<w∧w≤4∧|V (j+1) t-V j t-Y j| ≤ 2∧ S0 (j+1) t=FortG T' B hy w (V j t) (S0 j t) ∧ ∀ A, advance (Pike J j) T'.bind (lift0 B hy) (S0 j t) (V j t) A=gBody _ w (S0 (j+1) t A)
   lawT (t:Twin)(hv:t∈Z)(j:ℕ)(hq:j<l): Litmus (ΞP Ω (E (j+1)) (towerQ J B n (j+1) k) J (delay J n (j+1) x) (j+1)) b' (S0 (j+1) t) (U (j+1) t)

variable (l:ℕ)(V U:ℕ→Twin→ℝ)(S0:∀ i,Twin→Pixel (towerQ J B n i k) N)(F:Twin→Twin){Z:Set Twin}
include ht hPay hD
set_option maxHeartbeats 600000 in
lemma ridesC (hp:ChartQ T' B b' D' l Z V U S0 F (P':=P') (Y:=Y) (E:=E) (κ:=κ) (x:=x) (r:=r))(hl:l<n):∃ Z' V' U' S F,ChartQ T' B b' D' (l+1) Z' V' U' S F (P':=P') (k:=k) (Y:=Y) (E:=E) (κ:=κ) (x:=x) (r:=r):=by
   obtain ⟨v,u,z,hZ⟩:= hD.rails l hl; choose! w p q hQ using fun i (hi:i∈Z)=> hZ.entries (V l i) (U l i) (S0 l i) (hp.vogue _ hi l le_rfl).1 (hp.vogue _ hi _ le_rfl).2.2 (hp.vogue _ hi _ le_rfl).2.1
   let E₁(i):=FortG T' B hl (w i) (V l i) (S0 l i); let b₁ i:= V l i+Y l+q i; let y:=run J.L x; let c:=centerG Y y n; let g:= rangeG J n (l+1) κ r x; let z:= sideG n (l+1)
   have hs1 := solarX (S:= Pike J l) (h:=lift0 B hl) hp.live.clans hp.walk ht hp.chargeP -- Branch.K inferred?
   obtain ⟨hr,hv,he,hχ⟩:= garnet (E (l+1)).Z.page _ _ _ b' w _ hs1 (Xs:=E₁) (E:=b₁) (fun i=>rfl) (fun i hi=> ⟨(hQ i hi).2.2.2.2.2.2.2,(hQ i hi).1,(hQ i hi).2.2.2.2.2.2.1⟩) hZ.gift
   have hX : c l+Y l=c (l+1):=squares Y J _ hl
   have hY :sideG n l= sideG n (l+1)+3:=by unfold sideG; rw [show n-l=n-(l+1)+1 from (by omega)]; push_cast; ring
   have hx(i)(hi:i∈Z):=(abs_le.mp (hQ i hi|>.2.2.1)); obtain ⟨Z₁,F,H',H⟩:= hullT F hp.live (side_p n (l+1)) (hD.positive (l+1)) hr hv (w:=centerG Y y n (l+1)) (fun i hi=>by unfold b₁; constructor <;> (intro ht; rw [ht]; linarith only [hX,hY,(hx i hi).1,(hx i hi).2])) (fun i hi=> (hQ i hi).2.2.2.2.1)
   subst Z₁
   let V':= Function.update V (l+1) b₁; let U':= Function.update U (l+1) p; let F':= Function.update S0 (l+1) E₁
   refine ⟨_,V',U',F',F,by unfold V' U'; simpa only [Function.update_self] using H,?_,?_ ,?_ ,?_, ?_,?_⟩
   · unfold V'; rw [Function.update_self]; exact hr.mono fun i hi=>hi.1
   · unfold F'; rw [Function.update_self]; exact he.mono fun i hi=>⟨hi.1.1,hi.2⟩ -- D×Set
   · intro i hi; simp only [V',U',F',Function.update_of_ne (show 0≠l+1 from (by omega))]; exact hp.birth i hi.1
   · intro i hi j hj; change _∧ _ ∧ _; by_cases hb:j=l+1
     · subst j; simp only [V',U',F',Function.update_self]; exact ⟨(hPay _ hl).le _ hi.2.1,hi.2.2,(hQ i hi.1).2.2.2.1⟩
     simp only [V',U',F',Function.update_of_ne hb]; exact hp.vogue i hi.1 j (by omega)
   · intro i hi j hj hy; unfold V' F'; by_cases hb:j=l
     · subst j; rw [update_self,update_of_ne (Nat.ne_add_one _),update_self,update_of_ne (Nat.ne_add_one _)]; -- applies motive?
       obtain ⟨hk,hw,hv,he,hH,hM',hf⟩:= (hQ i hi.1); refine ⟨w i,hk,hw,(by rwa [show b₁ i-(V l i)-Y l=q i from (by unfold b₁; ring)]),rfl,hM'⟩
     simp only [update_of_ne (show j+1≠l+1 from (by omega)),update_of_ne (show j≠ l+1 from (by omega))]; exact hp.cost i hi.1 j (by omega) hy
   intro i hi j hj
   unfold F' U'; by_cases hℓ:j=l
   · subst j; rw [update_self,update_self]; have H:= (hQ i hi.1).2.2.2.2.2.2; exact ⟨H.1,H.2.lea,H.2.life⟩
   simp only [update_of_ne (show j+1≠l+1 from (by omega))]; exact hp.lawT _ hi.1 _ (by omega)

end Rails
end YM.QCD.Acre
