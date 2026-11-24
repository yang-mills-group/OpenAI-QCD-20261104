import YM.QCD.Vita.Equi
import YM.Extraction.Tame
import Mathlib.Topology.UniformSpace.Ascoli
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
open Push.BetaTransport Rain MeasureTheory
variable {M Rᵥ V U Wᵥ A₁ Y:ℕ→ℝ}
noncomputable def money (A:Pixel c N): Pixel c N:= (Cvol A).re⁻¹ • A
lemma lucent (A:Pixel c N): Cvol (money A) = (Cvol A).re⁻¹ • Cvol A:=by
   unfold money Cvol; rw [← integral_smul]; apply integral_congr_ae; apply ae_of_all; intro i; exact map_smul ((peakW c N).restrictScalars ℝ) ..
lemma lays (A:Pixel c N)(hv:Rain.realP A) : Cvol A= ((Cvol A).re:ℂ):=by
    let f:=cBer A; have he: Cvol A= (((∫ x,(f x).re ∂prior su c):ℝ):ℂ):=by rw [← integral_complex_ofReal]; exact integral_congr_ae (ae_of_all _ fun i=> (hv i).1)
    rw [he]; rfl
lemma boosts (A:Pixel c N)(hp:0<(Cvol A).re)(hc:Continuous A)(hv:Rain.realP A)(hh:∀ i,‖A i‖≤(Cvol A).re*u) : Continuous (money A) ∧ Rain.realP (money A) ∧ Cvol (money A)=1∧∀ i, ‖money A i‖≤u:=by
    let r:=(Cvol A).re; have he:0<r:=hp
    refine ⟨continuous_const.smul hc,fun i=>?_,?_,fun i=>?_⟩
    · have hX: cBer (money A) i=r⁻¹ • cBer A i:=map_smul ((peakW c N).restrictScalars ℝ) ..; obtain ⟨hV,hR⟩:=hv i; rw [hX,Complex.smul_re,smul_eq_mul]; exact ⟨by rw [Complex.real_smul, Complex.ofReal_mul,← hV],by positivity⟩
    · rw [lucent]; change r⁻¹ • Cvol A= _; rw [lays _ hv]; change r⁻¹ • (r:ℂ)= _; simp [he.ne']
    change ‖r⁻¹ • A i‖≤_; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr he).le]; exact (mul_le_mul_of_nonneg_left (hh i) (inv_pos.mpr he).le).trans_eq (by rw [← mul_assoc,inv_mul_cancel₀ he.ne',one_mul])
-- stronger than SimpleH (full Grass fields equality) preserve to limit
noncomputable def gRight (Y:Pixel c N)(w:ℝ)(i:Grid c): Fields c N:= (gain w⁻¹ c N)⁻¹ • gBody c w (Y i)
abbrev Modern (S:Flight j j)(K:KernelChoices)(h:f.val=c.val*S.L.val)(x t:ℝ)(X:Pixel f N)(Y:Pixel c N):Prop:=∀ i, advance S K h X x i=gRight Y t i
lemma versed (X:Pixel f N)(Y: Pixel c N)(v:ℝ)(hv: 0 < v)(hp: Modern S K h u v X Y): SimpleH S K h u v X Y:=by
    intro i; rw [hp]; unfold warpH; have he:0 < gain v⁻¹ c N:=pow_pos (inv_pos.mpr hv) _; rw [gRight, levyR,gBody, callH, smul_inv_smul₀ he.ne',wit _ _ _ (mul_inv_cancel₀ hv.ne')]
lemma moved (S:Flight j j)(h:f.val=c.val*S.L.val)(X:Pixel f N)(Y:Pixel c N)(w:ℝ)(hp: Cvol X= Rain.gain w⁻¹ c N • Cvol Y)(he:∀ i, advance S K h X β i=gBody c w (Y i)): Modern S K h β w (money X) (money Y):=by
    intro i; unfold money gRight; rw [hp,Complex.smul_re,smul_eq_mul, _root_.mul_inv_rev, beamG,he]
    let t:=(Cvol Y).re⁻¹; let M:= (Cove.light (Keys c N)).toLinearMap.restrictScalars ℝ; rw [show gBody _ w ((t • Y) i)=t • gBody _ w (Y i) from ?_]; rw [mul_smul,smul_comm]
    change M (songT (c:=c) (N:=N) w⁻¹ (t • Y i))= _; rw [map_smul,map_smul]; rfl
variable {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{S':ℕ→SparkMesh}(B:SparkMesh)(b':Flavor N) (g:PulseRide T'.bind T'.top.clip J a d S' n) (A0:∀ i,Pixel (towerQ J B n i k) N) (hG: Stargate T' B b' g P' X Y κ x r D W' k V U Wᵥ A0)
variable (he:∀ i≤n,Continuous (A0 i)∧Rain.realP (A0 i)∧0<(Cvol (A0 i)).re ∧ (∀ V,‖A0 i V‖≤ (Cvol (A0 i)).re * M (n-i))) (hQ:∀ i j,n=i+j+1 → Rᵥ j≤Wᵥ i)
noncomputable abbrev GaugeM (O:Patch)(j:ℕ)(x:ℝ):= run O.L (tallyK O.L x j)
-- transport straight
lemma alignsC (h:i ≤ n) : towerQ J B n (n-i) k=finC J B i k:=by unfold towerQ; rw [feetM,show n-(n-i)=i from (by omega)]
noncomputable def carryP (Q:Pixel c N)(hx:c=L):Pixel L N:= hx ▸ Q
noncomputable def aligned (m:ℕ): Pixel (finC J B m k) N:= if h:m≤n then carryP (money (A0 (n-m))) (alignsC B h) else 0
structure Candor (O:Patch)(B:SparkMesh)(K:KernelChoices)(M R:ℕ→ℝ)(N n k:ℕ)(x κ r:ℝ)(V U W:ℕ→ℝ)(A:∀ i,Pixel (finC O B i k) N):Prop where
    capital (i:ℕ)(h:i≤n): Continuous (A i) ∧ Rain.realP (A i)∧ Cvol (A i)=1 ∧ (∀ j, ‖A i j‖ ≤ M i) ∧ GaugeM O i x/2 ≤ V i ∧ V i ≤2*GaugeM O i x ∧ |U i|≤ rangeG O i 0 κ r x
    mint : U 0=0 ∧ V 0=run O.L x
    vocals (i:ℕ)(h:i<n): W i ≤4 ∧ R i ≤W i ∧ Modern (Pike O 0) K (powerV B O i k) (V (i+1)) (W i) (A (i+1)) (A i)
include hG he hQ
lemma blue (hk:J.Branches T'.bind su)(hN:Even N) : Candor J B T'.bind M Rᵥ N n k x κ r (fun i=> V (n-i)) (fun i=> U (n-i)) (fun i=> Wᵥ (n-(i+1))) (aligned B A0):=by -- binder order
    refine ⟨?_,by simpa only [Nat.sub_zero] using hG.finish.symm,?_⟩
    · intro i hi; let l:=n-i; obtain ⟨hx,hp,hE,hR⟩:= he l (by unfold l; omega); have hm:n-l=i:=by unfold l; omega
      rw [hm] at hR; obtain ⟨hV,hM,hT,hS⟩:=boosts (A0 l) hE hx hp hR -- boosts typo
      obtain ⟨hx,hv,hp,-⟩:= hG.costs l (by unfold l; omega); unfold Cashroom hatG delay at hx; unfold rangeG delay at hp; rw [hm] at hx hp
      have hg (d:Side)(K:d=finC J B i k) (A:Pixel d N) (hV:Continuous A) (hM:Rain.realP A)(hT:Cvol A=1)(hS:∀ j, ‖A j‖ ≤ M i): Continuous (carryP A K) ∧ Rain.realP (carryP A K) ∧ Cvol (carryP A K)=1∧∀ j, ‖carryP A K j‖≤M i:=by subst d; exact ⟨hV,hM,hT,hS⟩
      unfold aligned; rw [dif_pos hi]; obtain ⟨hK,H,Z,Y⟩:= hg _ (alignsC B hi) (money (A0 l)) hV hM hT hS; exact ⟨hK,H,Z,Y,hx.1,hx.2,by simpa only [rangeG,delay,Nat.sub_zero] using hp⟩
    intro i hi; let j:=n-(i+1); have hp:n=i+(j+1):=by unfold j; omega
    obtain ⟨hw,hv,hH,hU⟩:=hG.vocals j (by omega); have hY: Modern (Pike J j) T'.bind (lift0 B (by omega : j<n)) (V j) (Wᵥ j) (money (A0 j)) (money (A0 (j+1))):= moved _ _ _ _ _ (voltU B g b' A0 hG hk hN (j:=j) (by omega)|>.2) hU -- edit volt
    refine ⟨hv,hQ j i (by omega),?_⟩; unfold aligned; rw [dif_pos hi.le,dif_pos (show i+1≤n from hi)]; -- order
    let W:=Wᵥ j
    have hy(f c:Side)(hf:f=finC J B (i+1) k)(hc:c=finC J B i k)(p:f.val=c.val*J.L.val)(X:Pixel f N)(Y:Pixel c N)(hY: Modern (Pike J j) T'.bind p (V j) W X Y): Modern (Pike J 0) T'.bind (powerV B J i k) (V j) W (carryP X hf) (carryP Y hc):=by subst f c; exact hY
    have hx:n-i=j+1:=by omega; -- motive aligns hp equality using HEq
    have hxm (l:ℕ)(hh:l=j+1)(hC: towerQ J B n l k=finC J B i k): Modern (Pike J 0) T'.bind (powerV B J i k) (V j) W (carryP (money (A0 j)) (alignsC B hi)) (carryP (money (A0 l)) hC):=by subst l; exact hy _ _ _ _ (lift0 B (show j<n from by omega)) _ _ hY
    exact hxm _ hx _
end Rails
end YM.QCD.Acre
