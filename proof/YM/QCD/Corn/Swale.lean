import YM.QCD.Corn.Native
import YM.QCD.Vita.Cacti
import YM.Branch.Covariant
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
-- publication.Evaluation
open NormedSpace MeasureTheory High.PrismT Stew.Project Sway
def Maison (c:Side)(N:ℕ)(X:Pixel c N):Prop:=∃ (Y:EvenA c N)(f:Grid c→ℂ),∀ U,X U=f U • Y
lemma toast (V: Pixel c N)(hx:Maison c N V)(h:shadeG V) (hp: mud (V 1)≠0) (k:Lat.Frame c): sways (Lat.rotates N k) (V 1) = V 1 :=by
    obtain ⟨f,g,hX⟩:=hx; let D:=Lat.rotates N k; let Y:= gauge k (1:Grid c); have hv: sways D (V Y)=V 1:=Subtype.ext (h 1 k); have ht: mud (V 1)=mud (V Y):=(congr_arg mud hv.symm).trans (Reggae.walks ..)
    have hk(x):mud (V x)=g x*mud f:=by rw [hX]; exact map_smul (clay c N) ..
    have hL : mud f≠0:=fun he=> hp ((hk _).trans ((congr_arg _ he).trans (mul_zero _)))
    rw [hk,hk] at ht; exact (congr_arg (sways D) ((hX 1).trans ((congr_arg (fun x:ℂ=> x • f) (mul_right_cancel₀ hL ht)).trans (hX _).symm))).trans hv
-- test colour. only project gold first Hue. require i anchored exactly. select q diag.
private def PlumV: Mat:= Matrix.diagonal ![(-1:ℂ),-1,1]
private lemma mars : ∃ V:su.El, colour V=PlumV:=by
    have hv:star PlumV=PlumV:=by ext i j; fin_cases i <;> fin_cases j <;> simp [PlumV,Matrix.diagonal_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]
    have hm: PlumV∈unitary _:=by constructor <;> rw [hv] <;> ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [PlumV, Matrix.mul_apply,Hue,Fin.sum_univ_succ,Matrix.one_apply,Matrix.diagonal_apply]
    have hP:PlumV.det=1:=by simp [PlumV, Hue,Fin.prod_univ_succ,Matrix.det_diagonal]
    exact ⟨⟨⟨_,hm⟩,hP⟩,rfl⟩
lemma hoof (x:EvenA c N)(b:Flavor N)(h:∀ k:Lat.Frame c,sways (Lat.rotates N k) x=x) (hp:Fit x)(i j:Site c)(he:i≠j): Stew.gold (cell (Stew.meter (c:=c) b x) i j)=0:=by
    obtain ⟨V,hV⟩:=mars; let p: Frame c:= Function.update (fun _=>1) i V; let R:=siteRot p; let T:= feeF b x
    have hr : T=star R*T*R:= (congr_arg (feeF b) (h p).symm).trans (rite x b _ hp)
    have hG:R*T=T*R:=by nth_rw 1 [hr]; rw [←Matrix.mul_assoc,← Matrix.mul_assoc,(siteRot_u p).2,one_mul]
    let C:= cell T i j
    have hm:=congr_arg (fun X=> cell X i j) hG; have hv₁(Y: Site c→Bundle)(U:Sheet c): cell (U* rides (Equiv.refl _) Y) i j=cell U i j *Y j:=by nth_rw 1 [← star_star (rides (Equiv.refl _) Y)]; rw [ride_ad, cell_ride_right, star_star]; rfl
    unfold R siteRot at hm; rw [cell_ride_left,hv₁] at hm; change touch (colour (p i))*C=C*touch (colour (p j)) at hm; rw [show p i=V from update_self ..,show p j=1 from update_of_ne (Ne.symm he) _ _, show colour 1=1 from rfl, touch_one, mul_one,hV] at hm -- inspect
    ext a b'; have hx:=congr_fun (congr_fun hm (a,0)) (b',0); have hv: -C (a,0) (b',0)= C (a,0) (b',0):=by obtain ⟨i,j⟩:= a; fin_cases i <;> fin_cases j <;> simpa [Lat.touch, PlumV, Hue,Matrix.one_apply,Matrix.diagonal_apply, Fintype.sum_prod_type, Matrix.mul_apply, Fin.sum_univ_succ,ite_mul] using hx
    change C (a,0) (b',0)=0; linear_combination hv / -2
lemma height0 (X:Sheet c)(h:∀ i j:Site c,i≠j → Stew.gold (cell X i j)=0) : unitF true c X=0:=by
     have hh: μDir c true X=0:=by
          change (∑ i,∑ j,Stew.Project.stone c true i j • Stew.gold (cell X i j))= _; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; by_cases hz:i=j; · subst j; unfold Stew.Project.stone Entr.crest lift; simp
          rw [h _ _ hz,smul_zero]
     change ((Fintype.card (Site c):ℝ)⁻¹ • bb true (μDir c true X))=_; rw [hh,map_zero,smul_zero]
lemma coupler (X:Pixel c N)(b:Flavor N)(h: ConvexF X b): ¬Maison c N X:=by
    intro hM; have ht:=h.rocket; exfalso
    have hv : unitF true c (High.PrismT.fumes b (X 1))=0:=by
        apply height0; intro i j hi; have he(z:ℂ)(V:Sheet c):Stew.gold (cell (z • V) i j)=z • Stew.gold (cell V i j):=rfl
        unfold High.PrismT.fumes; rw [he,hoof _ b (toast X hM h.proper.gauges h.aliveT) (h.proper.fluteC _) _ _ hi,smul_zero]
    change _ ≤ unitF _ _ _ at ht; rw [hv] at ht; norm_num at ht
end Rails
end YM.QCD.Acre
