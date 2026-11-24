import YM.Massive.Conductor.Motive
import YM.Massive.Pressure.Runs
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Aperture
open Acre
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
open Stew Ursell
open Blaze Shells Sands Dust King Lapis Sienna Fare Octave Fount Grove Planned.JetPort Tidings Entr PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit -- Badge from Acre below
open Acre Rails
open Finset Coat Grass NormedSpace
open MeasureTheory Massive.Filament Pith Fibre Fused
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W r e:ℝ} {P T:BudgetPoint} {R:Pixel c N}
variable {I Ω ι β: Type}
open Struck Struck.Library
open Finch Carrier

variable {t p:ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (X:ℂ→ℂ→ Patron.Rail c N I)(Y:ℂ→ℂ→Ruby.Hue c N Ω)
open Ruby Weft High
set_option quotPrecheck false
local notation "Tz"=>P.threshold
variable {b Y₁: ℝ}{s z U:ℂ}{W₁:Grid c}
local notation "νT"=> (1/8:ℝ)
open Conductor Conductor.Quant Meridians
local notation "J"=> Site c × Flavor N -- avoid J variable
open Brick QCD.Free
variable (c) (u v:Flavor N→ℝ) (U:Grid c)
abbrev flux (z:ℂ)(V:Pixel c N)(U:Grid c): EvenA c N:= V U * exp (z • (∑ i:Site c×Flavor N, (rentGem u).view i 1))
abbrev ingredient : EvenA c N:=∑ i:Site c×Flavor N,(rentGem u).view i 1
noncomputable def pedestal (i:Flavor N):EvenA c N:= knob c i (Port.paleF N ((u i:ℂ) • (1:Sheet c)))
lemma indoors (b:Flavor N): (∑ i:Site c, unitL b (u b) i)=pedestal c u b:=by
    let M:ℂ:=(u b:ℝ); change (∑ i:Site c, knob c b (nozzle c N (localX i (M • 1))))=_; simp_rw [pineS]; rw [← map_sum, ← map_sum, ← Finset.smul_sum,volley,on_spin_one];rfl
lemma kiosk : ingredient c u=∑ i:Flavor N,pedestal c u i:=by unfold ingredient; rw [Fintype.sum_prod_type,sum_comm]; exact sum_congr rfl fun i _=> indoors c u i
lemma priceAt (b:Flavor N): feeF b (ingredient c u)= (u b:ℂ) • (1:Sheet c):=by
    rw [kiosk]; change Stew.meter b _=_; rw [map_sum,sum_eq_single b]; rotate_left
    · intro i _ hi; exact (profileK i b _).trans (if_neg hi)
    · simp
    exact (profileK b b _).trans (if_pos rfl)
lemma retail (b:Flavor N)(t:ℝ): Finch.flagRead b t (ingredient c u)=t^2*u b:=by rw [Finch.flagP,priceAt]; unfold flagW; rw [peel_smul, peel_one]; simp
open Massive.Onsite
lemma forge_linear : ∃ A:FormN c N→ₗ[ℂ] Fields c N, ∀ X,A X=form X:=by
   refine ⟨{ toFun:=fun X=>Grass.form X, map_add':= Grass.form_add, map_smul':=?_ },fun _=>rfl⟩; intro t V; dsimp; unfold Grass.form; simp [Finset.smul_sum,smul_smul] -- FormN ns
lemma panelised : Cove.light _ (ingredient c u)=Grass.form (Massive.Onsite.offset u (univ:Support c)):=by
    obtain ⟨A,hA⟩:= forge_linear c (N:=N); rw [kiosk,map_sum,←hA]; have h (i:Flavor N): Cove.light _ (pedestal c u i)=A (Finch.stripe N i ((u i:ℂ) • 1)):= (Pith.pure (c:=c) i ((u i:ℂ) • 1)).trans (hA _).symm
    simp_rw [h]; rw [← map_sum]; apply congr_arg
    ext ⟨x,i⟩ ⟨y,j⟩; rw [Matrix.sum_apply,sum_eq_single i]
    · by_cases he:x=y<;> by_cases hf:i=j<;> simp [Finch.stripe,Matrix.blockDiagonal_apply,Massive.Onsite.offset,he,hf]
    · intro b _ h; by_cases hx:i=j; subst j; simp [Finch.stripe,Matrix.blockDiagonal_apply,h]; simp [Finch.stripe,Matrix.blockDiagonal_apply,hx]
    simp
lemma daily (p m:ℝ): (⟨p,(0:Site c),fun _=>m⟩:Massive.Regulator c N).density U=primalD c N p m U:=rfl
variable (S T:Pixel c N)(p m:ℝ)
lemma visible (hK :Cove.light _ (S U)=primalD c N p m U)(z:ℂ): Cove.light _ (flux c u z S U)= primalD c N p m U * Massive.Pressure.Ray.mass u c z U:=by
    rw [flux,map_mul,hK,light_exp]; rw [map_smul]; rw [show Cove.light _ (_:EvenA c N)=Grass.form _ from panelised c u]; rfl
-- for complex beyond weighted state.
def splitR (t:ℝ)(x:ℝ): Flavor N→ℝ:= Massive.Pressure.Ray.path (fun _=>t) u x -- x t order
lemma prized (t:ℝ): (⟨p,0,splitR u m t⟩:Massive.Regulator c N).density U= primalD c N p m U * Massive.Pressure.Ray.mass u c t U:=by
    let T:Massive.Regulator c N:=⟨p,0,splitR u m t⟩; let V: Massive.Regulator c N:=⟨p,0,fun _=>m⟩; let D:= offset u (univ:Support c)
    rw [← daily c U p m]; have hD:T.D U=V.D U+(↑t:ℂ) • D:=by
      rw [unmasked T,unmasked V,add_assoc]; congr 1; ext i j; by_cases h:i=j<;> simp [D,T,V,Massive.Onsite.offset,splitR, Massive.Pressure.Ray.path,h]
    obtain ⟨A,hA⟩:= forge_linear c (N:=N); change T.density U=V.density U * _; rw [Massive.Regulator.density_apply, Massive.Regulator.density_apply,hD,gauss_add,← smul_mul_assoc]; refine congr_arg (fun y:Fields c N=> _*y) ?_ -- `*` meta issue.
    change exp (form ((t:ℂ) • D))=exp ((t:ℂ) • form D); rw [←hA,map_smul,hA]
lemma scaling (x:ℝ): ingredient c (x • u)=x • ingredient c u:=by
    unfold ingredient; rw [Finset.smul_sum]; refine sum_congr rfl fun i _=>?_ ; change unitL _ (x*u i.2) _=_; rw [Lscale]; exact (mul_smul x (u i.2) _).trans (congr_arg (x • ·) (Lscale i.2 i.1 _).symm)
lemma rise (s m:ℝ)(F:Pixel c N)(z:ℂ): flux c u ((s:ℂ)*(m:ℂ)*z) F=flux c ((s*m)•u) z F:=by
    funext U; apply congr_arg (F U * ·); apply congr_arg; change _=z • ingredient ..; rw [scaling c u]; let G:=ingredient c u; change _=z • ((↑(s*m):ℂ) • G); rw [smul_smul,Complex.ofReal_mul,mul_comm z]
end YM.QCD.Aperture
#print axioms YM.QCD.Aperture.panelised
#print axioms YM.QCD.Aperture.prized
