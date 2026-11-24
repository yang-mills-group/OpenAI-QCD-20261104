import YM.QCD.Glass.Water
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
local notation "𝔹" => Twin
variable {t₀ p₀ u₀ v₀ θ:ℝ}{P' : ℝ→ℝ}
def Stepper (d m a b v x:ℝ) :Prop:=(d=a → x ≤ -v)∧ (d=b → v ≤ x)
structure MapL (x r t:ℝ)(D:Set Twin) (X:Twin→ℝ)(Y:Twin→ℝ)(F:Twin→Twin):Prop where
 clans:IsClosed D
 born: Continuous F
 goals (i:Twin): i∉D→ Walls (F i)
 site (i:Twin)(h:i∈D): X i=x+ r*Sq.tail (F i) ∧ Y i=t*mast (F i)
 chir (i:Twin)(j:Bool): |ray i j|=1 → ray (F i) j=ray i j
variable {f f' m₁ m₂:𝔹→ℝ}{D₀:Set Twin}
lemma hullT (G:𝔹→𝔹)(h:MapL x u v D₀ f m₁ G)(hp:0<t₀)(ht:0<p₀)(hh:ContinuousOn f' D₀)(hc:ContinuousOn m₂ D₀)(hX:∀ i∈ D₀, (f i=x-u→ f' i≤w-t₀)∧ (f i=x+u→ w+t₀ ≤ f' i))(hY:∀ i∈ D₀,ForceMass (m₁ i) v (m₂ i) p₀) : ∃ (D':Set Twin)(H:Twin→Twin),D'={i | i∈D₀∧ |f' i-w|≤t₀ ∧ |m₂ i|≤p₀} ∧ MapL w t₀ p₀ D' f' m₂ H:=by
    let D':={i | i∈D₀∧ |f' i-w|≤t₀ ∧ |m₂ i|≤p₀}
    let X(i):= (f' i-w)/t₀; let Y(i):=m₂ i/p₀
    have hD :IsClosed D':=by
        have he := (ContinuousOn.preimage_isClosed_of_isClosed (ContinuousOn.abs (hh.sub (continuousOn_const (c:=w)))) h.clans (isClosed_Iic (a:=t₀))) -- syntax
        let A:= {i|i∈D₀∧|m₂ i|≤p₀}; let B: Set Twin:= {i|i∈D₀∧|f' i-w|≤ t₀}; suffices H: IsClosed B by
              apply Eq.mp (congr_arg IsClosed (show B∩A=D' from by ext; simp only [B,A,D',Set.mem_inter_iff,Set.mem_setOf_eq]; tauto)); exact H.inter (ContinuousOn.preimage_isClosed_of_isClosed hc.abs h.clans isClosed_Iic) -- rename
        exact he
    have hx:ContinuousOn X D₀:= (hh.sub continuousOn_const).div_const _; have hz:ContinuousOn Y D₀:= hc.div_const _
    obtain ⟨F,hF,hP,hQ⟩:= mirrorP G X Y hx hz h.born h.clans (by
        intro i hi; have hp':= (h.site i hi).1; obtain ⟨h1,h2⟩:=hX i hi; refine ⟨fun H=>(le_div_iff₀ hp).mpr ?_,fun Q=>(div_le_iff₀ hp).mpr ?_⟩
        · rw [H,mul_one] at hp'; exact by linarith [h2 hp']
        rw [Q,mul_neg,mul_one, ←sub_eq_add_neg] at hp'; linarith [h1 hp']) (by
        intro i hi; have hp':= (h.site i hi).2; obtain ⟨h3,h4⟩:= hY i hi
        refine ⟨fun H=>(le_div_iff₀ ht).mpr ?_,fun Q=>(div_le_iff₀ ht).mpr ?_⟩
        · rw [H,mul_one] at hp'; linarith [h3 hp']
        rw [Q,mul_neg,mul_one] at hp'; linarith [h4 hp'])
    refine ⟨D',F,rfl,hD,hF,?_,?_, Sq.cohere G F hQ h.chir⟩
    · intro i hi; by_cases hp' : i∈D₀; swap; · exact Sq.awake hQ (h.goals i hp')
      rw [hP hp']; by_cases h: |X i|≤1; swap; · exact ⟨false,Sq.glance _ h⟩
      refine ⟨true,Sq.glance (Y i) ?_⟩; intro H; unfold X at h; unfold Y at H; rw [abs_div,abs_of_pos hp,div_le_iff₀ hp,one_mul] at h; rw [abs_div,abs_of_pos ht,div_le_iff₀ ht,one_mul] at H; exact hi ⟨hp',h,H⟩
    intro i hi; obtain ⟨hI,h1,h2⟩:=hi; rw [hP hI]; change f' i= w+t₀*(tap (X i)).val ∧ m₂ i=_; change _ ∧ m₂ i=p₀*(tap (Y i)).val
    unfold X Y; rw [tapped _ (by rw [abs_div,abs_of_pos hp,div_le_iff₀ hp,one_mul]; exact h1), tapped _ (by rw [abs_div,abs_of_pos ht,div_le_iff₀ ht,one_mul]; exact h2)]; constructor<;> field_simp <;> ring
end Rails
end YM.QCD.Acre
