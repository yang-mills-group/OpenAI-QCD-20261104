import YM.Parishes.Settles
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
variable {c f C F L:Side} {J:Patch} {j kP k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j kP}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
open MeasureTheory
open MassiveQCD.Plate QCD.Kites Massive.Poised.Plans.Stamp
namespace Bank.Ontario
variable {Ua:YM.Source.Hol su}{V₁:YM.Massive.Lining.Temper.Collage.Exhibit Ua}{Θ:Massive.SourceRead.TaperHol}{M₁ M₂ M₃ M₄ t:ℝ}{Z0 Z1:Massive.UV.Label n}{A0:Cover}{q':Bool}
open Finset
variable {Y:Struck.Library.Code c 6}{pT:BudgetPoint}{z₀:ℂ}{Φ₁ Φ₂:Massive.Density c 6}{D:Grid c→ℝ}{T0:Run.St c}
variable (hSet:Settled Θ V₁ Y P pT a t k l m Z0 D T0 A0 z₀ q' M₁ M₂ Φ₁)(hx:Settled Θ V₁ Y P pT a t k l m Z1 D T0 A0 z₀ q' M₃ M₄ Φ₂)
variable (hP:Pilot Θ V₁ n pT.order pT.power l m k α A) (hX:∀ U',Summable (fun i=> ‖(Y.EvalK z₀).warp i U'‖))(ha:1≤a) (ht: 1≤t)(hv:30*(k+1) ≤ c.val)
include hSet hx hP hX ha ht hv
lemma joining : Settled Θ V₁ Y P pT a t k l m (Z0+Z1) D T0 A0 z₀ q' (M₁+M₃) (M₂+M₄) (Φ₁+Φ₂):=by
   obtain ⟨i,j,hI,hJ,U,he,hh⟩:= hSet.value; obtain ⟨k,u,hK,hU,X,hy,hb⟩:= hx.value
   refine ⟨_,_,inferInstance,inferInstance,sumup U X,sumupP _ _ he _ _ hy,?_⟩; rw [hh,hb]; exact funext fun i=> (gathered U (H:=Θ) i X he M₃ M₄ hy _ _ hP rfl rfl hv hX ha ht (by norm_num)).symm -- order
omit hx
lemma scaling (u:ℂ): Settled Θ V₁ Y P pT a t k l m (u • Z0) D T0 A0 z₀ q' (‖u‖*M₁) (‖u‖*M₂) (u • Φ₁):=by
    obtain ⟨i,j,hI,hJ,U,he,hh⟩:= hSet.value; refine ⟨_,_,hI,hJ, byG U u, byGP U he u,?_⟩; rw [hh]; exact funext fun i=> (applying U i he _ _ hP rfl rfl hv hX ha ht (by norm_num) u).symm
omit hSet
variable {ι:Type}
lemma eating (x:Finset ι)(hv':x.Nonempty)(f:ι→ℝ)(ψ:ι→Massive.UV.Label n)(φ:ι→Massive.Density c 6)(h':∀ i∈x,0≤f i)(he:∀ i∈x, Settled Θ V₁ Y P pT a t k l m (ψ i) D T0 A0 z₀ q' M₁ M₂ (φ i)) : Settled Θ V₁ Y P pT a t k l m (∑ i∈x,(f i:ℂ) • ψ i) D T0 A0 z₀ q' ((∑ i∈x,f i)*M₁) ((∑ i∈x,f i)*M₂) (∑ i∈x,(f i:ℂ) • φ i):=by
    induction x using Finset.induction_on with
    | empty=> exact (Finset.not_nonempty_empty hv').elim
    | insert i s hi ih=>
          simp_rw [sum_insert hi]; have hx:= scaling (he i (mem_insert_self ..)) hP hX ha ht hv (↑(f i)); rw [Complex.norm_real,Real.norm_of_nonneg (h' i (mem_insert_self ..))] at hx
          by_cases h:s.Nonempty; · rw [add_mul,add_mul]; exact joining hx (ih h (fun i h=>h' i (mem_insert_of_mem h)) (fun i h=> he _ (mem_insert_of_mem h))) hP hX ha ht hv -- mem args
          rw [Finset.not_nonempty_iff_eq_empty] at h; subst s; simpa using hx
omit hP hX ha ht hv
lemma pays_u (X:Settled Θ V₁ Y P pT a t k l m Z0 D T0 A0 z₀ q' M₁ M₂ Φ₁) (hp:M₁≤ M₃) (hb:M₂≤ M₄): Settled Θ V₁ Y P pT a t k l m Z0 D T0 A0 z₀ q' M₃ M₄ Φ₁:=by obtain ⟨i,j,hI,hJ,Yf,h,hS⟩:= X.value; exact ⟨_,_,hI,hJ,Yf, funds_hi _ h hp hb,hS⟩
end Bank.Ontario
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Bank.Ontario.eating
