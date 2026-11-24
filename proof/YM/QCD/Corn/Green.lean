import YM.QCD.Corn.Peers
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
lemma inject (X Y:Pixel c N)(hx:Continuous X)(hp:Continuous Y)(h:∀ Z:Insertion c N,stressP X Z=stressP Y Z) : X=Y:=by
     let M:=Modes c N; let L(V: Pixel c N):=fun (i:Grid c)=> Cove.light _ (V i)
     funext i; apply Subtype.ext; change L X i=L Y i; apply (perfect (Modes c N)).injective; apply LinearMap.ext; intro U
     let z(V:Grid c):= ber M (L X V*U)-ber M (L Y V*U); have he (V:Pixel c N)(hp:Continuous V): Continuous (fun i:Grid c=> ber M (L V i*U)):= (ber M).continuous_of_finiteDimensional.comp (((Cove.lightC _).comp hp).mul continuous_const)
     have hz : Continuous z:= (he X hx).sub (he Y hp); let S:Insertion c N:=⟨fun i=>star (z i) • U,hz.star.smul continuous_const⟩
     have hf : Integrable (fun i=>‖z i‖^2) (prior su c):=(hz.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..)
     have hv: (∫ i, ‖z i‖^2 ∂prior su c)=0:=by
            apply Complex.ofReal_injective; rw [← integral_complex_ofReal,Complex.ofReal_zero,← sub_eq_zero.mpr (h S)]; unfold stressP; rw [← integral_sub (tidePay X hx S) (tidePay Y hp S)]
            apply integral_congr_ae; apply ae_of_all; intro i; dsimp only; rw [show ∀ V,tideM V S i=star (z i)* ber M (L V i*U) from (fun V=>by unfold tideM; rw [show S i= star (z i) • U from rfl,mul_smul_comm,map_smul]; rfl), show tideM Y S i=star (z i)* ber M (L Y i*U) from (by unfold tideM; rw [show S i= star (z i) • U from rfl,mul_smul_comm,map_smul]; rfl), ← mul_sub]; change _=star (z i)*z i; rw [mul_comm, Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
     haveI:(prior su c).IsOpenPosMeasure:=by unfold prior; infer_instance
     have hw: (fun i=> ‖z i‖^2)=0:= ((hz.norm.pow 2).ae_eq_iff_eq (prior su c) continuous_zero).mp ((integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _=>sq_nonneg _) hf).1 hv); have ht : ‖z i‖^2=0:=congr_fun hw i; have he: z i=0:= norm_eq_zero.mp (by nlinarith [norm_nonneg (z i)])
     simp only [perfect_apply]; exact sub_eq_zero.mp he
-- quantifies broad.Insert. coercion gauge-averaged
abbrev JoinsF (X:Pixel c N) : Prop:= ∀ P:Pixel c N, Continuous P → shadeG P → Maison c N P → ∃ V: Insertion c N, Invariant V ∧ stressP X V ≠ stressP P V
lemma growsF (X:Pixel c N)(hp:Continuous X)(b:Flavor N)(he:ConvexF X b) : JoinsF X:=by
    intro P hP hQ h; by_contra! ht; apply coupler X b he; suffices h:X=P by rw [h]; assumption
    apply inject X P hp hP; intro Z; obtain ⟨hv,hY⟩:= paintsX X hp he.proper.gauges Z; obtain ⟨hZ,hT⟩:= paintsX P hP hQ Z; exact hY.trans ((ht _ hv).trans hT.symm)
end Rails
end YM.QCD.Acre
