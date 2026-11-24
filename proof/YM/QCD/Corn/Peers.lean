import YM.QCD.Corn.Swale
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
noncomputable def tideM (X:Pixel c N)(P: Insertion c N):Grid c→ℂ:=fun U=> ber _ (Cove.light _ (X U)*P U)
lemma tidePay (X:Pixel c N)(h:Continuous X)(P:Insertion c N): Integrable (tideM X P) (prior su c):=by
   let L:=LinearMap.toContinuousLinearMap (ber (Modes c N)); exact (L.continuous.comp (((Cove.lightC _).comp h).mul P.continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..)
noncomputable def stressP (X:Pixel c N)(P:Insertion c N):ℂ:= ∫ U,tideM X P U ∂prior su c
lemma paidM (X:Pixel c N)(h:Continuous X) : ∃ L: Insertion c N→L[ℂ]ℂ, stressP X=L:=by
    let F: Insertion c N→ₗ[ℂ]ℂ:= {
       toFun:=stressP X
       map_add':=fun A B=> by unfold stressP; rw [← integral_add (tidePay X h A) (tidePay X h B)]; exact integral_congr_ae (ae_of_all _ (fun _=>by simp [tideM,mul_add])) -- rw stress def
       map_smul':=fun a A => by change (∫ i,tideM X _ i ∂_)= a • (∫ i,_ ∂_); rw [← integral_smul]; apply integral_congr_ae; apply ae_of_all; intro j; unfold tideM; simp only [ContinuousMap.smul_apply,mul_smul_comm, map_smul] }
    let G:= LinearMap.toContinuousLinearMap (ber (Modes c N)); obtain ⟨K,hK⟩:= (((Cove.lightC _).comp h).norm).bounded_above_of_compact_support (HasCompactSupport.of_compactSpace ..)
    suffices hP:∀ x,‖F x‖≤ ‖G‖*K*‖x‖ from ⟨F.mkContinuous _ hP,rfl⟩
    intro x; refine (norm_integral_le_of_norm_le (integrable_const (μ:=prior su c) (‖G‖*K*‖x‖)) (ae_of_all _ (fun i=>?_))).trans (by simp)
    · have hv: ‖Cove.light _ (X i)‖ ≤ K:= (show ‖(⇑(Cove.light (Cove.Keys c N)) ∘ X) i‖≤ K from (by simpa only [norm_norm] using hK i))
      change ‖G ((Cove.light _ (X i))*x i)‖ ≤ _; rw [mul_assoc]; exact (G.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans (mul_le_mul hv (ContinuousMap.norm_coe_le_norm x i) (norm_nonneg _) ((norm_nonneg _).trans hv))) (norm_nonneg _))
lemma stamen (X:Pixel c N)(h:Continuous X)(he:shadeG X)(P:Insertion c N)(k:Frame c): stressP X (Lat.transform k P)=stressP X P:=by
    unfold stressP; have hh:= tidePay X h P; have hp:=prior_gauge k; nth_rw 2 [← hp.map_eq]; rw [integral_map hp.aemeasurable (hp.map_eq.symm ▸ hh.1)]; apply integral_congr_ae; apply ae_of_all; intro i; unfold tideM; dsimp only; rw [← no_jac N k (Cove.light _ (X (gauge k i)) * P (gauge k i)),map_mul (Lat.slots N k)]; apply congr_arg; exact congr_arg (· * (Lat.transform k P i)) ((he i k).symm)
-- Haar groupT
lemma cupR (U:Insertion c N)(P:Continuous (fun k:Lat.Frame c × Grid c=>Lat.slots N k.1 (U (Lattice.gauge k.1 k.2)))): Continuous fun k=>Lat.transform k U:= ContinuousMap.continuous_of_continuous_uncurry _ P
lemma rotZ (X: Side)(F:ℕ): Continuous (fun k:Lat.Frame X × Fields X F=> Lat.slots F k.1 k.2):= Land.turn_c
lemma pullL {X U A S:Type}[TopologicalSpace X][TopologicalSpace U][TopologicalSpace S][TopologicalSpace A](Z:X×U→U)(H:X×A→S)(V:U→A) (hc:Continuous V)(hp:Continuous H)(hx:Continuous Z): Continuous fun q:X×U => H (q.1,V (Z q)):= hp.comp (continuous_fst.prodMk (hc.comp hx))
lemma dyeP (X:Insertion c N):Continuous fun k=>Lat.transform k X:=by
    let f:=fun p:Frame c × Grid c=> gauge p.1 p.2
    have hp:Continuous f:=by apply continuous_pi; intro i; unfold f Lattice.gauge; fun_prop
    apply cupR
    exact pullL f _ _ X.continuous (rotZ c N) hp
lemma sealT (X:Insertion c N)(u:Frame c):∃ L: Insertion c N→L[ℂ]Insertion c N, Lat.transform (F:=N) u=L:=by
    let F :Insertion c N→ₗ[ℂ]Insertion c N:={
       toFun:= Lat.transform u
       map_add':=fun x y=>by ext1 p; exact map_add (Lat.slots N u) ..
       map_smul':=fun x y=>by ext1 p; exact map_smul (Lat.slots N u) .. }
    let T:= LinearMap.toContinuousLinearMap ((Lat.slots N u).toLinearMap)
    suffices h:∀ x, ‖F x‖≤ ‖T‖*‖x‖ from ⟨F.mkContinuous _ h, rfl⟩
    intro x; exact (ContinuousMap.norm_le _ (by positivity)).2 fun i=> (T.le_opNorm (x (gauge u i))).trans (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm x _) (norm_nonneg _))
lemma paintsX (X: Pixel c N)(hX:Continuous X)(h:shadeG X)(P: Insertion c N): let Q:= ∫ k, Lat.transform k P ∂Patron.brine c
     Invariant Q ∧ stressP X P=stressP X Q:=by
    intro R; have hp:= (dyeP P).integrable_of_hasCompactSupport (μ:=Patron.brine c) (HasCompactSupport.of_compactSpace ..)
    constructor
    · intro k; obtain ⟨L,hL⟩:= sealT P k; rw [hL]; unfold R; rw [← L.integral_comp_comm hp, ← hL]; let ν:= brine c
      have hz:MeasurePreserving (fun i:Frame c=> i*k) (brine c) (brine c):=measurePreserving_pi _ _ (f:= fun i (g : su.El) => g*k i) (fun i => measurePreserving_mul_right _ _)
      conv_rhs=> rw [←hz.map_eq]; -- syntax ν expand
      rw [integral_map hz.aemeasurable (hz.map_eq.symm ▸ hp.1)]; apply integral_congr_ae; apply ae_of_all; intro i; ext1 z
      have hh:gauge i (gauge k z)=gauge (i*k) z:=by funext a; unfold Lattice.gauge; simp only [Pi.mul_apply]; group
      change Lat.slots N k (Lat.slots N i (P _)) = Lat.slots N _ (P _); rw [hh]; exact Land.turning ..
    obtain ⟨M,hM⟩:=paidM X hX; unfold R; rw [hM,← M.integral_comp_comm hp,← hM]; simp_rw [stamen X hX h]; simp
end Rails
end YM.QCD.Acre
