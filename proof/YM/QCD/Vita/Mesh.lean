import YM.QCD.Vita.Rating
import Mathlib.Topology.MetricSpace.Equicontinuity
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
variable {j:ℕ} (B:SparkMesh)(O:Patch)
section limit
variable {S:ℕ→ℕ}(V U W:ℕ→ℕ→ℝ)(P: ℕ→∀ i,Pixel (finC O B i k) N)
variable (hp:∀ n:ℕ, Candor O B K M Rᵥ N n k x κ r (V n) (U n) (W n) (P n)) (ht:∀ i, 0<Rᵥ i)(hK:O.Branches K su) (hm:∀ y,x≤y→ Shade O.L r y)
noncomputable abbrev Knot (t:ℕ): Set (ℝ×ℝ×ℝ):= Set.Icc (GaugeM O t x/2) (2*GaugeM O t x) ×ˢ Set.Icc (-(rangeG O t 0 κ r x)) (rangeG O t 0 κ r x) ×ˢ Set.Icc (Rᵥ t) 4
abbrev RealY (t:ℕ)(q:ℕ):ℝ×ℝ×ℝ:= (V q t,U q t,W q t)
structure Hook (Q:ℕ→ℕ) (V₀ U₀ W₀:ℕ→ℝ) (X:∀ i,Pixel (finC O B i k) N):Prop where
   hm (j:ℕ): Tendsto (fun v=> RealY V U W j (Q v)) atTop (𝓝 (V₀ j,U₀ j,W₀ j))
   hx (j:ℕ):∃ (Y:ℕ→ ContinuousMap (Grid (finC O B j k)) (EvenA (finC O B j k) N))(H:ContinuousMap (Grid (finC O B j k)) (EvenA (finC O B j k) N)), (∀ᶠ i in atTop, (Y i).toFun=P (Q i) j) ∧ X j= H.toFun∧ Tendsto Y atTop (𝓝 H)
include hp hK ht hm
abbrev Silk (B:Side)(N:ℕ):Type:=ContinuousMap (Grid B) (EvenA B N)
lemma drum (i:ℕ):∃ A:ℕ→Silk (finC O B i k) N, (∀ n:ℕ,i<n→ (A n).toFun=P n i) ∧ IsCompact (closure (Set.range A)):=by
    let c:=finC O B i k; let f:=finC O B (i+1) k; let T n:= P n i; have hΓ(n:ℕ)(h:i+1≤n): Continuous (T n):= ((hp n).capital i (le_trans (by omega) h)).1
    have hh(n:ℕ)(h:i+1 ≤ n): ∀ x,‖T n x‖ ≤M i:= ((hp n).capital i (by omega)).2.2.2.1; have hx(ε:ℝ)(he:0<ε):∃ δ:ℝ,0 < δ∧∀ n:ℕ,i+1 ≤ n →∀ x y, dist x y <δ → dist (T n x) (T n y)< ε:=by
        let u:= GaugeM O (i+1) x; have hu:0 < u:= (hm _ (matters ..)).value
        obtain ⟨δ,hδ,hT⟩:= descent (N:=N) (Pike O 0) hK (powerV B O i k) (Rᵥ i) (2*u) (M (i+1)) (ht i) he; refine ⟨δ,hδ,fun n hn=>?_⟩
        obtain ⟨hp₀,h,h₁,h₂,h₃,h₄,h₅⟩:= (hp n).capital (i+1) hn; obtain ⟨hz,hH,hQ⟩:= (hp n).vocals i hn; exact hT (P n (i+1)) _ hp₀ h₂ _ _ ((abs_of_nonneg (show 0 ≤ V n (i+1) from (lt_of_lt_of_le (half_pos hu) h₃).le)).trans_le h₄) ⟨hH,hz⟩ (versed _ _ _ ((ht i).trans_le hH) hQ)
    obtain ⟨A,hA,hx'⟩:= ridge T _ (i+1) hΓ hh hx; exact ⟨A,fun n hn=> Eq.trans (congr_arg ContinuousMap.toFun (hA _ hn)) (congr_arg T (max_eq_right hn)),hx'⟩
lemma meshV :∃ Q:Extraction.Sequence,∃ V₀ U₀ W₀ X, Hook B O V U W P Q V₀ U₀ W₀ X:=by
    choose Z hZ hc using drum B O V U W P hp ht hK hm; let X i:= Knot (x:=x) (κ:=κ) (Rᵥ:=Rᵥ) (r:=r) O i; have hx i : IsCompact (X i):= isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    let T i n:=(RealY V U W i n, Z i n); have hX(i:ℕ):∀ᶠ n:ℕ in atTop,T i n ∈ X i ×ˢ closure (Set.range (Z i)) := by
         filter_upwards [eventually_gt_atTop i] with n hn; obtain ⟨_,_,_,_,h,hp',hr⟩:= (hp n).capital i hn.le; obtain ⟨he,hv,_⟩:= (hp n).vocals i hn; exact ⟨⟨⟨h,hp'⟩,abs_le.mp hr,hv,he⟩, subset_closure ⟨n,rfl⟩⟩
    obtain ⟨q,Y,hQ⟩:= Extraction.simultaneous T (fun i=> (hx i).prod (hc i)) hX; refine ⟨q,(fun i=>(Y i).1.1),(fun i=>(Y i).1.2.1),(fun i=>(Y i).1.2.2),(fun i=> (Y i).2.toFun),fun i=> (continuous_fst.tendsto (Y i)).comp (hQ i).2, fun i=> ⟨fun j=> Z i (q j),(Y i).2,(q.cofinal.eventually (eventually_gt_atTop i)).mono (fun j hh=> hZ i _ hh),rfl,continuous_snd.continuousAt.tendsto.comp (hQ i).2⟩⟩
omit hp hK ht hm
lemma allowY {q:ℕ→ℕ} {V₀ U₀ W₀:ℕ→ℝ}{Y:∀ i,Pixel (finC O B i k) N}(hx: Hook B O V U W P q V₀ U₀ W₀ Y): ∀ i, Continuous (Y i) ∧∀ x,Tendsto (fun j=>P (q j) i x) atTop (𝓝 (Y i x)):=by
    intro i; obtain ⟨Z,R,hZ,hR,hQ⟩:= hx.hx i; rw [hR]; exact ⟨R.continuous,fun x=> ((continuous_eval_const x|>.continuousAt (x:=R)).tendsto.comp hQ).congr' (hZ.mono fun i hi=>congr_fun hi _)⟩
-- preserves each. 
end limit
end Rails
end YM.QCD.Acre
