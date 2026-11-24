import YM.VStages.AriseY
/-! # Chart maintenance in the presence of arbitrary spectator sources

The preceding measure-level expansion outfits make an unmarked rail at every chart.
The marked expansion adjoins to the rail, so knowing the *total* evolution of the unmarked
is not enough. We track exponents and the strides of the individual weighted soft corrections.
Obtain an identity of the exponentials without requiring any nonvanishing of the hard-sector
rail at a given large field. `sum_buds` style observations remain valid after this linking.
-/
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
variable {c f C F L:Side} {J:Patch} {kP₀ j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j kP₀}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet Footprint Push.Local Shard DoorKit Badge Adornment
namespace Rails
namespace Links
open LicenseM
open Grass Patron Struck Library Weft Fibre NormedSpace
open High Meridians Ruby High.PrismT Finset
/- Test Rails at a point with its exact flags. -/
lemma known T (V:Grid c) : ∃ (J:Type)(_ : Countable J)(X:Patron.Rail c N J), (∀ v,Summable (Ruby.tK X T v))∧ Kites.heartK X T V=1:=by
    by_cases H : (RG.flags T V).Nonempty
    · let X:Patron.Rail c N Unit := ⟨fun _=>⟨RG.flags T V,RG.flags T V,H,le_refl _⟩,fun _ _=>1⟩; refine ⟨Unit,inferInstance,X,fun _=> Summable.of_finite,?_⟩; unfold heartK; rw [tsum_eq_single ({()}) ?hs]; swap
      · intro i hi; have he:i=∅:=not_nonempty_iff_eq_empty.mp fun hg=> hi (ext (fun j=>by have h:i.Nonempty:=hg; obtain ⟨l,hl⟩:=h; rw [mem_singleton]; simpa only [Subsingleton.elim l j] using (show l∈i ↔ True from iff_true_intro hl)))
        unfold tK; rw [if_neg]; simp [he,H.ne_empty]
      unfold tK; rw [if_pos,prod_singleton]
      refine ⟨?_,by rw [singleton_biUnion]; rfl⟩
      rw [GasP.close]; simp
    let X:Patron.Rail c N Empty:=⟨nofun,nofun⟩; refine ⟨Empty,inferInstance,X,fun _=>Summable.of_finite,?_⟩; unfold heartK; rw [tsum_eq_single ∅ (fun j h=>False.elim (h (Subsingleton.elim ..))),tK,if_pos,prod_empty]; rw [GasP.close]; simp [not_nonempty_iff_eq_empty.mp H]
section common
abbrev enveloped (t:ℝ)(K:Patron.Rail c N I)(E:EvenA c N)(V:Grid c):= E*heartK K t V
local notation "bz"=> P.threshold
lemma firstWire (A B:EvenA c N)(t r:ℝ)(u:ℂ)(C: BudgetPoint)(G: Ruby.Hue c N I)(a c₀ z:ℝ)(hA:Purchases G C.threshold C.B a c₀ z)(V:Grid c)(hh:0≤a)(he:1≤z)(hr:t=C.threshold)(hp:∀ (J:Type)[Countable J] (F: Patron.Rail c N J), (∀ x,Summable (Ruby.tK F t x))→ wearK c N r (enveloped t F A V)= u • enveloped t (flightK (Trail G F t) r) B V):
       wearK c N r A= u • (B * wearK c N r (exp (swarm G V))):= by
    obtain ⟨J,hJ,F,hS,hC⟩:=known t (c:=c) (N:=N) V; have h:= hp J F hS
    obtain ⟨h1,h2⟩:=Kites.heart G hA hh he V
    have hx:= Ruby.plenary G F V (hS V) (hr.symm ▸ hA.life) h1 h2
    unfold enveloped at h; rw [show heartK _ _ _= _ from (story (Trail G F t) V r t hx.summable).tsum_eq] at h
    rw [show (∑' i,tK _ _ _ i)=heartK F t V * NormedSpace.exp (swarm G V) from hx.tsum_eq,hC,mul_one,one_mul] at h; exact h
lemma laterWire (A B:EvenA c N)(C: BudgetPoint)(G: Ruby.Hue c N I)(r a c₀ z:ℝ)(hA: Purchases G C.threshold C.B a c₀ z)(V:Grid c)(hh:0≤a)(he:1 ≤ z)(hp:∀ (J:Type)[Countable J] (F:Patron.Rail c N J),(∀ x,Summable (Ruby.tK F C.threshold x))→ wearK c N r (enveloped C.threshold F A V)=enveloped C.threshold (Trail G (flightK F r) C.threshold) B V):
       wearK c N r A=B*exp (swarm G V):=by
    obtain ⟨J,hJ,F,hS,hC⟩:=known C.threshold (c:=c) (N:=N) V; have h:=hp J F hS
    obtain ⟨h1,h2⟩:=Kites.heart G hA hh he V; have hv:=story F V r C.threshold (hS V)
    have hx:= Ruby.plenary G (flightK F r) V hv.summable hA.life h1 h2
    unfold enveloped at h; rw [show heartK _ _ _ = _ from hx.tsum_eq,show (∑' i,tK _ _ _ i)= wearK c N r (heartK F C.threshold V) from hv.tsum_eq,hC,map_one,mul_one,one_mul] at h; exact h
-- K support persistence with real masks for grafting
abbrev Envelope (c:Side)(N:ℕ):= Sigma (Patron.Rail c N)
abbrev toEnv {J:Type} (K:Patron.Rail c N J):Envelope c N:=⟨J,K⟩
lemma env_finish (X:ℂ→ℂ→ Patron.Rail c N I)(Y:ℂ→ℂ→ Ruby.Hue c N J')(t:ℝ) (hA: Arc X)(hp:Arch Y)(z s:ℂ): toEnv (graffiti X Y t z s)=toEnv (Trail (Y z s) (X z s) t):= congr_arg₂ (fun Y X=> toEnv (Trail Y X t)) (hp.equal Y z s) (hA.equal X z s)
lemma env_wears {E':Type} (r:ℝ)(X:Patron.Rail c N I)(Y: Patron.Rail c N E')(h: toEnv X=toEnv Y):toEnv (flightK X r)=toEnv (flightK Y r):=congr_arg (fun Z:Envelope c N=>toEnv (flightK Z.snd r)) h
lemma env_trail {E':Type}(r:ℝ)(G:Ruby.Hue c N J')(X:Patron.Rail c N I)(Y:Patron.Rail c N E')(h:toEnv X=toEnv Y):toEnv (Trail G X r)=toEnv (Trail G Y r):=congr_arg (fun Z:Envelope c N=>toEnv (Trail G Z.snd r)) h
lemma twiceM (x:EvenA c N) (s t:ℝ): wearK c N s (wearK c N t x)=wearK c N (s*t) x:= Subtype.ext (Kites.makes x.val s t)
lemma flight_add (X:Patron.Rail c N I)(r s:ℝ): flightK (flightK X r) s= flightK X (s*r):=by unfold flightK; congr! 2; funext U; exact twiceM _ s r
end common
end Links
end Rails
end YM.QCD.Acre
