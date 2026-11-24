import YM.QCD.Rain.Majesty
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
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open Rain PulseRide
variable {O:Patch} {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{U V Wv Y:ℕ→ℝ}
variable {τ':Policy Q T'.top N}(B:SparkMesh){S':ℕ→SparkMesh}(b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n)
variable {T₁:ℕ→Towers O.L}{V₁:ℕ→Bed}{b₀:ℕ→ℝ}
variable (A0:∀ i,Pixel (towerQ O B n i k) N) (hG: Stargate T' B b' g P' X Y κ x τ'.t D W' k V U Wv A0)
-- publication.Evaluation
open Sway OrbitG MeasureTheory
structure ProperF (Q:Pixel c N):Prop where
   gauges : shadeG Q
   fluteC (i:Grid c): Fit (Q i)
lemma garbs {Y:Pixel c N}(he:∀ i,Cove.light _ (Y i)=primalD c N u v i): ProperF Y:=by
    let K:Lat.Cut c N:= ⟨u,0,v⟩
    constructor
    · intro i g; rw [he,he]; unfold primalD; rw [bare_gauge]; change Lat.slots N g ((bare u i:ℂ) • K.insertD (Lattice.gauge g i))=_; rw [map_smul]; exact congr_arg _ (invariant_weight g K i)
    intro i A h; let M:=Sway.flute (Lat.Row c) A
    apply Subtype.ext; change disguise M (Cove.light _ (Y i))= Cove.light _ _; rw [he,primalD]; change disguise M ((bare u i:ℂ) • K.insertD i)=_; rw [map_smul]; apply congr_arg
    have hp:M*K.ferm i* star M=K.ferm i:=by rw [show M*K.ferm i=K.ferm i*M from (Sway.column _ A), Matrix.mul_assoc, (show M*star M=1 from (Sway.unit_f h).2),Matrix.mul_one]
    have hx:= disguised (R:=M) (Sway.unit_f h) (K.ferm i); rw [hp] at hx; exact hx
-- same op.Q Haar.K
lemma marchP (Z:Pixel f N)(T:Pixel c N)(w u:ℝ)(hK:S.patch.Branches K su)(hp:ProperF Z)(hx:Continuous Z)(hr:0<w)(ht:∀ U,advance S K h Z u U=gBody c w (T U)): ProperF T:=by
    let Y:= S.visit K h; let C:= can S h N Z; have hg:= (Rain.tenderL S h Z hx).integrable_of_hasCompactSupport (μ:=prior su f) (HasCompactSupport.of_compactSpace ..); have hX:= Y.isKernel hK u
    let X:= advance S K h Z u
    have hm (M: Matrix (Modes c N) (Modes c N) ℂ)(U V:Grid c)(p:disguise M (X V)=X U): sways M (T V)=T U:=by
        have hs: sways M (wearK c N w⁻¹ (T V))=wearK c N w⁻¹ (T U):=Subtype.ext ((congr_arg (disguise M) (ht V).symm).trans (p.trans (ht U)))
        rw [purity] at hs; have hv:= congr_arg (wearK c N w) hs; rwa [wit _ _ _ (mul_inv_cancel₀ hr.ne'), wit _ _ _ (mul_inv_cancel₀ hr.ne')] at hv
    -- transport matrix insert in integrand 
    have hh (U V:Grid c) (M: Matrix (Modes c N) (Modes c N) ℂ) (P:Grid f→Grid f)(hP:MeasurePreserving P (prior su f) (prior su f))(hD:∀ A:Grid f, Y.density u (P A) V= Y.density u A U)(hC:∀ A:Grid f, disguise M (C (P A))=C A) : disguise M (X V) =X U:=by
         let W:= LinearMap.toContinuousLinearMap ((disguise M).toLinearMap.restrictScalars ℝ); let z(x:Grid f):=Y.density u x V • C x; have hk:Integrable z (prior su f):= Y.push_slice hX V C hg; have he: (∫ i,z i ∂prior su f) = ∫ i,z (P i) ∂prior su f:=by
              conv_lhs=> rw [← hP.map_eq]; exact integral_map hP.aemeasurable (hP.map_eq.symm ▸ hk.1)
         change W (∫ i,z i ∂prior su f)= _; rw [he, ← W.integral_comp_comm (show Integrable (fun i:Grid f=> z (P i)) (prior su f) from hP.integrable_comp_of_integrable hk)]; refine integral_congr_ae (ae_of_all _ fun i=>?_); change W (Y.density u (P i) V • C (P i))= _; rw [map_smul,hD]; exact congr_arg _ (hC i) -- congr
    refine ⟨fun V k=> ?_,fun i A H=>?_⟩
    · let q:= k ∘ Y.ratio.parent; let W: Matrix (Modes f N) (Modes f N) ℂ:=Lat.rotates N q; let D: Matrix (Modes c N) (Modes c N) ℂ:=Lat.rotates N k; have hq: q∘ Y.ratio.embed=k:=funext fun i=> congr_arg k (Y.ratio.embed_parent i)
      refine congr_arg Subtype.val (hm D V _ (hh V _ D (Lattice.gauge q) (prior_gauge _) (fun i=>by rw [← hq]; exact Y.covary hK ..) ?_)); intro i; unfold C can; rw [show ater S h (F:=N) (gauge q i)=(D*ater S h (F:=N) i:Matrix (Modes c N) (Modes f N) ℂ)*star W from ?_,compat (R:=W) (W:=D) (rotates_law ..) (rotates_law ..)]
      · exact congr_arg _ (hp.gauges ..)
      unfold D W ater; rw [gauges, show q ∘ (sliceL S h).embed=k from hq, choir_mul,choir_mul,Matrix.star_eq_conjTranspose,choir_star]; rfl -- star choir
    let M: Matrix (Modes c N) (Modes c N) ℂ:=Sway.flute (Lat.Row c) A; let D: Matrix (Modes f N) (Modes f N) ℂ:=Sway.flute (Lat.Row f) A; have hd:D∈unitary _:= Sway.unit_f H
    refine hm M i i (hh i i M id (MeasurePreserving.id _) (fun _=>rfl) ?_); intro V; let z:=ater S h (F:=N) V
    have hv : M*z*star D=z:=by rw [show M*z=z*D from (Sway.column _ _),Matrix.mul_assoc, (show _ from hd.2),Matrix.mul_one]
    have he:= Kit.compat (R:=D) (W:=M) hd (Sway.unit_f H) 1 z (Cove.light _ (Z V)); rw [hv] at he; exact he.trans (congr_arg (Kit.sheath _ z) (congr_arg Subtype.val (hp.fluteC V A H))) -- RHS eq
include hG
lemma schooled (hv: Even N)(hk:O.Branches T'.bind su)(h:i≤n) : ProperF (A0 i):=by
    induction i with
    | zero=> exact garbs hG.begin
    | succ i ih=>
         obtain ⟨h,hx,hH,hp⟩:=hG.vocals i h
         apply marchP (A0 i) (A0 (i+1)) (Wv i) (V i) (S:=Pike O i) (K:=T'.bind) (h:=lift0 B _) hk (ih _) (Rain.firms _ g _ A0 hG hk hv _ (by omega)).1 h hp
         all_goals omega
end Rails
end YM.QCD.Acre
