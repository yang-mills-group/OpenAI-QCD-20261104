import YM.VStages.MirrorW
import YM.VStages.SquareM
import YM.QCD.Rain.Majesty
import YM.Massive.Tuner.Limits
import YM.Massive.Pressure.Smoothed
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rain
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {c L:Side}{k₀ N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar Acre Rails Pressure ConnectedActivityE6 Cost Free Pine
open Acre Rails PhysicalNext.Repeat Raft ParcelR Sq
variable {f:Side}{k: ℕ}{K:KernelChoices}
-- namespaces.Tuning uses j
section sol
variable (S:YM.Next.Free.Flight j k₀)(h: f.val=c.val*S.L.val)(X:Pixel f N)(T:KernelChoices)
lemma tenderLQ (he:Continuous X):Continuous (canQ S h N X):=by
      have hf : Continuous (fun i:Grid f=> (ater S h i (F:=N),Cove.light (Keys f N) (X i))) := (signsQ (S:=S) (h:=h) (N:=N)).prodMk ((lightC (Keys f N)).comp he)
      have hp := (Kit.sheath_cont (A:=Modes f N) (B:=Modes c N) (b:=1)).comp hf
      exact hp
variable (hK:S.patch.Branches T su) (hx: Continuous X)
include hx hK
set_option maxHeartbeats 700000 in
lemma livingQ (p:ℝ): Continuous (advanceF S T h X p):=by
     rw [continuous_iff_continuousAt]; intro i; rw [← continuousWithinAt_univ]; have he:Integrable (canQ S h N X) (prior su f):=(tenderLQ S h X hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..); exact (Push.BetaTransport.push_continuousWithinAt (S.visit T h) hK (b:=fun _=>p) (y:=i) continuousWithinAt_const continuousWithinAt_id (V:=id) (F:=fun _=>canQ S h N X) he (Eventually.of_forall fun _=> he.1) (ae_of_all _ fun _=> continuousWithinAt_const) he.norm (Eventually.of_forall fun _=> ae_of_all _ fun _=> le_rfl)).2
lemma assetsQ (w:ℝ)(V:Grid c)(hV: realP X) : let u:= ber _ (advanceF S T h X w V); u=(u.re:ℂ)∧ 0 ≤ u.re:=by
   intro z; let Y:= S.visit T h; have hh:Y.IsKernel w su:=Y.isKernel hK _
   have he:=Y.push_slice hh V _ ((tenderLQ S h X hx).integrable_of_hasCompactSupport (μ:=prior su f) (HasCompactSupport.of_compactSpace (f:=canQ S h N X) ..)) -- signature
   let l (i:Grid f):= Y.density w i V; let H:=LinearMap.toContinuousLinearMap (ber (Modes c N)); let g (i:Grid f):= l i*(cBer X i).re
   have hz(i:Grid f):H (l i • canQ S h N X i)=(g i:ℂ):=by
       rw [show l i • canQ S h N X i= ((l i):ℂ) • _ from rfl,map_smul]; change ((l i):ℂ)*ber _ (sheath 1 (ater S h i) _)=_; rw [insulate (by norm_num : (1:ℝ)≠ 0)]; change ↑(l i)*cBer X i =_; rw [(hV i).1]; unfold g; norm_cast -- bad rewriting re
   have hm:z= ((∫ i,g i ∂prior su _) :ℝ):=by
        change H (∫ i, l i • canQ S h N X i ∂prior su f) =_; rw [← H.integral_comp_comm he]; rw [← integral_complex_ofReal]; apply integral_congr_ae (ae_of_all _ hz)
   rw [hm]; exact ⟨rfl,integral_nonneg (fun i=> mul_nonneg (hh.positive _ _) (hV i).2)⟩
lemma marchingQ (w:ℝ) (Y:Pixel c N)(hp:0<t)(he:∀ i,advanceF S T h X w i=gBody _ t (Y i)) : Continuous Y ∧ Cvol X=gain t⁻¹ c N • Cvol Y:=by
    have hv i:Y i=(songT t) (fortQ S T h N w X i):=by rw [fortQ, Function.comp_apply,he, gBody,callH]; exact (wit _ _ _ (mul_inv_cancel₀ hp.ne')).symm
    let R:=canQ S h N X; let F:=S.visit T h; have hI:F.IsKernel w su:=F.isKernel hK _; have he' :Integrable R (prior su f):=(tenderLQ S h X hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..); have hp' := F.push_integrable hI _ he'; let G:=LinearMap.toContinuousLinearMap (ber (Modes c N))
    constructor
    · rw [funext hv]; exact Continuous.comp (songT t|>.continuous) ((levit c N).continuous.comp (livingQ _ _ _ _ hK hx _))
    have hJ:Cvol X = ∫ V:Grid c, G (advanceF S T h X w V) ∂prior su c:=by
          unfold advanceF; rw [G.integral_comp_comm hp', F.push_integral hI R he', ← G.integral_comp_comm he']; unfold Cvol; apply integral_congr_ae (ae_of_all _ fun _=>?_); exact (insulate (by norm_num : (1:ℝ)≠ 0) _ _).symm
    rw [hJ,←integral_smul]; refine integral_congr_ae (ae_of_all _ fun i=>?_); dsimp only; rw [he]; exact crestP ..
end sol
end YM.QCD.Rain

namespace YM.QCD.Rain
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {c L:Side}{k₀ N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar Acre Rails Pressure ConnectedActivityE6 Cost Free Pine
open Raft ParcelR PhysicalNext.Repeat Next.Free Acre Rails Precision ConnectedActivityE6
variable {T':Teller su}{V':ConnectedActivityE6.Target su T'}{O:Patch}{Ω:ParcelR}{Y U W V: ℕ→ℝ}{X:ℕ→SunR Ω}{P':ℕ→BudgetPoint}{Q: Policy V' T'.top N}{t:ℕ}{f:Side} {Λ:ℝ}
lemma sunlightQ (S:Flight j k₀)(h:f.val=c.val*S.L.val)(K:KernelChoices)(p t:ℝ)(X:Pixel f N)(Y:Pixel c N)(he:0<t)(hK:S.patch.Branches K su)(hx:Continuous X)(hp:∀ i,advanceF S K h X p i=gBody _ t (Y i))(hX:realP X): realP Y:=by
     intro i; have hz : ber _ (advanceF S K h X p i)= (gain t⁻¹ c N:ℂ)*cBer Y i:=by rw [hp]; exact crestP ..
     obtain ⟨hr,hh⟩:= assetsQ S h X K hK hx p i hX; let G:=gain t⁻¹ c N; have he':0<G:=pow_pos (inv_pos.mpr he) _
     rw [hz, Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr hh
     exact ⟨mul_left_cancel₀ (show (G:ℂ) ≠0 from by exact_mod_cast he'.ne') (hr.trans (Complex.ofReal_mul ..)), nonneg_of_mul_nonneg_right hh he'⟩
end YM.QCD.Rain
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
variable {c f C F L:Side} {J:Patch} {k₀ j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j k₀}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
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
lemma marchPQ (Z:Pixel f N)(T:Pixel c N)(w u:ℝ)(hK:S.patch.Branches K su)(hp:ProperF Z)(hx:Continuous Z)(hr:0<w)(ht:∀ U,advanceF S K h Z u U=gBody c w (T U)): ProperF T:=by
    let Y:= S.visit K h; let C:= canQ S h N Z; have hg:= (Rain.tenderLQ S h Z hx).integrable_of_hasCompactSupport (μ:=prior su f) (HasCompactSupport.of_compactSpace ..); have hX:= Y.isKernel hK u
    let X:= advanceF S K h Z u
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
      refine congr_arg Subtype.val (hm D V _ (hh V _ D (Lattice.gauge q) (prior_gauge _) (fun i=>by rw [← hq]; exact Y.covary hK ..) ?_)); intro i; unfold C canQ; rw [show ater S h (F:=N) (gauge q i)=(D*ater S h (F:=N) i:Matrix (Modes c N) (Modes f N) ℂ)*star W from ?_,compat (R:=W) (W:=D) (rotates_law ..) (rotates_law ..)]
      · exact congr_arg _ (hp.gauges ..)
      unfold D W ater; rw [gauges, show q ∘ (sliceL S h).embed=k from hq, choir_mul,choir_mul,Matrix.star_eq_conjTranspose,choir_star]; rfl -- star choir
    let M: Matrix (Modes c N) (Modes c N) ℂ:=Sway.flute (Lat.Row c) A; let D: Matrix (Modes f N) (Modes f N) ℂ:=Sway.flute (Lat.Row f) A; have hd:D∈unitary _:= Sway.unit_f H
    refine hm M i i (hh i i M id (MeasurePreserving.id _) (fun _=>rfl) ?_); intro V; let z:=ater S h (F:=N) V
    have hv : M*z*star D=z:=by rw [show M*z=z*D from (Sway.column _ _),Matrix.mul_assoc, (show _ from hd.2),Matrix.mul_one]
    have he:= Kit.compat (R:=D) (W:=M) hd (Sway.unit_f H) 1 z (Cove.light _ (Z V)); rw [hv] at he; exact he.trans (congr_arg (Kit.sheath _ z) (congr_arg Subtype.val (hp.fluteC V A H))) -- RHS eq
end Rails
end YM.QCD.Acre
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
variable {c f C F L:Side} {J:Patch} {k₀ j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j k₀}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
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
namespace IV
open MeasureTheory Push.BetaTransport
variable {t:ℝ}(hp: S.patch.Branches K su)(X:Pixel f N)(hx:Continuous X)(hR: Rain.realP X)
include hR hp hx
lemma voicingQ (p:ℝ)(V:Grid c): let Z:= S.visit K h; let f'(i:Grid f):= Z.density p i V * (cBer X i).re
    Integrable f' (prior su f) ∧ (ber _ (advanceF S K h X p V)).re= ∫ i:Grid f,f' i ∂ prior su f:=by -- f use rename
   intro Z f'; have hk:= Z.isKernel (show Z.patch.Branches Z.kernel su from hp) p; have hI: Integrable (fun i=> Z.density p i V • canQ S h N X i) (prior su f):= Z.push_slice hk V (canQ S h N X) ((tenderLQ S h X hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
   let G:= Complex.reCLM.comp ((LinearMap.toContinuousLinearMap (ber (Modes c N))).restrictScalars ℝ)
   let Y(i:Grid f):= Z.density p i V • canQ S h N X i
   have he:f'= fun i=> G (Y i):=by
        funext i; unfold Y; rw [map_smul]; let J:=ater S h i (F:=N); change Z.density p i _* (cBer X i).re= _* (ber _ (Kit.sheath 1 J _)).re; rw [Kit.insulate (by norm_num : (1:ℝ)≠ 0)]; rfl
   rw [he]; exact ⟨ContinuousLinearMap.integrable_comp _ hI,(G.integral_comp_comm hI).symm⟩ -- syntax
end IV
end Rails
end YM.QCD.Acre
