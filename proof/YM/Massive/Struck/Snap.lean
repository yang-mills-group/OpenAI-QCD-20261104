import YM.Massive.Struck.Salvo
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Struck
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
namespace Library
variable (b: Flavor N)(o:Site c)
open Lime High.PrismT Strut Brick
open Massive.Log
lemma leafM (h:(EvenA c N))(n:ℕ)(hx:mud h=0)(he:2≤n) : Stew.panel 2 (h^n).val=0:=by
    refine poster _ _ fun i=> ?_; rw [angel,map_zero]; split
    · have hz:= n; cases n; · omega
      next p=> rw [pow_succ]; exact lossM i (by omega) _ _ (held h p hx (by omega)) hx
    rfl
lemma octM {V:(EvenA c N)}(hx:mud V=0): octave V=V:=by unfold Reggae.octave; rw [show Reggae.river c N V=0 from ?_,map_zero,sub_zero]; change -(mud _).re=_; rw [hx,Complex.zero_re,neg_zero]
lemma fadeM {V Z:(EvenA c N)}(he:Stew.panel 2 V.val=Stew.panel 2 Z.val)(hp:Unfeatured o Z): Unfeatured o V:=by
    have hv : grasp V.val=grasp Z.val:=by rw [← breast,he, breast ..] -- occurrence both? edit
    exact ⟨he.trans (hp.1.trans (congr_arg Grass.form hv.symm)),hv.symm ▸ hp.2⟩
lemma fade0 : Unfeatured o (0:(EvenA c N)):=by
    unfold Unfeatured; have he: grasp (0:(EvenA c N)).val=0:=by ext i j; change bit i j*coef _ 0=0; rw [map_zero,mul_zero]
    rw [he, show Grass.form (0:Brick.FormN c N)=0 from (by simp [Grass.form])]; refine ⟨map_zero _,?_⟩
    intro p q; refine ⟨?_,fun h=>False.elim (Bool.noConfusion h) ⟩; simp only [Brick.flowN, Brick.signN, Matrix.zero_apply,mul_zero,sum_const_zero]
lemma mud_real_scale (z:(EvenA c N))(r:ℝ) : mud (r • z)=r • mud z:=map_smul ((clay c N).restrictScalars ℝ) r z
lemma light_scaling {x:(EvenA c N)} (hr:Unfeatured o x)(p:ℂ): Unfeatured o (p • x):=by
    let v:= x.val; have hp: grasp (p • x).val=p • grasp v:= regalia ..; unfold Unfeatured at *; rw [hp]; refine ⟨?_, ?_⟩
    · change panel 2 (p • x.val)=_; rw [map_smul,hr.1]; unfold Grass.form; simp only [Finset.smul_sum,Matrix.smul_apply,smul_smul,smul_eq_mul];rfl
    · intro a b; obtain ⟨hg,hα⟩:= hr.2 a b; have he:∀ M:FormN c N, flowN o (p • M) a b none= p* flowN o M a b none:=by intro M; unfold flowN signN; rw [Finset.mul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [Finset.mul_sum]; exact sum_congr rfl (fun i _=>by rw [Matrix.smul_apply, smul_eq_mul]; ring)
      constructor; · rw [he,hg,mul_zero]
      intro h; exact False.elim (Bool.noConfusion h)
-- carrier `Pulse3`: assign flag shape even for high. Need charge all zero scalar at id; unmarked keeps Φ.Guard. Use only where available.
variable {E V: Type}
def Mint (b:Bool)(F: Grid c→(EvenA c N))(o:Site c)(A:Support c): Prop:= mud (F 1)=0 ∧ (Nonwrapping A o → b → Unfeatured o (F 1))
variable {b':Bool}{U:Support c}{t:ℝ}
lemma puff (hp:Grit R)(hx:Woven o U P t R a)(he:Mint b' R o U)(hv:0<t)(hl:Nonwrapping U o)(hq:o∈U): Fleck P U o b' R t a :=by
   refine ⟨hx,hp.gauge,hp.real,fun ht=> octM he.1|>.symm ▸ (he.2 hl ht),(spores _ _ _ hx hp.gauge hv.le).1,hq,?_⟩
   change -(mud _).re=0; rw [he.1,Complex.zero_re,neg_zero]
lemma Bite.mint (Y:Gem c N I)(hp:Bite Y P t x v b')(i:I): Mint b' (Y.view i) (Y.addr i).site (Y.addr i).support:=by
   obtain ⟨f,hf,h⟩:=hp; exact ⟨(h i).2.1, fun hw hr=> octM (h i).2.1 ▸ ((h i).2.2 hw).rack hr⟩
section leaves
variable (F:Grid c→(EvenA c N)) (w:Tw)
lemma mud_seed (h:mud (F 1)=0) : mud (Lime.off F w 1)=0:=by
   induction w with|nil=> exact h|cons n l ih=>rw [Lime.off,Pi.smul_apply,Pi.pow_apply,mud_real_scale, High.PrismT.held _ _ ih (by omega),smul_zero]
lemma wishM (w:Tw)(he:Mint b' F o U): Mint b' (Lime.off F w) o U:=by
   refine ⟨mud_seed F w he.1, fun h hp=>?_⟩
   cases w with
   | nil=>exact he.2 h hp
   | cons n l => apply light_scaling o (x:=(Lime.off F l 1)^(n+2)) (p:=((-Massive.Log.c (n+2):ℝ):ℂ)) -- signature.R
                 exact fadeM o (leafM (Lime.off F l 1) (n+2) (mud_seed F l he.1) (by omega)|>.trans (map_zero _).symm) (fade0 o (N:=N))
lemma mud_log {V:(EvenA c N)}(h : ‖V‖<1)(hv:mud V=0) : mud (Massive.Log.log V)=0:=by
   unfold Reggae.mud; -- inspect. use clay.hasSum
   have hf (k:ℕ): Massive.Log.c k • mud (V^k)=0:=by cases k; exact (by rw [show Massive.Log.c 0=0 from (by simp [Massive.Log.c]),zero_smul]); next k=>rw [High.PrismT.held V _ hv (by omega),smul_zero]
   let M:= (clay c N).restrictScalars ℝ; have hp := M.hasSum (Massive.Log.afford h).of_norm.hasSum; have he: ∀ k, M (Massive.Log.c k • V^k)=0:=fun k=> (map_smul M _ _).trans (hf k)
   change M (Massive.Log.log V)=_; rw [Massive.Log.log_eq,← hp.tsum_eq,show (fun k=> M (Massive.Log.c k • _))=fun k:ℕ=>(0:ℂ) from (funext he)]; exact tsum_zero
lemma log_mint (he:Mint b' F o U)(h: ‖F 1‖<1): Mint b' (Massive.Log.log ∘ F) o U:=by
    refine ⟨mud_log h he.1, fun hw hp=>fadeM o (Finch.visibleLog N (F 1) he.1 h) (he.2 hw hp)⟩ -- Args!
lemma mudloan_pipe (z:ℝ)(hV:Mint b' F o U): Mint b' (z • F) o U:=by
    refine ⟨(mud_real_scale (F 1) z).trans (by rw [hV.1,smul_zero]),fun hq ht=> light_scaling o (hV.2 hq ht) (z:ℂ)⟩
variable (K: (EvenA c N)→+*(EvenA c N)) (u v:Grid c)(G:Grid c→(EvenA c N))(hKV:K (F u)=G v)
include hKV
lemma offK (he:Continuous K): K (Lime.off F w u)=Lime.off G w v:=by
   induction w with|nil=>exact hKV|cons i w ih=> rw [Lime.off,Lime.off,Pi.smul_apply,Pi.smul_apply,Pi.pow_apply,Pi.pow_apply,eSM K he,map_pow,ih]
lemma walk_log (he:Continuous K)(hh:Bijective K): K (Massive.Log.log (F u))=Massive.Log.log (G v):=by
   let X:= K.toAddMonoidHom.toRealLinearMap he; let T: (EvenA c N) ≃L[ℝ] (EvenA c N):= (LinearEquiv.ofBijective X.toLinearMap hh).toContinuousLinearEquiv; rw [Massive.Log.log_eq, Massive.Log.log_eq];
   change T _ = _; rw [T.map_tsum]; apply tsum_congr; intro i; rw [map_smul]; exact congr_arg (Massive.Log.c i • ·) ((map_pow K ..).trans (congr_arg (·^i) hKV))
-- crossing.Grit extension for all leaves and parameters, even unmasked
omit hKV
lemma sepC (hp:shadeG F)(w:Tw): shadeG (Massive.Log.log ∘ Lime.off F w):=by
    intro U p; exact congr_arg Subtype.val (walk_log (Lime.off F w) (sways (Lat.rotates N p)) _ _ _ (offK F w _ (gauge p U) U F (Subtype.ext (hp ..)) (Sway.OrbitG.phare _)) (Sway.OrbitG.phare _) (surfeit (Lat.rotates_law ..)))
lemma gritE (hp:Grit F)(w:Tw): Grit (Massive.Log.log ∘ Lime.off F w):=by
    refine ⟨sepC F hp.gauge w,fun U i h=> ?_,fun U=>?_⟩
    · let k:=sways (Sway.flute (Lat.Row c) (Matrix.diagonal i)); exact walk_log (Lime.off F w) k U U (Lime.off F w) (offK F w _ _ _ F (hp.flex U i h) (Sway.OrbitG.phare _)) (Sway.OrbitG.phare _) (surfeit (Sway.unit_f h))
    exact walk_log (Lime.off F w) (Regal c N) U U (Lime.off F w) (offK F w _ _ _ F (hp.real U) (Sway.OrbitG.phare _)) (Sway.OrbitG.phare _) (imp _ (gammaL ..))
end leaves
end Library
end YM.QCD.Struck
#print axioms YM.QCD.Struck.Library.log_mint
#print axioms YM.QCD.Struck.Library.wishM
