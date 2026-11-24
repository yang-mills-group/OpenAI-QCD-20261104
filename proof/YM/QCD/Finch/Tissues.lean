import YM.QCD.Finch.Trust
/-! # Real layer. hue dictionaries on arbitrary virtual-τ labels; convert only via corresponding j Tape. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Shells
open ConnectedActivityE6 ConnectedActivityE6.Blaze Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side}{j n l k : ℕ} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {O R : BudgetPoint} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B t t' w y u: ℝ}
variable {δ β B₀:ℝ}{Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T (trimP T R δ β B₀)}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
open Ursell QCD.GasP Stained March Graph AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Spice Lat Multi Multi.Puff Kit Jets Port Fork Sands Fj
variable {N':Libretto su j}
open Garden Stew Dust Brick YM.Next.Free Jets.Touch Orbit Further Leaf Tee Flume Quarry Pine
open Planned.AtomRegular
open Run Jets Jets.Sun
open Ac Trees Labels Animals Further.ShellBirth49.Fusing Collide
open Trees Ac Further.ShellBirth49.Fusing Collide
open Labels
variable {p i j' m m':ℕ}
namespace Warmlet
variable {β':ℝ}{t₅ p':ℝ}{θ σ:ℝ}
open Finch Stem Grove Moss Calm
lemma fresh (f:ι→ℝ)(v:ι→Support c)(hp:Hit v n f A b)(hz:B≤ A)(he:∀ i,0 ≤ f i):Hit v n f B b:=by
     intro x; refine budget_mono (hp x) (fun i=>?_) (fun i=> ?_)
     · split; exact mul_nonneg (he _) (Real.exp_pos _).le; exact le_rfl
     split
     exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hz (by positivity))) (he _)
     exact le_rfl
lemma waives {c f:Side}{S:StepData c f}{T:Tube su S}{H:Cash W s μ L Q o C T (trimP T R δ β B₀)} (Y: Fleet H (ι⊕ Varn f c ⊕ Gaze c) N) (hc:Gosh Y χ B b j k)(hz:A≤B) (hp:BudgetPoint)(hO:hp.order=j)(hv: hp.power=k)(hr:hp.threshold=Pressure.temp s)(hk:hp.B=radiusB s):Gosh Y χ A b j k:=by
      obtain ⟨g,hg,hT,hH⟩:=hc.bills; choose x hx using naming Y; have he i : 0 ≤ g i:=(hg hp x hx hO hv hk hr i).travel; exact ⟨_,hg,fresh g _ hT hz he,fresh _ _ hH hz (fun i=>ite_nonneg (he _) le_rfl)⟩
-- remask.Exact any θ. Debit by α' B bootstrap.
variable (E G:Gem c N ι)
noncomputable def lira (t:ℝ): Ruby.Hue c N ι:=⟨fun i=>(G.addr i).support, fun i V=> letters E t V i- letters G t V i⟩
local notation "φ"=>lira E G O.threshold
variable {η':ℝ}
lemma quills (hp:Licence O B v t E)(he:Dyed E)(hc:E.view=G.view)(hx:G.Gather)(hq:0<t)(hm:∀ i,(G.addr i).site∈(E.addr i).support)(hψ:∀ i,(E.addr i).support ⊆(G.addr i).support)(f:ι→ℝ)(hv:Valued G.addr (A+1+1) f O.B u)(h:∀ i U, ‖Loom.token c N t (letters E O.threshold U i)‖≤f i)(hA:0 ≤A): TokenB (φ) O.threshold O.B A (payment 1 (4*O.B+2) 0 1 1 u A 0) t :=by
    have hp : E.Gather:= Entr.Licence_g hp; have he' i:= wonders _ _ O.threshold (he.gauge i) (he.num i) (he.real i) (hp.role i); have hh i:= wonders (G.view i) _ O.threshold (congr_fun hc i ▸ he.gauge i) (congr_fun hc i ▸ he.num i) (congr_fun hc i ▸ he.real i) (hx.role i)
    have hvG i U (h:Healthy O.threshold (G.addr i).support U) : (φ).mean i U=0:= sub_eq_zero.mpr ((masked_eq _ _ _ _ (h.mono_left (hψ i))).trans ((congr_fun (congr_fun hc i) U).trans (masked_eq _ _ _ _ h).symm))
    refine ⟨⟨fun i U V w z=> congr_arg₂ (·-·) (Work.H03.reads_larger (hψ i) (clearUse E _ (hp.sees i) O.threshold) U V w z) (clearUse G _ (hx.sees _) O.threshold U V w z),fun i=> (RG.masked_measurable _ _ _ (hp.reads i)).sub (RG.masked_measurable _ _ _ (hx.reads i)),fun i U hn hp=> hn (hvG i U hp),fun i U=> wingsZ _ _ _ (gateMon _ _ (hψ i) _ (licit _ hp i U)) (licit _ hx i U)⟩,fun i U k => ?_,fun i U W hz=>?_,fun i U=>?_,f,tipped G f hv (vex G.addr f hv) le_rfl hA,fun i U=>?_⟩
    · refine congr_arg Subtype.val (show Patron.sways (Lat.rotates N k) ((φ).mean i (Lattice.gauge k U))=(φ).mean i U from Eq.trans (map_sub ..) (congr_arg₂ (·-·) (Subtype.ext ((he' i).1 U k)) (Subtype.ext ((hh i).1 U k)))) -- not correct Prop
    · exact Eq.trans (map_sub ..) (congr_arg₂ _ (((he' i).2 U).1 W hz) (((hh i).2 U).1 W hz))
    · exact Eq.trans (map_sub ..) (congr_arg₂ _ (((he' i).2 U).2.1) (((hh i).2 U).2.1))
    by_cases hU:Healthy O.threshold (G.addr i).support U; · rw [hvG _ _ hU,map_zero,norm_zero]; exact vex G.addr f hv _
    change ‖Loom.token _ _ _ (_-letters _ _ _ _)‖≤_; rw [show letters G _ _ _=0 from masked_ne _ _ _ _ hU,sub_zero]; exact h i U
lemma coinQ (hp:Licence O B v t E)(he: Dyed E)(ht: Licence O σ μ t G)(hc:E.view=G.view)(hQ:TokenB (φ) O.threshold O.B A η' t)(hz:1 ≤ t)(ha:0 ≤B)(hσ:0 ≤ σ)(hr:0 ≤A): PayC G (φ) O t σ A μ η' 0 (Stem.income E O.threshold):=by
    have h : Dyed G :=⟨fun i=> congr_fun hc i ▸ he.gauge i,fun i=> congr_fun hc i ▸ he.num i,fun i=> congr_fun hc i ▸ he.real i⟩
    have hp':0<t:=zero_lt_one.trans_le hz
    have hV :Stem.income E O.threshold=Stem.income G O.threshold+Calm.netT (φ):=by
         funext U; let P i:= letters E O.threshold U i; have hx:P=fun i=>letters G O.threshold U i+(φ).mean i U:=funext fun i=>(add_sub_cancel ..).symm; -- lemma sign
         change (∑' i, P i)=_; rw [hx]; exact ((permits G ht hp' hσ U).hasSum.add (scaledLift _ hQ U hr hz).hasSum).tsum_eq
    rw [hV]; exact penny G _ ht h hQ
end Warmlet
end YM.QCD.Shells
