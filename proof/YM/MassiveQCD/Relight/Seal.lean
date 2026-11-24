import YM.MassiveQCD.Relight.Wing
import YM.QCD.Grove.Mike
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
open Relight
variable {β':ℝ}{t₅ p':ℝ}{θ σ:ℝ}
open Finch Stem Grove Moss Calm
-- remask.Exact any θ. Debit by α' B bootstrap.
lemma dayEffect (f:Grid c→ EvenA c N)(W:Support c)(δ:ℝ)(ht:shadeG f)(hp:∀ x,AccentFit (f x))(hq:∀ x,Regal c N (f x)=f x)(hv:∀ U,Gated W (f U)):
   let f':=masked δ W f; shadeG f'∧∀ i, AccentFit (f' i)∧ Regal c N (f' i)=f' i∧ Gated W (f' i) :=by
    intro f'; refine ⟨fun i k=>?_,fun i=> ?_⟩
    · have h : Healthy δ W (Lattice.gauge k i) ↔ Healthy δ W i:=by unfold Healthy; rw [gauge_flags]
      by_cases he:Healthy δ W i
      · unfold f'; rw [masked_eq _ _ _ _ (h.2 he),masked_eq _ _ _ _ he]; exact ht i k
      unfold f'; rw [masked_ne _ _ _ _ (mt h.1 he),masked_ne _ _ _ _ he]; exact congr_arg Subtype.val (map_zero (sways (Lat.rotates N k)))
    by_cases he:Healthy δ W i
    · unfold f'; rw [masked_eq _ _ _ _ he]; exact ⟨hp _,hq _,hv _⟩
    unfold f'; rw [masked_ne _ _ _ _ he]; exact ⟨fun _ _=> map_zero _,map_zero _, Loom.Fleet.spruce W⟩
variable (E G:Gem c N ι)

local notation "φ"=>lira E G O.threshold
variable {η':ℝ}
lemma burnY (hp:Licence O B v t E)(he:Noted E)(hc:E.view=G.view)(hx:G.Gather)(_hq:0<t)(_hm:∀ i,(G.addr i).site∈(E.addr i).support)(hψ:∀ i,(E.addr i).support ⊆(G.addr i).support)(f:ι→ℝ)(hv:Valued G.addr (A+1+1) f O.B u)(h:∀ i U, ‖Loom.token c N t (letters E O.threshold U i)‖≤f i)(hA:0 ≤A): LampInk (φ) ∧ Wax (φ) O.threshold O.B A (payment 1 (4*O.B+2) 0 1 1 u A 0) t :=by
    have hp : E.Gather:= Entr.Licence_g hp; have he' i:= dayEffect _ _ O.threshold (he.gauge i) (he.num i) (he.real i) (hp.role i); have hh i:= dayEffect (G.view i) _ O.threshold (congr_fun hc i ▸ he.gauge i) (congr_fun hc i ▸ he.num i) (congr_fun hc i ▸ he.real i) (hx.role i)
    have hvG i U (h:Healthy O.threshold (G.addr i).support U) : (φ).mean i U=0:= sub_eq_zero.mpr ((masked_eq _ _ _ _ (h.mono_left (hψ i))).trans ((congr_fun (congr_fun hc i) U).trans (masked_eq _ _ _ _ h).symm))
    refine ⟨⟨fun i U k=> ?_,fun i U=> ?real,fun i U W hz=>?fit⟩,⟨⟨fun i U V w z=> congr_arg₂ (·-·) (Work.H03.reads_larger (hψ i) (clearUse E _ (hp.sees i) O.threshold) U V w z) (clearUse G _ (hx.sees _) O.threshold U V w z),fun i=> (RG.masked_measurable _ _ _ (hp.reads i)).sub (RG.masked_measurable _ _ _ (hx.reads i)),fun i U hn hp=> hn (hvG i U hp),fun i U=> wingsZ _ _ _ (gateMon _ _ (hψ i) _ (licit _ hp i U)) (licit _ hx i U)⟩, f,tipped G f hv (vex G.addr f hv) le_rfl hA,fun i U=>?_⟩⟩
    · refine congr_arg Subtype.val (show Patron.sways (Lat.rotates N k) ((φ).mean i (Lattice.gauge k U))=(φ).mean i U from Eq.trans (map_sub ..) (congr_arg₂ (·-·) (Subtype.ext ((he' i).1 U k)) (Subtype.ext ((hh i).1 U k)))) -- not correct Prop
    case fit=> exact Eq.trans (map_sub ..) (congr_arg₂ _ (((he' i).2 U).1 W hz) (((hh i).2 U).1 W hz))
    case real=> exact Eq.trans (map_sub ..) (congr_arg₂ _ (((he' i).2 U).2.1) (((hh i).2 U).2.1))
    by_cases hU:Healthy O.threshold (G.addr i).support U; · rw [hvG _ _ hU,map_zero,norm_zero]; exact vex G.addr f hv _
    change ‖Loom.token _ _ _ (_-letters _ _ _ _)‖≤_; rw [show letters G _ _ _=0 from masked_ne _ _ _ _ hU,sub_zero]; exact h i U


end Warmlet
end YM.QCD.Shells
