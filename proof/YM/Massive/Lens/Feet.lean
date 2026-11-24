import YM.Massive.Horizon.Castle
import YM.Massive.Pith.Bill
import YM.QCD.Finch.Dad
import YM.QCD.Finch.Tissues
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
open Finch Stem Grove Moss Calm Garden
variable {I0 J0:Type}
lemma limited_view (G:Gem c N I0)(X:I0→Prop) (x:I0): letters (muteK G X) O.threshold 1 x= if X x then G.view x 1 else 0:=by
    rw [masking, show letters G O.threshold 1 x=G.view x 1 from masked_eq _ _ _ _ (AnalyticBridge.VerifiedReset.flat_ok ..)] -- name ambiguous
lemma cutoff_lead (G:Gem c N I0) [Fintype J0] (Y:J0→I0) (P:I0→Prop)(he:Injective Y)(hp:∀ i,P i ↔ i∈Set.range Y) : Patron.total (muteK G P) O.threshold 1 = ∑ i,G.view (Y i) 1:=by
     unfold Patron.total; let R i:= if P i then G.view i (1:Grid c) else 0; simp_rw [limited_view G]; change (∑' i,R i)=_
     apply HasSum.tsum_eq; apply (he.hasSum_iff ?_).mp; · exact (hasSum_fintype (fun i:J0=>G.view (Y i) (1:Grid c))).congr_fun fun i=> if_pos ((hp _).2 ⟨_,rfl⟩)
     exact fun i h=> if_neg (mt (hp i).1 h)
lemma total_lead (G:Gem c N I0) (X Y:I0→Prop)(hA:Licence O u s t (muteK G X))(hB:Licence O u r t (muteK G (fun i=>Y i∧¬ X i)))(hC:∀ i, X i→ Y i)(ht:0 < t)(hq:0≤ u) : Patron.total (muteK G Y) O.threshold 1= Patron.total (muteK G X) O.threshold 1 + Patron.total (muteK G (fun i=>Y i∧¬ X i)) O.threshold 1:=by
   let S i:=Y i∧¬ X i; have hm:= ((Stew.permits _ hA ht hq (1:Grid c)).hasSum.add (Stew.permits _ hB ht hq (1:Grid c)).hasSum); refine (hm.congr_fun (g:=letters (muteK G Y) O.threshold (1:Grid c)) ?_).tsum_eq; intro i; rw [limited_view,limited_view,limited_view]; by_cases hx:X i <;> by_cases he:Y i <;> simp [hx,he]; exact False.elim (he (hC _ hx))
lemma totBound (G:Gem c N I0)(hp: Licence O u r t G)(ht:0<t)(hu:0≤u)(x:Flavor N): ‖flagRead x t (Patron.total G O.threshold 1)‖ ≤ r:=by obtain ⟨f,hf,h⟩:=hp.zone; exact sector_pay x G hf hu h ht -- banker
lemma budget_bridge (Y:I0→ℝ) [Fintype I0] (X:I0→ℝ)(h:∀ i,‖Y i-X i‖ ≤u) (he:(∑ i,X i)=a*b)(hp:y=(∑ i,Y i)/b+r)(hb:0<b): ‖y-a‖ ≤ Fintype.card I0*u/b+‖r‖:=by
    rw [hp,show _/b+r-a=((∑ i,Y i)-a*b)/b+r from (by field_simp; ring : (∑ i,Y i)/b+r-a=_),← he]; refine le_trans (norm_add_le ..) (add_le_add ?_ (le_refl _)); rw [norm_div,Real.norm_of_nonneg hb.le,←sum_sub_distrib]; exact div_le_div_of_nonneg_right ((norm_sum_le ..).trans ((sum_le_sum (fun i _=> h i)).trans_eq (by rw [sum_const,nsmul_eq_mul,card_univ]))) hb.le
lemma rate_earned (G:Gem c N I0) (F: Kit.Rail f c) (H:Site f × Flavor N→ I0) (he:Injective H)(P:I0→Prop) (hp:∀ i,P i ↔ i∈ Set.range H)(Y:I0→Prop)(hA:Licence O u s t (muteK G P))(hB:Licence O u r t (muteK G (fun i=>Y i∧¬ P i)))(hC:∀ i,P i→Y i)(m:Flavor N→ℝ) (T:Site f×Flavor N→ EvenA f N) (hf:∀ i,Stew.panel 2 (T i).val=Grass.form (Finch.stripe N i.2 (localX i.1 ((m i.2:ℂ) • 1)))) (x:Flavor N) (hw:∀ i, ‖watchW c t x (G.view (H i) 1) - planeW c t x (Dust.bill F N (T i))‖≤w) (ht:0<t)(hQ:0 ≤u):
       ‖flagRead x t (Patron.total (muteK G Y) O.threshold 1)- t^2*(m x*flagW (railDay F*F))‖ ≤ Fintype.card (Site f×Flavor N)*w/(Fintype.card (Site c) :ℝ)+r :=by
     let Z:= muteK G fun i=>Y i∧¬P i; refine (budget_bridge (fun i=>watchW c t x (G.view (H i) 1)) _ hw ?_ ?_ (r:=flagRead x t (Patron.total Z O.threshold 1)) (b:=((Fintype.card (Site c)):ℝ)) (a:= t^2*(m x*flagW (railDay F*F))) (by positivity)).trans ?_ -- hp y y not refl. edit
     · rw [onShelf N F m _ x hf]; ring
     · unfold flagRead; rw [total_lead G P Y hA hB hC ht hQ,map_add,add_div,cutoff_lead G H P he hp,map_sum]
     exact add_le_add_right (totBound Z hB ht hQ x) _
end Warmlet
end YM.QCD.Shells
