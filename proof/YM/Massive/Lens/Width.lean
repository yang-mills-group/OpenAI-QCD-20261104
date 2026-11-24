import YM.Massive.Horizon.Castle
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
variable {β':ℝ}{t₅ p':ℝ}{θ σ:ℝ}
open Finch Stem Grove Moss Calm
variable {I0 J0:Type}
lemma valued_transport (G D:Gem c N I0)(f:I0→ℝ)(hp:Valued G.addr u f O.B v)(he:∀ i,f i ≠0 → D.addr i= G.addr i): Valued D.addr u f O.B v:=by
    intro y; let P (X:Gem c N I0)(i:I0):= if (X.addr i).site=y then f i*Real.exp (u*coverNumber O.B (X.addr i).support) else 0; change SumBudget (P D) v; rw [show P D=P G from funext fun i=>?_]; exact hp y
    by_cases hx:f i=0; · simp [P,hx]
    unfold P; rw [he _ hx]
lemma loanCost (G:Gem c N I0)(F:Gem c N J0)(g:I0→Prop)(w:{i:I0//g i}→J0)(hw:Injective w)(ht:∀ i:{i:I0//g i},F.addr (w i)=G.addr i.val)(q:J0→ℝ)(hp:Valued F.addr v q O.B u)(hh:∀ i:{i:I0//g i}, Woven (F.addr (w i)).site (F.addr (w i)).support O t (G.view i.val) (q (w i))): Licence O v u t (muteK G g):=by
    let f i:= if h:g i then q (w ⟨i,h⟩) else 0; refine ⟨f,wire _ g _ w hw _ (fun i=>(ht i).symm) q hp (fun i=>rfl),?_⟩
    intro i; rw [eitherX]; change Woven (G.addr i).site (G.addr i).support _ _ _ _; split
    next he=> let i':{i//g i}:=⟨i,he⟩; rw [show f i=q (w i') from dif_pos he]; exact (show Woven (G.addr i).site _ _ _ _ (q (w i')) from ht i' ▸ hh i')
    next he=> rw [show f i=0 from dif_neg he]; exact freeK ..
lemma valued_limit (A:I0 → RegularAddress c)(f:I0→ℝ)(h:Valued A t f n s)(p:I0→Prop):Valued A t (fun i=>if p i then f i else 0) n s:=valued_trim A f _ (fun i=>ite_nonneg (vex _ _ h _) le_rfl) (fun i=> by split; rfl; exact vex _ _ h _) h
lemma costUnion (G:Gem c N I0)(X Y Z: I0→Prop)(hX:Licence O v t w (muteK G X))(hY:Licence O v u w (muteK G Y))(hp:∀ i,Z i→ X i∨ Y i):Licence O v (t+u) w (muteK G Z):=by
    obtain ⟨g,hg,h⟩:= hX.zone; obtain ⟨f,hf,hY⟩:=hY.zone; refine ⟨g+f, valued_sum G.addr g f hg hf,?_⟩; intro i; change Woven (G.addr i).site (G.addr i).support _ _ _ (g i+f i); rw [eitherX]; split
    next hh=> obtain hh|hh:= hp i hh
              · apply Woven.stretches (show Woven (G.addr i).site (G.addr i).support _ _ _ _ from ?_) (Subset.refl _) (le_add_of_nonneg_right (hY i).travel); rw [← show (muteK G X).view i=G.view i from (eitherX ..).trans (if_pos hh)]; exact h i
              apply Woven.stretches (show Woven (G.addr i).site (G.addr i).support _ _ _ _ from ?_) (Subset.refl _) (le_add_of_nonneg_left (h i).travel); rw [← show (muteK G Y).view i=G.view i from (eitherX ..).trans (if_pos hh)]; exact hY i
    next hh=> exact (freeK ..).stretches (Subset.refl _) (add_nonneg (h i).travel (hY i).travel)
lemma chargedWidth (G D: Gem c N I0)(X P:I0→Prop)(hp:∀ i,¬X i→ D.addr i=G.addr i)(he:D.view=G.view)(f:I0→ℝ)(hc:∀ i,P i→¬ X i→Woven (G.addr i).site (G.addr i).support O t (G.view i) (f i)) (hf:Valued G.addr t' f O.B A): Licence O t' A t (muteK D fun i=>P i∧¬X i):=by
    let Y i:=P i∧¬ X i; let g i:= if Y i then f i else 0; refine ⟨g,valued_transport G D g (valued_trim G.addr f (fun i=>g i) (fun i=>ite_nonneg (vex _ _ hf i) le_rfl) (fun i=>by dsimp only [g]; split; rfl; exact vex _ _ hf i) hf) (fun i hi=> hp i ((by by_contra! ht; exact hi (if_neg (mt And.right (by simpa using ht)))))),?_⟩; intro i; change Woven (D.addr i).site (D.addr i).support _ _ ((muteK D Y).view i) _; rw [eitherX]; split
    next hh=> rw [he,hp i hh.2,show g i=_ from if_pos hh]; exact hc i hh.1 hh.2
    next hh=> rw [show g i=_ from if_neg hh]; exact freeK ..
lemma lendWidth (G D: Gem c N I0) (g:I0→Prop)(u:I0→Prop) (X:J0→RegularAddress c)(W:{i//g i}→J0)(h:Injective W)(he:∀ i:{i//g i}, D.addr i.val=X (W i))(hc:D.view=G.view)(p:J0→ℝ)(hp:Valued X t p O.B t')(hy:∀ i:{i//g i}, u i.val → Woven (X (W i)).site (X (W i)).support O w (G.view i.val) (p (W i))): Licence O t t' w (muteK D (fun i=>u i∧g i)):=by
    let H(i:{i//u i∧g i}):{i//g i}:=⟨i.val,i.property.2⟩; let Q:Gem c N J0:= ⟨X,fun _ _=>0⟩
    refine loanCost D Q _ (W∘H) (h.comp (fun i j hij=> Subtype.ext (congr_arg (fun x:{i//g i}=> x.val) hij))) (fun i=>(he (H i)).symm) p hp (fun i=> ?_)
    rw [hc]; exact hy _ i.property.1
end Warmlet
end YM.QCD.Shells
