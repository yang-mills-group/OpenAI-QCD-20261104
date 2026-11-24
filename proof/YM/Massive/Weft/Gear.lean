import YM.Massive.Weft.Mode
import YM.Massive.Weft.Shine
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.QCD.Weft
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
open Struck Struck.Library
open Finch Carrier

variable {t p:ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (Y0: Code c N) -- independent shape
set_option quotPrecheck false
variable (Y:Ruby.Hue c N Ω)(X:Gem c N I)(Q:Ruby.Hue c N I)(K: ℝ)
variable {g:Site c→ℂ}(L':I→Dye)(L0:Ω→ Dye)
open Ruby
open Warmlet
variable (E G :Gem c N I)(U:Grid c)(i:I)(w u:ℝ)
variable {E₀:Ruby.Hue c N I}(X:Gem c N Ω)
-- low orientation all at peg.Fees.Account.Field. 
local notation "ω"=> E
lemma nesting (F:Gem c N I):Library.wind F (fun _=>1)=F:= by unfold Library.wind; simp
lemma cooling (h:E.view=G.view):Patron.total E P.threshold 1=Patron.total G P.threshold 1:=tsum_congr fun i=> (masked_eq P.threshold _ _ (1:Grid c) (flat_ok ..)).trans ((congr_fun (congr_fun h i) (1:Grid c)).trans (masked_eq P.threshold _ _ _ (flat_ok ..)).symm) -- inference

noncomputable abbrev serving (D:I→Dye)(z s:ℂ) (i:I):ℂ := pigment (D i) z s
abbrev myLow (ι:Type):ι→ Dye:=fun _=> pegE
abbrev qFirst (x:Dye):Prop:=x.1=1
abbrev qHigh (x:Dye):Prop:= 2≤x.1
def qset (x:Dye): Dye:= if qHigh x then x else (2,3)
def qualified (x:Dye):Prop:= Ash x ∧2≤x.1
lemma qualYes (x:Dye)(h:Ash x):qualified (qset x):=by
    unfold qset; split
    next he=> exact ⟨h,he⟩
    next _=> exact ⟨Or.inr (Or.inr ⟨le_rfl,le_rfl⟩), le_rfl⟩ -- format
lemma winter (hp:Bigger E G n)(X:I→ Prop): Bigger (muteK E X) (muteK G X) n:=⟨by funext i; rw [eitherX, eitherX,hp.view],hp.bump⟩
noncomputable abbrev myH (X:I→ Dye): I→ Dye:= qset∘ X

lemma holdS (z s :ℂ)(hp:∀ i, Ash (L' i))
  (hs0:Summable (letters E P.threshold U)) (hz:‖z‖≤1)(hg:‖s‖≤1): Patron.total (Library.wind E (fun i=> pigment (L' i) z s)) P.threshold U - Patron.total (Library.wind E (fun i=> pigment (L' i) 0 0)) P.threshold U
      = Patron.total (Library.wind (LowSection E L') (fun _=> pigment pegE z s)) P.threshold U + Patron.total (Library.wind (MoreSection E L') (serving (qset∘ L') z s)) P.threshold U:=by
     let Z p q := letters (Library.wind E (serving L' p q)) P.threshold U; let A:=∑' i,Z z s i; let K:=∑' i,Z 0 0 i; let Dp:= P.threshold
     have hE(z s:ℂ)(ht:‖z‖≤1)(he:‖s‖≤1) : HasSum (Z z s) (∑' i,Z z s i):=(weighL U E (serving L' z s) hs0 (fun i=>upperPaint (L' i) z s ht he)).hasSum
     let L:=LowSection E L'; let H:=MoreSection E L'; let P(i:I):= if (L' i).1=1 then pigment pegE z s else if 2 ≤ (L' i).1 then pigment (qset (L' i)) z s else 0
     have hc(X:I→Prop): Summable (letters (muteK E X) Dp U) := by
          apply Summable.of_norm_bounded hs0.norm; intro i; rw [masking]; split; exact le_rfl; rw [norm_zero]; exact norm_nonneg _
     let S:=Library.wind L (fun _=> pigment pegE z s); let B:= Library.wind H (serving (qset∘ L') z s); have hA:= weighL U L (fun _=> pigment pegE z s) (hc _) (fun i=> upperPaint pegE z s hz hg); have hB:=weighL U H (serving (qset∘ L') z s) (hc (fun i=>_)) (fun i=> upperPaint _ z s hz hg)
     have he:HasSum (fun i=>Z z s i-Z 0 0 i) (A-K):=(hE z s hz hg).sub (hE _ _ (by simp) (by simp))
     refine he.unique ( (hA.hasSum.add hB.hasSum).congr_fun (fun i=>?_)); unfold Z; rw [wireL,wireL,wireL,wireL]; unfold L H LowSection MoreSection; rw [masking,masking]; unfold serving
     dsimp only [Function.comp_apply]; obtain h|h|⟨h,hr⟩:=hp i
     · simp [h,Dp,Struck.pigment]
     · change L' i=(1,2) at h; simp [h,Dp,Struck.pigment,qset,pegE]
     have hx:¬ (L' i).1=1:=by omega
     simp [hx, h,qset,qHigh,Dp,Struck.pigment,zero_pow (Nat.ne_of_gt ((by norm_num:0 < 2).trans_le h))]
end YM.QCD.Weft
