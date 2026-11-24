import YM.TIPS.Tap
import YM.TIPS.Tight
import YM.TIPS.Units
import YM.Differ.Treasures
import YM.TIPS.Tip
import YM.Oars.PursePages
import YM.Cape.Fuel
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {I J E D U :Type}[Fintype I]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
namespace Taxing
open QCD.Ruby Cove Cape SC
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j N:ℕ}
-- general active injection from raw Reel.C
variable (p:I→Site c)(q:I→Bool) (E₀: Reel c N I E)
noncomputable def birthV (t:ℝ): Lure c N I E:=⟨fun i=> (E₀.addr i).support,fun i V=> E₀.mark i V- Reel.mist E₀ t i V,E₀.z⟩
open Stitch
lemma onBirth (hz:Reel.Book p q E₀): Lure.On p q (birthV E₀ t) t:=by
    let f(i:E):=(E₀.addr i).support; let T:= birthV E₀ t; refine ⟨fun i U V hu hx=> congr_arg₂ (·-·) (hz.room i U V hu) (MaskR _ _ (hz.room i) U V hu hx), fun i=> (hz.permit i).sub (masked_measurable _ _ _ (hz.permit i)),fun i V h hV=> h (?_:T.wick i V=0),?_,?_,hz.stamp,hz.stays⟩
    · change Healthy t (f i) V at hV; change E₀.mark i V- masked t (f i) _ V=0; rw [masked_eq _ _ _ _ hV]; exact sub_self _
    · intro i V; change lights _ _ _ _ (_-_); rw [sub_eq_add_neg]; obtain ⟨hx,hQ⟩:= hz.stage i V; obtain ⟨hv,hS⟩:=Cape.upM p q E₀ hz (t:=t) i V; exact ⟨hx.lays hv.minus,hQ.plus hS.neg⟩
    · intro i V g; have hk: Healthy t (f i) (Lattice.gauge g V) ↔ Healthy t (f i) V:=by simp [Healthy]
      change parcelColor _ _ _ (E₀.mark i (Lattice.gauge g V) - masked t (f i) (E₀.mark i) (Lattice.gauge g V)) = E₀.mark i V - masked t (f i) (E₀.mark i) V; rw [map_sub,hz.tint]; apply congr_arg; by_cases hv:Healthy t (f i) V; rw [masked_eq _ _ _ _ (hk.mpr hv),masked_eq _ _ _ _ hv]; exact hz.tint i V g
      rw [masked_ne _ _ _ _ (mt hk.mp hv),masked_ne _ _ _ _ hv,map_zero]
lemma unmaskV (i:E)(V:Grid c)(h:Tablet.credits v (E₀.mark i V)≤ Γ) (he:0≤ Γ): Tablet.credits v ((birthV E₀ t).wick i V) ≤ wig (fun _=> Real.log (1+Γ)) i:=by
   rw [show wig (fun _=>Real.log (1+Γ)) i=Γ by unfold wig; rw [Real.exp_log (by linarith : 0<1+Γ)]; ring]; change Tablet.credits v (_-masked t _ _ V) ≤ _; by_cases hv:Healthy t (E₀.addr i).support V; swap; · rw [masked_ne _ _ _ _ hv,sub_zero]; exact h
   rw [masked_eq _ _ _ _ hv]; unfold Tablet.credits; rw[sub_self,map_zero,Cove.load_zero]; exact he
-- charter activation Fame.New
variable (H: Massive.SourceRead.TaperHol){S:YM.Source.Hol su}(B:Massive.Lining.Temper.Collage.Exhibit S)(o:I → Cover)(r:I→ Label d)(F:∀ i:I,CentreFrame (c:=c) P v (r i) (q i) B (o i) (l+1) Unit Empty)(W:I→ℝ)
open Stags
variable {θ z:ℝ}
variable (hk:Pilot H B d P.order P.power k n l z θ)(hX:∀ i,Published (F i) H k n α t (W i) 0)(ht:1≤v)(ha:0 ≤ Γ)(hH:30*(l+1)≤ c.val)(hC:∀ i:I,Courtesy B (o i) (r i) (q i) P (F i) 4 Γ)(hG:∀ i j, ((ritual (F i)).addr j).support⊆Massive.Poised.Carte.Hem.pot P.B c (o i)) -- cost viewport
set_option quotPrecheck false
local notation "O"=> wrap c ∘ o
local notation "I₁"=>Jars d ⊕ Unit
local notation "J'"=> Σ i:I,I₁
local notation "Xp"=> unionL 6 (fun i:I=> burstY 6 q i (ritual (F i)))
local notation "T!"=> birthV Xp P.threshold
include hk hX ht hH
lemma litOn: Lure.On O q T! P.threshold:=onBirth O q Xp (gatherings 6 O q (fun i:I=> burstY 6 q i (ritual (F i))) (fun i=>burstP 6 O q i (ritual (F i)) (rendition hk rfl rfl ht hH (F i) (hX i)).1))
include hC ha
lemma marksC (j:J')(V:Grid c): Tablet.credits v ((T!).wick j V) ≤ wig (fun _=> Real.log (1+Γ)) j:=by
    apply unmaskV Xp j V _ ha
    let G:= burstY 6 q j.1 (ritual (F j.1)); have hK:= burstP 6 O q j.1 (ritual (F j.1)) (rendition hk rfl rfl ht hH (F j.1) (hX j.1)).1
    rw [show (Xp).mark j= G.mark j.snd from rfl,Tablet.polite_bill (G.z j.snd) _ (hK.stage _ _).1 (zero_lt_one.trans_le ht)]
    let X:=F j.1; have hx:pluck _ (burst q (G.z j.snd)) (G.mark j.snd V) = (ritual X).fill j.snd V:= congr_fun (burstReads 6 q j.1 _ j.snd) V
    obtain ⟨f,hf,hv,hS⟩:= (hC j.1).paid; change Creek.load (fun _=>v) (pluck _ (burst q (G.z j.snd)) (G.mark j.snd V)) ≤ Γ; rw [hx]; have he:f j.2 ≤ f j.2*Real.exp (4*coverNumber P.B ((ritual (F j.1)).addr j.2).support):= le_mul_of_one_le_right (hf _) (Real.one_le_exp (by positivity)); exact (hv _ _).trans (he.trans ((single_le_sum (fun i _=>mul_nonneg (hf i) (Real.exp_pos (4*(coverNumber P.B ((ritual (F j.fst)).addr i).support))).le) (mem_univ j.snd)).trans hS))
omit hk hX ht hH hC
-- count scattered Mark.Ph.W.We.Currency. choose β slow
variable (hf:Fires (wrap c ∘ o) m)
include ha hf hG
def rateX (Γ:ℝ)(B m D:ℕ)(a:ℝ):= ((B+B+1)^4*m*Fintype.card (Jars D ⊕ Unit):ℕ)*Real.log (1+Γ)*Real.exp (a*(81:ℕ))
lemma scopeV (a:ℝ)(ht:0≤a) : Ac.Hit (T!).spot P.B (fun _=> Real.log (1+Γ)) a (rateX Γ P.B m d a):=by
    let V:=T!; refine cotton P.B 1 V.spot 81 _ _ (Real.log_nonneg (by linarith)) ht (fun i=>?_) (glebe O V.spot (fun i=> i.fst) (fun j=>hG _ _) hf ?_)
    · exact (Corona.cover_mono (hG i.1 i.snd) _).trans (by have h:= Corona.tile (wrap c (o i.1)) 1 P.B P.B_pos; rw [one_mul] at h; exact h)
    intro i L h; have hX: L ⊆ Finset.univ.image fun j:I₁=> (⟨i,j⟩:J'):=fun j hj=>Finset.mem_image.mpr ⟨j.snd,mem_univ _,by rw [← h _ hj]⟩ -- may see L notation.P.L.
    exact (card_le_card hX).trans (card_image_le.trans (card_univ ..).le)
end Taxing
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Taxing.litOn
#print axioms YM.MassiveQCD.Sample.Taxing.marksC
#print axioms YM.MassiveQCD.Sample.Taxing.scopeV
