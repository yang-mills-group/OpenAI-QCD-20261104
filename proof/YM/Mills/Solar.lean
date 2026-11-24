import YM.Mills.Porch
import YM.Mills.Acorns
import YM.Mills.Mint
import YM.MassiveQCD.Charter.Lane
import YM.MassiveQCD.Apron.Card
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Apron
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {j k m i k₁ n:ℕ}
variable {z η p h a a' hQ v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f N E J} [Countable E][Countable J]
variable (G:Sun L' c f d η h z a a' m X) (U :Swathe L' d X W' P' h η a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
variable [Fintype I] (Y:Stitch.Tablet P₀ I)(A:I→Site f)(φ:ℝ)
local notation "M"=> Ribbon.ample N I
local notation "R'"=> trimP T O δ β b
local notation "B"=> radiusB τ
local notation "M'"=> highR L τ
local notation "Z'"=> G.equip N (radiusB τ)
local notation "Zⁱ"=> roof (G.equip N (radiusB τ)) P₀ 30 B
local notation "Y'" => closet H (G.equip N (radiusB τ)) (Zⁱ) Y A φ
local notation "U'" => loommark I (VarnC H U N)
local notation "X'" => loommark I (sailP H Γ N)
local notation "Vx" => tableau L' d K P₀ H G U Γ
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Uq"=> deckHue H (Z') P₀ (Zⁱ)
variable (F:Tree.Forest (Flight.visit L' K d).ratio) (θ:ℝ)
local notation "a₂"=> shiftCost L'.L τ (romp L'.L)
namespace Grove
open Glow
structure RoomV (Ω: Tree.Forest (Flight.visit L' K d).ratio) (Y:Fleet H ι N) (φ θ:ℝ) (κ:ι→ℝ):Prop where
    per :let P:=Y.suitcase Ω; let b:= Glow.simple Q L'.L μ C θ β τ; ∃ w,P.Depth b w (fun _=>0) ∧ Summable w ∧ (∀ V:Grid c,P.solves V)∧ P.Merit w (shiftCost L'.L τ (romp L'.L)) (token c N φ) ∧ ∃ v, (∀ i,w i*κ i≤ v i)∧ 0 ≤ v ∧ Ac.Hit P.ground (radiusB τ) v Q.relative (Glow.levelX L'.L θ τ)
local notation "UC"=> Glow.simple Q L'.L μ C θ β τ
local notation "Uw"=> fan L'.L θ τ
local notation "SM"=> Sum.elim
local notation "νP"=> lantern L'.L τ
variable {t q₀:ℝ}{q₁:I→Bool}{e₀:E→ℝ}{κ₀:J→ℝ} (pX:E→ℝ)
variable (hw:Y.Wave O.threshold q₁ A)
-- root charge factors
variable (A₀:E→ℝ)
-- pure indices in Short.System. a₀ flags.
private def maskV (p r:ℕ)(α:ℝ) (i:Tr f):ℝ:=if QCD.Jets.Sun.broad r p i then α else 1
def billP (H: Fj (Tr f) E J→Support c)(p r:ℕ)(α:ℝ)(i:Wound H):= α^(spent i.val).card*((∏ j∈ops i.val,maskV p r α j)*∏ j∈leftE i.val,A₀ j)
def incomesP (α:ℝ) : Wound (Zⁱ) ⊕ Varn f c ⊕ Gaze c→ℝ:= Sum.elim (billP A₀ (Zⁱ) m B α) (fun _=> α)
-- H in incomesP? B depends τ. Check lean binder variables.
lemma golden (A:Fj (Tr f) E J→Support c)(l n:ℕ)(b:ℝ)(hu:1 ≤ b)(hD:∀ i,1 ≤ A₀ i) (j:Wound A): 1 ≤ billP A₀ A l n b j:=by
    refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ hu) (one_le_mul_of_one_le_of_one_le (Finset.one_le_prod ?_) (Finset.one_le_prod fun i _=>hD i)); intro i _; unfold maskV; split; exact hu; exact le_rfl
variable (Dq: Porch L' d K H G U Γ N θ φ p t)
local notation "tX"=> QCD.Jets.Touch.chip L'.L τ
local notation "Φ"=> taxK L'.L τ 1
variable (hA:Cents P₀ e₀ κ₀ (fan L'.L θ τ) O.threshold)(hB:Fill P₀ e₀ κ₀ t t (taxK L'.L τ 1) 1 (Jets.Touch.chip L'.L τ) (highR L'.L τ))
variable (hX:P₀.Wave O.threshold) (hZ:P₀.Reframe)
variable {e:E→ℝ}{κ:J→ℝ} (hp' : Cents P₀ e κ (fan L'.L θ τ) O.threshold)
variable (hh: Y.Coins e κ (fan L'.L θ τ) O.threshold)
variable (htA:∀ i, 1 ≤ A₀ i)
variable (hM:Cents P₀ pX κ (fan L'.L θ τ) O.threshold) (hN: Fill P₀ pX κ (1/32) (1/32) (taxK L'.L τ (7/8)) 1 (chipV L'.L τ) (highR L'.L τ))
variable (hD:∀ i, (Real.exp (e i)-1)*A₀ i ≤ Real.exp (pX i)-1)
include hp' hh hw Dq hA hB hZ hX htA hM hN hD
local notation "h₀"=> maskV (f:=f) m B νP
local notation "hxK"=> billP A₀ (Zⁱ) m B νP
local notation "pv"=> Sum.elim hxK (fun (_:Varn f c⊕Gaze c)=> νP)
local notation "ζ"=> taxK L'.L τ (1/2)
-- Υ independent.SOLD. loyalty; wider geographic.Se.
set_option maxHeartbeats 700000 in
lemma goods : let Υ:=Tx; Υ.Famous ∧ RoomV L' d K H F Υ φ θ pv ∧ Υ.Feasible:=by
    intro Xq
    have he:= Dq.room; have hr:=roofs (Z') P₀ 30 B le_rfl he.2.2.2
    obtain ⟨X₀,h₁,h₂⟩:= Dq.stoves P₀ e₀ κ₀ hA hB; obtain ⟨he',hh'⟩:= h₂ pX κ hM hN
    let fΩ i:= Real.exp 1*terra G N B Uw φ i; let gΩ:= tenderP G N B Uw φ νP
    let s0:=mintD H (Z') P₀ Zⁱ fΩ e κ X₀; let s' := Mint.vipM H (Z') P₀ Zⁱ pX κ gΩ X₀ νP
    have hη: 0 ≤ Q.relative:=by unfold Target.relative; have hm:=Q.usable; have hv:=Q.bound; have ht:=Q.pos; linarith
    have hL:= Mint.incomeR H (Z') P₀ (Zⁱ) he' hM hX hh' (Real.one_le_exp (mul_nonneg (by norm_num) (fan_pos ..).le)) (zero_le_one.trans Dq.haze) he.1 he.2.1 hη
    have hb i: 0 ≤ s0 i:= votes H (Z') (Zⁱ) Y A φ hw hh h₁ he.1 i
    -- change GroveGrounds to votes
    have hH(i:Wound Zⁱ): (s0 i) * (hxK i) ≤ s' i:=(mul_comm ..).trans_le (Mint.upland H (Z') P₀ (Zⁱ) νP pX gΩ h₀ A₀ i he.1 hp'.pos hp'.non (fun i=>(h₁.spare i 1).nn) h₁.post Dq.haze (fun i=>by unfold maskV; split; exact Dq.haze; exact le_rfl) htA (fun _=>le_rfl) hD)
    have hk i:s0 i ≤ s' i:= (le_mul_of_one_le_right (hb i) (golden A₀ (Zⁱ) m B νP Dq.haze htA i)).trans (hH i)
    have hI: Ac.Hit (Uq).ground B s0 Q.relative (fundsL L'.L θ τ*(1-(1/2:ℝ))⁻¹):= Labels.raise_prices _ _ hb hL hk
    let xs:= Y'; have hP := homeP H (Z') P₀ (Zⁱ) h₁ hp' hX he.1 rfl Dq.loft (fun UU g he s=>fowl H P₀ L' d G UU g he B hZ s)
    have hΨ:= ensembleX H (Z') (Zⁱ) Y A φ hw hr.1 rfl (Stitch.Tablet.tonal G N B) hP Dq.loft hh h₁ he.1
    let A₁:= U'; let A₂:= X'; obtain ⟨hx,hz,hE',hQ'⟩:=Dq.pumps
    have hQ:Xq.Famous:= jungle xs (united A₁ A₂) hΨ (jungle A₁ A₂ (loping I _ hx) (loping I _ hz));
    have hδ:=he.1
    obtain ⟨s1,s2,h1,h2,p1,p2⟩:=Dq.whiter F
    have hp:=certify (F:=F) H (Z') (Zⁱ) Y A φ hw hr.1 hh h₁ hδ Dq.loft hI hη; obtain ⟨hs,hm,hK⟩:=hp
    let sX:=Sum.elim (s0) (Sum.elim s1 s2); have hx:= balanceP (united A₁ A₂) (steals (F:=F) H (Z') (Zⁱ) Y A φ hw hh h₁ hδ (fun _=>0) (fan_pos L'.L (1/4) τ).le 0 0) (balanceP A₂ (gait I _ h1) (gait I _ h2)); let pT:= Xq.suitcase F
    have hP : Ac.Hit pT.ground B (tariff sX (fun _=>0) (fun _=>0) Q.ε) Q.relative (leanX L'.L θ τ):=by
       rw [show tariff sX (fun _=>0) (fun _=>0) Q.ε=sX by ext; simp [tariff]]; exact Labels.together _ _ _ hI (Labels.together _ _ _ p1 p2)
    have hF: pT.Merit sX a₂ (token c M φ):=by
       have hv:=watch _ hx; rw [show max 0 (max (18*B) (18*B))=18*B by omega, show 0+(L'.L.val^4+1+1)=romp L'.L by rw [zero_add]; rfl] at hv; exact hv
    let v₁ i:= νP*s1 i; let v₂ i:= νP*s2 i; let vX:= Sum.elim s' (Sum.elim v₁ v₂); have hΓ i:(sX i) * (pv i) ≤ vX i:=by
       rcases i with i|i|i; exact hH i; exact (mul_comm ..).le; exact (mul_comm ..).le
    refine ⟨hQ,⟨sX,surveyP pT rfl hx.grow (fun _=>le_rfl) _ _ Dq.first hP, Summable.sum _ hs (hasSum_fintype _).summable,fun v=>legible H xs (united A₁ A₂) v (hm _) hQ,hF,vX,hΓ,fun i=>?_,?_⟩,?_⟩
    · rcases i with i|i|i; exact (hb i).trans (hk i); exact mul_nonneg (zero_le_one.trans Dq.haze) (hx.grow (.inr (.inl i))); exact mul_nonneg (zero_le_one.trans Dq.haze) (hx.grow (.inr (.inr i)))
    · exact Labels.together _ _ _ hL (Labels.together _ _ _ (heights_factor _ _ _ v₁ p1 (fun _=>rfl) (zero_le_one.trans Dq.haze)) (heights_factor _ _ _ v₂ p2 (fun _=>rfl) (zero_le_one.trans Dq.haze)))
    obtain ⟨hp⟩:=Villa.validH L' K d H G U P₀ (Γ:=Γ) he.2.2.2; constructor; rintro (i|i|i) U V h
    · exact hK.spark i U V h
    · refine hp (.inr (.inl i)) U V ?_; intro hh; apply h; exact (congr_arg (bearing I c N) hh).trans (map_zero _)
    refine hp (.inr (.inr i)) U V ?_; intro hh; apply h; exact (congr_arg (bearing I c N) hh).trans (map_zero _)
end Grove
end YM.MassiveQCD.Apron
#print axioms YM.MassiveQCD.Apron.Grove.goods
