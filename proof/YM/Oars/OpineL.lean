import YM.Cardinal.Ficus
import YM.Oars.Lavender
import YM.Oars.OpaqueL
import YM.Cardinal.Wand
/-! # Bridge Cupola and Siege.Tower: paid on ONE trajectory -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Lyre
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}
variable {j k m i k₁ n:ℕ}
variable {z vP p h a a' v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f 6 E J} [Countable E][Countable J]
variable {P₁:Plan j}{a₀ b₀ a₁ b₁ mm :ℝ}{E₁:Offer 1 a₀ a₁}{E₂:Offer 2 b₀ b₁}
local notation "Xγ"=> (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) mm f))
variable (G:Sun L' c f d (coneK L'.L vP τ) h z a a' m (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) mm f))) (U :Swathe L' d (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) mm f)) W' P' h (coneK L'.L vP τ) a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
namespace Drawing.Claro
open Massive.Poised QCD.Shells Cupola Plate Card Iris Puff Patron
open Ac QCD.Cove.Send Warmlet Push.Local Massive.Poised.Plans Massive.Poised.Plans.Stamp
open Massive.UV
variable {E' K':Type}{q': Bool}
-- Pu.6
variable {IE Gp:Type} [Fintype IE]
variable (Qx:Puff f 6 E' q')(Tq:Film f 6 IE K')(Oq: Charter (Gp:=Gp) P₀ Qx Tq)
variable (A A' :Cover) (Qe: Seal 6 (wrap f A) Qx)
local notation "Aᴮ"=>Oq.loc A
set_option quotPrecheck false
local notation "A⁺"=> ((Flight.visit L' K d).ratio.parent ∘ (Aᴮ))
local notation "Tᴮ"=>fun (_:Unit)=>wrap c A'
local notation "K₀"=> ({Oq.K0}:Finset IE)
local notation "qᴮ"=>Oq.style
local notation "Y"=> Oq.V
variable (φ:ℝ)
local notation "B"=>radiusB τ
local notation "Z'"=> G.equip 6 (radiusB τ)
local notation "Zⁱ"=>QCD.Jets.Touch.roof (G.equip 6 (radiusB τ)) P₀ 30 B
local notation "S₁"=>united (VarnC H U 6) (sailP H Γ 6)
local notation "Tx"=> vantage L' d K H G U Γ (Y) (Aᴮ) φ
local notation "U₀"=>Warmlet H S₁ (Z') P₀
local notation "D'"=>Sum.elim (fun u:Wound Zⁱ=> (Y).markers u.val) (fun _: Varn f c⊕Gaze c=>∅)
local notation "χ'"=>swingE 6 Tx D'
set_option quotPrecheck false
open Warmlet MassiveQCD.Lyre Sands
variable {χ:Chi}{α ξ θ t t₀ x x₀ x₁ κ α₁ α₂ ε:ℝ}{P₂: BudgetPoint}
variable (X:Clusters (vantage L' d K H G U Γ (Oq.V) (Oq.loc A) φ).Bright → RegularAddress c)
variable (hM:∀ i,(X i).support= GasP.seatP ((vantage L' d K H G U Γ (Oq.V) (Oq.loc A) φ).lightF) i)
variable (F':Cash W τ μ L'.L Q o C T (lore (trimP T O δ β b)))
local notation "Cⁱ"=> crude Tx χ X
local notation "a⁺"=>  budAtlas (A⁺) (30*B)
local notation "I✡"=> Oq.Role (A⁺) (Cⁱ) (χ')
local notation "E✡"=> (Reel.render 6 (A⁺) φ t₀ Cⁱ (χ') Oq.demand)
local notation "H✡"=> Oq.helm (A⁺) Cⁱ (χ')
local notation "Z✡"=> Reel.speaker (qᴮ) (E✡) ∘ H✡
variable (hSup:Supplies L' d K H G U Γ (Oq.V) (Oq.loc A) φ χ (Oq.style) t θ P₂.order P₂.power)
local notation "kindY"=> (address H S₁ (Z') P₀)
local notation "ι'"=> Clusters (Tx).Bright
-- naming geometry
local notation "Iⁱ"=> aisle L' d K H G U Γ Qx Tq Oq A φ X F'
variable {u₀ u₁ αe:ℝ}{Dx nL r:ℕ}
local notation "Q✡"=> fun i:I✡=>(Iⁱ) i.val
local notation "P✡"=>fun i:I✡=> (X i.val).support
local notation "D✡"=> fun i:I✡=> Dated Tx Fury nectarP τ i.val
variable (hB:P₂.B=radiusB τ)(he:0 ≤ αe)
-- sigma actual, require large compared frost for soft payment. Use a>0 separately
variable (hR:separation ((Flight.visit L' K d).ratio.parent (wrap f A)) (wrap c A') ≤ k₁)(hp:k₁ ≤ 10* radiusB τ)
local notation "Uⁱ"=> A⁺ Oq.K0
local notation "t✡"=> wrap c A'
local notation "tr"=> towerE L' d K H G U Γ Qx Tq Oq A φ X Qe hM (χ:=χ)
open Massive.Poised Massive.Poised.Pipes Massive.Poised.Plans.Girdle
-- A.Call.WhereOut
local notation "κ'"=> warmA L' d K H G U Γ Qx Tq Oq A φ X F'
local notation "ξχ" => Girdle.tariff k₁ 2 P₂.power P₂.order* Reel.voiceE 2 ε (radiusB τ)
local notation "Φ"=>ξχ*flowM L'.L τ
local notation "Ψ"=>ξχ*jelly L'.L τ
local notation "D⁻"=> (radiusB τ:ℝ) /frostQ Q.halo
local notation "Δ"=> chill Q.halo τ
-- Out of Small
variable (hPx:BudgetPoint)(σ:E→ℝ)
-- Tap at registered labels. Range equivalence.W.
variable (Θ:Massive.SourceRead.TaperHol) {R₁:BudgetPoint}
variable (F₁:Cash W τ μ L'.L Q o C T (lore (trimP T R₁ δ β b))) (hO₁:O.threshold=R₁.threshold)(hO:O.B=R₁.B)
variable (G':Sun L' c f d (coneK L'.L vP τ) h z a a' m (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) 0 f)))
open Massive.Poised.TrainG PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Planned.PrimaryIntegral295.Carrier
variable (N₀:Libretto su n)(V:Hera.Rights su n){E₀:Heir.Record}
variable (hWorks:Works P L'.L τ (L'.visit K d) T)(hPl:Plays N₀ E₀ P₂ R₁ P T τ)(hSeat: Seats H χ)
variable {Gh Gn Gd Kq s₀ pL m₀ M0:ℕ}{brac μ₁ μ₂ A₀ A₁ A₂ T₀:ℝ}
variable (htV: β≥betaF su τ L'.L/2) (hΔ:|mm|≤ haloK L'.L τ)(hξ: R₁.threshold=fiery su τ L'.L)(hOc:R₁.B=highR L'.L τ)
variable (hg:L'.L.val ≥ m₀)(hPre:Prebit Q j k R₁.power Gd Dx P₂.power N₀ A₀ A₁ A₂ μ₁ μ₂ brac m₀)
-- don't write (S')
variable (hA:Ledger P₁ Q (Flight.visit L' K d).patch N₀ E₀ o μ C a vP h z a' m k Gn χ Θ V Gd k₁ R₁.power P₂.power R₁.order nL Dx A₀ A₁ A₂ τ)
variable (hK:0<u₀)(hw:0<t₀)(hX:u₀*t₀ ≤ φ)(hpF:φ ≤ A₀*x₀)(hv1:0<x₀)(ha:0<a)(hη:1 ≤ A₀)(hn:6 ≤ n)(hN:Gn<n)(hJ:4 ≤ k)
variable (hY:2*(radiusB τ+1)< f.val)(hvDx:2 ≤ Dx)(hvD:Gd ≤ Gn+1)(hvL:Gd ≤ nL)(ht:P₂.order=n)
local notation "CZ"=> tr
local notation "Ix"=> I✡
local notation "R★" p=> ((kindY).symm (Oq.ear p)).val
local notation "pu"=> brac*Massive.Poised.tipW N₀ V nL Gd A₁ A₂ (pup Gd A₂)
variable (i' :E')(hS: warmA L' d K H G U Γ Qx Tq Oq A φ X F' ((towerE L' d K H G U Γ Qx Tq Oq A φ X Qe hM (χ:=χ)) i'))
variable (hF : Flame (Qx.fill i') R₁ (Qx.addr i').support (wrap f A) x₀ Dx nL T₀)(hχ:∀ J:Labels.Jet su, ∀ i<Gd,WardBin.leading i (Beacon.moment (d:=Gn) Θ A J (Qx.fill i'))=0)
include hA hPre hg hM Qe hF hS hWorks hPl hSeat hO₁ hO hB hSup htV hΔ hξ hOc hK hw hX hpF hv1 ha hη hn hN hY hvDx hvD hvL hR
local notation "α⁰"=>price k₁ P₂.power P₂.order Dx nL
local notation "Oⁱ"=>coverNumber (radiusB τ) ((Q✡) ((tr) i'))
local notation "PV"=> coverNumber R₁.B (Qx.addr i').support
open Kites
local notation "Em" p => Real.exp (μ₁ * coverNumber R₁.B (Qx.addr i').support- μ₂* p) * (Kit.slope L'.L ^ Gd * pu) *T₀
include F₁ G' hχ

variable (hAR:T.R.A0=linesOf L' P.bind.penalty) (hG':K=P.bind)(hr:Laurent.size (cellar L'.L A - A') ≤ k₁)(hZG: gateH k₁ τ≤c.val)
variable (hnL:Fintype.card (Massive.Poised.Palette.ZBand Gn)<nL)(hΔ':Gn/2≤j)(htQ:Gn*Gn ≤P₂.power)(htY:Beacon.surface Gn≤Dx)
omit hvDx hvL hR hvD
include hr hAR hG' hZG hJ hnL hΔ' htQ htY
open Stative Massive.Poised.TrainG
set_option maxHeartbeats 590000 in
lemma read_step (hs:coverNumber R₁.B (Qx.addr i').support ≤ R₁.B)(y₀ x':Label Gn)(e:Rings Gn)(hv: Beacon.ActionTest Θ A (Qx.fill i') y₀.val)(hT: Beacon.ActionTest Θ A' (Z✡ (tr i')) x'.val)(hp:Massive.UV.weight e.val ≤ Gd) :
    ‖Stative.fare e.val x'.val P₂.threshold u₀ - (Kit.slope L'.L:ℂ)^Massive.UV.weight e.val * Stative.fare e.val y₀.val P₂.threshold (u₀*t₀)‖ ≤ 2 * relief L'.L τ*T₀:=by
    let u:= tr i'; let z:= R★ i'; have htK:u.val=individual z.code:= tower_step ..
    obtain ⟨b,hG,hS⟩:= hS
    rw [show b=z from (copyQ H S₁ (Z') P₀ b z (hG.symm.trans htK))] at hS
    let r' :=perch H S₁ (Z') P₀ F' z; let b' :=Oq.ear i'; obtain ⟨hm1,hm2⟩ : leftE z.label.val={b'} ∧ ops z.label.val=∅:= (slate H S₁ (Z') P₀ _ b').1 (enlist ..)
    have h1:r'.support=(Iⁱ) u.val:= ((tame L' d K H G U Γ Qx Tq Oq A φ X F' u z htK).trans (congr_arg RegularAddress.support (show trunkP H S₁ _ _ F' z= r' from if_pos hS))).symm
    have hTx: (P₀.row b').support=(Qx.addr i').support:= congr_arg RegularAddress.support (Oq.homeP i'); have hZ:wrap f A=(P₀.row b').site:=((congr_arg RegularAddress.site (Oq.homeP i')).trans (Qe.anchor _)).symm
    let U':=(Y).markers z.label.val; let g:= fun (x:ι')=> (prescription (N:=6) L' d K Aᴮ φ U' qᴮ) ∘ (Cⁱ).view x; have hy: U'=K₀:= (name_stamp L' d K H G U Γ Y Aᴮ φ z).symm.trans (stamps L' d K H G U Γ Qx Tq Oq A φ _)
    let T':= Em (coverNumber (radiusB τ) r'.support); let f0:= g u.val
    have ht0 : ((Em (coverNumber (radiusB τ) r'.support)))=(Em (coverNumber (radiusB τ) ((Q✡) ((tr) i')))):=by rw [h1]
    have hι := tapis Qx Tq Oq i'; have hP:= projected L' d K H G U Γ Y Aᴮ φ F' V F₁ hO₁ hO hB hWorks hPl G' A₀ A₁ A₂ hη rfl rfl hn hξ hOc htV hY ha hΔ hSup z X hM b' hm1 hm2 (show (U').Nonempty from hy.symm ▸ singleton_nonempty _) hSeat A hZ hpF hv1 (by change Flame (Elevator.tap (q:=qᴮ) P₀ _ (Oq.ear i')) R₁ _ _ x₀ Dx nL T₀; rw [hι,← hZ,hTx]; exact hF) A' k₁ Θ hr rfl hAR hG' hA hPre hg hN hnL hΔ' htQ htY (by rw [hTx]; exact hs) hZG hJ hS
    obtain ⟨p,hq,hK',hh⟩:= hP; have hz:Z✡ u= engine t₀ (Keys c 6) ∘ g (individual z.code):=(spool L' d K H G U Γ Qx Tq Oq A φ X u z htK).trans (congr_arg (fun i:ι'=> engine t₀ (Keys c 6) ∘ g i) htK)
    let v:=g (individual z.code); let P₃:= Sieve.dimming 1 (t₀⁻¹) Gn x'
    have he: Beacon.ActionTest Θ A' v P₃.val :=by
         have ht:= Orientation.actsWear Θ A' Gn (engine t₀ (Keys c 6) ∘ v) x' t₀⁻¹ (hz ▸ hT)
         have h: engine t₀⁻¹ (Keys c 6)∘ engine t₀ (Keys c 6) ∘ v=v:=by funext i; simp only [Function.comp_apply,Kites.makes,inv_mul_cancel₀ hw.ne',Wage.engine₁]
         exact h ▸ ht
    have h0:∀ (J:Labels.Jet su) (k:ℕ), k < Massive.UV.weight e.val → WardBin.leading k (Beacon.moment (d:=Gn) Θ A J (Elevator.tap (q:=qᴮ) P₀ Y b'))=0:=by intro J k hk; exact (hι.symm ▸ (hχ J k (Nat.lt_of_lt_of_le hk hp))) -- motive adjust
    have hm':= (hh e).2 h0 y₀.val ((label_law _).mp y₀.property).1 (by rw [hι]; exact hv)
    let s₀ :ℂ:= (Kit.slope L'.L:ℂ)^Massive.UV.weight e.val
    have he' := (hh e).1 P₃.val ((label_law _).1 P₃.property).1 he
    let o' p y:= Stative.fare e.val p P₂.threshold y
    have hu: ‖o' P₃.val φ - s₀ * o' y₀.val φ‖ ≤2*relief L'.L τ*T₀:= (norm_sub_le_norm_sub_add_norm_sub (o' P₃.val φ) (o' p φ) (s₀*o' y₀.val φ)).trans ((add_le_add he' hm').trans_eq (by ring))
    have hF': o' P₃.val (u₀*t₀)=o' x'.val u₀:=by
       unfold o' Stative.fare; rw [rank_fee,rank_fee]; change _ * coord _ (Sieve.widths _ _ x'.val)= _; rw [rank_fee]; have hF': (t₀:ℂ)≠0:=by exact_mod_cast hw.ne'
       simp only [Complex.ofReal_one, one_pow,one_mul,Complex.ofReal_inv,Complex.ofReal_mul,mul_pow,inv_pow]; field_simp
    change ‖o' _ _ - s₀*_‖≤_; rw [← hF']; apply le_trans _ hu; unfold o' Stative.fare; simp_rw [rank_fee]; let U':= P₂.threshold; let x:= coord e.val P₃.val; let z:= coord e.val y₀.val
    let f(a:ℂ):= ((U':ℂ)^Sieve.life e.val.1*a)*x - s₀*((U':ℂ)^Sieve.life e.val.1*a*z)
    have hf(a:ℂ):f a=a*f 1:=by unfold f; ring
    change ‖f ((↑(u₀*t₀):ℂ)^e.val.2.card)‖≤ ‖f ((φ:ℂ)^ e.val.2.card)‖; rw [hf,hf ((φ:ℂ)^e.val.2.card),norm_mul,norm_mul, norm_pow,norm_pow,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (mul_pos hK hw).le,Real.norm_of_nonneg (by exact (mul_pos hK hw).le.trans hX)]; gcongr
end Drawing.Claro
end YM.MassiveQCD.Lyre
#print axioms YM.MassiveQCD.Lyre.Drawing.Claro.read_step
