import YM.Poised.Scrips
import YM.Poised.Treks
import YM.Poised.Cruise
import YM.Poised.Vaults
import YM.Poised.Harp
import YM.Poised.Watch
import YM.MassiveQCD.Lyre.Affair
import YM.MassiveQCD.Lyre.Revenue
import YM.Poised.Laurel
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
variable {z η p h a a' v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f 6 E J} [Countable E][Countable J]
variable {P₁:Plan j}{a₀ b₀ a₁ b₁ w mm vP:ℝ}{E₁:Offer 1 a₀ a₁}{E₂:Offer 2 b₀ b₁}
local notation "Xγ"=> (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) mm f))
variable (G:Sun L' c f d (coneK L'.L vP τ) h z a a' m (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) mm f))) (U :Swathe L' d (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) mm f)) W' P' h (coneK L'.L vP τ) a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
variable [Fintype I] (Y:Stitch.Tablet P₀ I)(A:I→Site f)(φ:ℝ)
local notation "M"=> Ribbon.ample 6 I
local notation "R'"=> trimP T O δ β b
local notation "B"=> radiusB τ
local notation "M'"=> highR L τ
local notation "Z'"=> G.equip 6 (radiusB τ)
local notation "Zⁱ"=> roof (G.equip 6 (radiusB τ)) P₀ 30 B
local notation "Y'" => closet H (G.equip 6 (radiusB τ)) (Zⁱ) Y A φ
local notation "U'" => loommark I (VarnC H U 6)
local notation "X'" => loommark I (sailP H Γ 6)
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Vx"=> tableau L' d K P₀ H G U Γ
local notation "Uq"=> deckHue H (Z') P₀ (Zⁱ)
set_option quotPrecheck false
local notation "loc"=> ((S').ratio.parent ∘ A)
local notation "Β" => Ribbon.banknote 6 loc φ
local notation "I'"=> Ribbon.Spine I
local notation "mx"=> Keys c 6 ⊕ Ribbon.Spine I
open Cupola Plate Spice Shells Sands Phased -- inspect
variable (F':Cash W τ μ L'.L Q o C T (lore (trimP T O δ β b)))
local notation "V₁"=> withdraw 6 loc φ
local notation "HU"=> VarnC H U 6
local notation "HP"=> united (VarnC H U 6) (sailP H Γ 6)
local notation "Vⁱ"=> Wound (roof (G.equip 6 (radiusB τ)) P₀ 30 B)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim Warmlet
variable {N₀:Libretto su n}{E₀:Heir.Record}{μ':Tr f→ℝ}{σ: E→ℝ}{Φ:J→ℝ}{x x₀ x₁ x₂ z₀ κ' ρ g₀ ι':ℝ}{χ:Chi}{B':BudgetPoint}{q':I→Bool}
variable (hw:Y.Wave O.threshold q' A) (htB:0<radiusB τ) (H': Hera.Rights su n)
local notation "Tz"=> fun i=>Real.exp 1*terra G 6 (radiusB τ) x₀ x i
open Cupola Elevator Massive.Poised Massive.Poised.Pipes Ac Cove.Send
variable {O₁:BudgetPoint}(F₁:Cash W τ μ L'.L Q o C T (lore (trimP T O₁ δ β b))) (hO₁:O.threshold=O₁.threshold)(hO:O.B=O₁.B)
variable (hB:B'.B=radiusB τ)(hL:Works P L'.L τ (L'.visit K d) T)(hP:Plays N₀ E₀ B' O₁ P T τ)
variable {Kq Φ₁ U₂ Dd Gd Gh Gn:ℕ}
variable (G':Sun L' c f d (coneK L'.L vP τ) h z a a' m (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) 0 f)))
variable (A₀ A₁ A₂ :ℝ)(hH:1≤A₀)(hα:B'.power=Kq)(hg:O₁.power=Gh)
variable (hr: Diary N₀ P j k Gh Gd Dd A₀ A₁ A₂)
variable (hn:6 ≤ n)(hD:Gn≤O₁.order)(hG:Gd≤Gn+1)(hW:Gd ≤ 2*n)(hk:2 ≤ Dd)(hQx:Gd ≤ U₂)
variable (hξ : O₁.threshold = fiery su τ L'.L)(hOc:O₁.B= highR L'.L τ)(hT:betaF su τ L'.L/2 ≤ β) (hX:2*(radiusB τ+1)< f.val)(ha:0<a)(hh':|mm| ≤ haloK L'.L τ)
variable {t ν:ℝ}(hSup:Supplies L' d K H G U Γ Y A φ χ q' t ν B'.order B'.power)
local notation "F§"=> Warmlet H HP (Z') P₀
variable (Z: Warmlet H (united (VarnC H U 6) (sailP H Γ 6)) (G.equip 6 (radiusB τ)) P₀)
variable (w:Clusters (vantage L' d K H G U Γ Y A φ).Bright → RegularAddress c)(hw':∀ i,(w i).support=GasP.seatP (vantage L' d K H G U Γ Y A φ).lightF i)
variable (e:E)(hE:leftE Z.label.val={e})(hq: ops Z.label.val=∅)(hp:(Y.markers Z.label.val).Nonempty)(h'Q: Seats H χ)
variable (Xb: Cover)(hY:wrap f Xb=(P₀.row e).site)(hU:φ ≤ A₀*x₀)(hΦ:0 < x₀)(hΘ: Flame (Elevator.tap (q:=q') P₀ Y e) O₁ (P₀.row e).support (P₀.row e).site x₀ Dd U₂ κ')
variable (S0:ℕ)(t0:ℝ)
variable (hV': Menus P₁ N₀ E₀ Kq Gh Dd U₂ k A₀ (pup Gd A₁+pup Gd A₂) H' Q (Flight.visit L' K d).patch L'.L W o μ C a vP h z a' m χ τ S0 t0)
variable (ht': O₁.B ≤ 2*radiusB τ)(hτ: coverNumber O₁.B (brimW (G.equip 6 (radiusB τ)) P₀ Z.label.val)≤ S0)
-- preserve price via porch
local notation "Sγ"=> Warmlet.perch H HP (Z') P₀ F' Z
local notation "nv"=> coverNumber O₁.B (brimW (G.equip 6 (radiusB τ)) P₀ Z.label.val)
open Massive.Poised.Chute Planned.PrimaryIntegral295.Carrier Massive.SourceRead
variable (XB:Cover) (q0 p0 v0:ℕ)(d0:ℝ)(Θ: TaperHol)
local notation "Yg"=> (Sγ).support
local notation "Xg"=> (P₀.row e).support
local notation "Fp"=> Elevator.tap (q:=q') P₀ Y e
local notation "Fₓ"=> (prescription L' d K A φ (Y.markers Z.label.val) q') ∘ (crude Tx χ w).view (individual Z.code)
-- actual supports; expose intrinsic X→Yg. Price support reach explicit.M.Point. Extra toll.T.B'
variable (hSize:coverNumber O₁.B (P₀.row e).support≤ q0)(hRe:Laurent.size (cellar L'.L Xb-XB) ≤ p0)
open TrainG Stative
variable (hA₃:B'.order=n)(hA₄:p=1) {q'h:ℕ}{μ₁ μ₂ bracq β₂:ℝ} {p'k:ℕ}(hNq: O₁.order=q'h)
variable (ht: T.R.A0=linesOf L' P.bind.penalty)
-- Kernel orientation equal.S
variable (hPΘ: K=P.bind)
variable (hAsk: Ledger P₁ Q (L'.visit K d).patch N₀ E₀ o μ C a vP h z a' m k Gn χ Θ H' Gd p0 Gh Kq q'h U₂ Dd A₀ A₁ A₂ τ)(hPre:Prebit Q j k Gh Gd Dd Kq N₀ A₀ A₁ A₂ μ₁ μ₂ bracq p'k) (hN:L'.L.val ≥p'k)
variable (ha0:Gn<n)(hx0:Fintype.card (Palette.ZBand Gn)< U₂)(hΔ:Gn/2≤j)(hpΩ:Gn*Gn ≤ Kq)(hXQ:Beacon.surface Gn ≤ Dd)
include hAsk hPre hN ha0 hn hX hp hh' ha hNq hAsk hΘ hY hH hα hP hB hg hE hq ht hSup hw' h'Q hO₁ hT hΦ hU hξ hOc hO
-- bill for ANY prince. no Short.Q potential support.Motion given later. Size-est.TechB.Small budget.Ph
local notation "sz"=> coverNumber O₁.B (P₀.row e).support
local notation "sz'"=> coverNumber B Yg
local notation "r!"=> (Sγ).site
local notation "β'!"=>Real.exp (μ₂*sz')*badgeQ N₀ B' Gd nv
-- emissive.
include hP hL F₁ G' hG hW hk hQx
omit ht hPre hw' G' F₁ hP hL ha0 hn hX hp hh' ha hNq hΘ hY hH hB hg hT hΦ hU hξ hSup h'Q hO₁ hG hW hk hQx hN -- remove simplify
include hPre hN
lemma prince_cost : β'! ≤ bracq*Real.exp (μ₁*sz):=by
    let p:Duke H HP (Z') P₀:= ⟨Z,e,(slate _ _ _ _ _ _).2 ⟨hE,hq⟩⟩; have hx: col H HP (Z') P₀ p = e:=by
       have hx₀:=duke H HP (Z') P₀ p; have ht:=congr_arg Fj.leftE hx₀; exact Finset.singleton_injective (((slate H HP (Z') P₀ Z _).1 hx₀).1.symm.trans hE)
    have hr:O.B≤2*B:=hO.symm ▸ hOc.symm ▸ hAsk.shores
    have hη: (Z').trim+1 ≤ O.B+O.B:= hO.symm ▸ hOc.symm ▸ hAsk.grows
    have ht':= sizeP H HP (Z') P₀ p hη; rw [hx,hO] at ht'; have hs:= terrestrial H HP (Z') P₀ F' p le_rfl hr hAsk.holy; rw [hx,hO] at hs; exact hPre.tax _ hN B' hα _ _ (sliceL L' d) rfl _ _ _ ht' hs
include F₁ G' hw' hP hL ha0 hn hX hp hh' ha hNq hΘ hY hH hB hg hT hΦ hU hξ hSup h'Q hO₁ hG hW hk hQx
lemma tribute (hS:Warmlet.Small H HP (Z') P₀ Z F')(h0:∀ J: Labels.Jet su,∀ i<Gd,WardBin.leading i (Beacon.moment (d:=Gn) Θ Xb J Fp)=0):
     let τ':=(Kit.slope L'.L)^Gd * (bracq*tipW N₀ H' U₂ Gd A₁ A₂ (pup Gd A₂))
     Flame Fₓ B' Yg r! φ Dd U₂ (Real.exp (μ₁*sz-μ₂*sz')*τ'*κ'):=by
     have hu:Gn≤O₁.order:= ha0.le.trans hP.rehearsed.orders; intro τ'; apply Facets.leFlame (tips L' d K H G U Γ Y A φ F' H' F₁ hO₁ hB hL hP G' A₀ A₁ A₂ hH hα hg hPre.lore hAsk.vows hn hu hG hW hk hQx hξ hOc hT hX ha hh' hSup Z w hw' e hE hq hp h'Q Xb hY hU hΦ hΘ Θ h0 hS)
     apply mul_le_mul_of_nonneg_right _ hΘ.sight.travels
     let f:= tipW N₀ H' U₂ Gd A₁ A₂ (pup Gd A₂); let A:= (Kit.slope L'.L)^Gd; have hA : 0 ≤ A:= pow_nonneg (Kit.slope_pos _).le _; have hf:0 ≤ f:=by unfold f tipW; have h:= sinR H'; exact add_nonneg (add_nonneg (by norm_num) h) (sum_nonneg fun i _=> zero_le_one.trans (senior H' _ _ _ _ _ hPre.lore.warm hPre.lore.stellar (pup_pos hPre.lore.stellar _))) -- args
     have he:=prince_cost L' d K H G U Γ F' H' hO A₀ A₁ A₂ hα hOc Z e hE hq p0 Θ hAsk hPre hN
     have hβ : badgeQ N₀ B' Gd nv ≤ Real.exp (μ₁*sz-μ₂*sz')*bracq :=by
        rw [Real.exp_sub, div_mul_eq_mul_div, le_div_iff₀ (Real.exp_pos _)]; exact le_trans (le_of_eq (mul_comm ..)) (he.trans_eq (mul_comm ..))
     exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ hA) hf).trans_eq (by unfold τ'; change A*(_*bracq)*f = _*(A*(bracq*f)); ring)
-- projection key.Mar.Window Cart.
include hRe hXQ hpΩ hΔ hx0 ht hPΘ
local notation "KFo"=>Massive.Poised.Chute.kite L' d T Fp Yg
local notation "Cℓ"=> relief L'.L τ*κ'
variable (hy:coverNumber O₁.B (P₀.row e).support ≤ O₁.B)(hSZ:gateH p0 τ≤ c.val)(hk':4≤k)
include hy hSZ hk'
omit hG hW hk hQx in
set_option maxHeartbeats 600000 in
lemma projected (hS:Warmlet.Small H HP (Z') P₀ Z F') : ∃ (y: Massive.UV.Pol Gn), y∈ Massive.UV.cap Gn ∧ Beacon.ActionTest Θ XB KFo y∧ ∀ i':Rings Gn, (∀ A:Massive.UV.Pol Gn,A∈Massive.UV.cap Gn →Beacon.ActionTest Θ XB Fₓ A → ‖Stative.fare i' A B'.threshold φ-Stative.fare i' y B'.threshold φ‖≤ Cℓ) ∧ ((∀ J:Labels.Jet su,∀ k < Massive.UV.weight i'.val,WardBin.leading k (Beacon.moment (d:=Gn) Θ Xb J Fp)=0)→ ∀ (U:Massive.UV.Pol Gn), U∈Massive.UV.cap Gn→ Beacon.ActionTest Θ Xb Fp U→ ‖Stative.fare i' y B'.threshold φ - (Kit.slope L'.L:ℂ)^(Massive.UV.weight i'.val) * Stative.fare i' U B'.threshold φ‖ ≤ Cℓ):=by
    obtain ⟨T₁,σ1,hσ,hσ',he0⟩:=hAsk.stakes; let Lfa:= L'.L; obtain ⟨g1,g2⟩:= (he0 c f).pays L' rfl; have hZΛ: LinksT (c:=c) (f:=f) T₁ σ1 A₀ Θ H' L'.L j k p0 Kq Gn Dd K (deckH p0 τ) τ (relief L'.L τ) := (by rw [hPΘ]; exact he0 _ _);  have hr:O₁.B≤2*B:= hOc.symm ▸ hAsk.shores
    have hxB:= hy.trans hr; have hx1:= ticketG p0 τ c O₁ sz hr hxB hSZ; have hp':nv ≤ mineH τ:=by
       rw [← hO]; let p:Duke H HP (Z') P₀:= ⟨Z,e,(slate _ _ _ _ _ _).2 ⟨hE,hq⟩⟩; have hp: col H HP (Z') P₀ p =e:= Finset.singleton_injective (((slate H HP (Z') P₀ _ _).1 (duke H HP (Z') P₀ p)).1.symm.trans hE)
       apply le_trans (sizeP H HP (Z') P₀ p (hO.symm ▸ hOc.symm ▸ hAsk.grows)); rw [hp,hO]; exact mul_le_mul_right' hxB _ -- deprecated
    obtain ⟨hI,hSX,hθ,hκ,hW',ht',hU',hPV,hΩ0⟩:= moonlight (Gn:=Gn) L' d K H G U Γ Y A φ F' H' F₁ hO₁ hB hL hP G' A₀ A₁ A₂ hH hα hg hPre.lore hn hξ hT hX ha hh' hSup Z w hw' e hE hq hp h'Q Xb hY hU hΦ hΘ (mineH τ) (fan L'.L (-1/2) τ) hAsk.near hr hp' XB sz p0 (deckH p0 τ) le_rfl hRe hx1 hS ha0 hx0 hpΩ hXQ σ1 T₁ hk' (ht.symm ▸ g2) g1
    have hv:ContDiffAt ℝ Gn (Fp ∘ increment 1) 0 := (hΘ.sight.use 1 (Next.Foundations.one_healthy _ _ O₁.threshold_pos.le)).of_le (by exact_mod_cast (ha0.le.trans hP.rehearsed.orders)); obtain ⟨y,hy,hh⟩:=Beacon.obtainsD Θ XB KFo (powered_germ _ _ _ _ hv)
    exact ⟨y,hy,hh,fun i=> ⟨fun A4 hs hz=> hZΛ.bridge L' d T B' Fp Fₓ Yg r! XB φ κ' A4 y rfl hy hs hh hz hSX hθ hv (Sγ).anchor hS hκ ht' hα hXQ hpΩ hU' hΘ.sight.travels hΩ0 i,fun q U4 hK hU=> hZΛ.honored L' d T O₁ Xg Yg Xb XB x₀ φ B'.threshold κ' U₂ rfl (by rw [← show K.penalty=P.bind.penalty from congr_arg KernelChoices.penalty hPΘ] at ht; exact ht) hP.rehearsed.orders hx0 hI Fp U4 y hW' hK hy hU hh hΔ hPV i q⟩⟩
end YM.MassiveQCD.Lyre
#print axioms YM.MassiveQCD.Lyre.projected
