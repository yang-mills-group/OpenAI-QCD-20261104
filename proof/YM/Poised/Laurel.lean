import YM.Poised.Compas
import YM.MassiveQCD.Charter.Plural
import YM.QCD.Purse.Debit
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
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {j k m i k₁ n:ℕ}
variable {z η p h a a' v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
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
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Vx"=> tableau L' d K P₀ H G U Γ
local notation "Uq"=> deckHue H (Z') P₀ (Zⁱ)
set_option quotPrecheck false
local notation "loc"=> ((S').ratio.parent ∘ A)
local notation "Β" => Ribbon.banknote N loc φ
local notation "I'"=> Ribbon.Spine I
local notation "mx"=> Keys c N ⊕ Ribbon.Spine I
open Cupola Plate Spice Shells Sands Phased -- inspect
variable (F':Cash W τ μ L'.L Q o C T (lore (trimP T O δ β b)))
local notation "V₁"=> withdraw N loc φ
local notation "HU"=> VarnC H U N
local notation "HP"=> united (VarnC H U N) (sailP H Γ N)
local notation "Vⁱ"=> Wound (roof (G.equip N (radiusB τ)) P₀ 30 B)
variable (Z:Wound (roof (G.equip N (radiusB τ)) P₀ 30 (radiusB τ))) (hF: spent Z.val=∅)
include hF
local notation "sξ"=> (Y.markers Z.val)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
variable {N₀:Libretto su n}{E₀:Heir.Record}{μ':Tr f→ℝ}{σ: E→ℝ}{Φ:J→ℝ}{x x₀ x₁ x₂ z₀ κ' ρ g₀ ι':ℝ}{χ:Chi}{B':BudgetPoint}{q':I→Bool}
variable (hw:Y.Wave O.threshold q' A) (htB:0<radiusB τ) (H': Hera.Rights su n)
variable (D₁:ℕ) (hx: ( (lore (trimP T O δ β b)).activities.reg D₁).support= brimW (G.equip N (radiusB τ)) P₀ Z.val) (hs:x₂ ≤ x)(hv:0<x₂)(hf:0 < φ)
local notation "X₁"=> Brim.plate F' D₁
local notation "Tz"=> fun i=>Real.exp 1*terra G N (radiusB τ) x₀ x i
local notation "Ωv"=>prescription L' d K A φ (Y.markers Z.val) q'
variable (hp: Peak (G.equip N (radiusB τ)) O.threshold x₀ x x₁ (fun i=>Real.exp 1*terra G N (radiusB τ) x₀ x i))
open Filter Ac Cupola Elevator
variable {O₁:BudgetPoint} (F₁:Cash W τ μ L'.L Q o C T (lore (trimP T O₁ δ β b))) (hO₁:O.threshold=O₁.threshold)(hO:O.B=O₁.B)
variable (hB:B'.B=radiusB τ)(hL:Works P L'.L τ (L'.visit K d) T)(hP:Plays N₀ E₀ B' O₁ P T τ)
variable {g'' θ kal α v₂ p₁ p₂ g W₀ W₁ ψ Y₂ θ' mm:ℝ}
-- price tags before using SMART tilt signal.Front Ω political. Monic receipts.
variable (hW:News P L'.L τ W Q o μ C n N₀ E₀ χ B'.power p₁ p₂ g₀ (L'.visit K d).patch)
variable (hΓ:Seats H χ)(hy:coverNumber (radiusB τ) (Brim.plate F' D₁).support ≤radiusB τ)
variable (Ω:Clusters (vantage L' d K H G U Γ Y A φ).Bright → RegularAddress c)
variable (hxP:(vantage L' d K H G U Γ Y A φ).Famous)(hzQ:Colored (vantage L' d K H G U Γ Y A φ))
local notation "J!"=>(vantage L' d K H G U Γ Y A φ).Bright
variable {qc:(vantage L' d K H G U Γ Y A φ).Bright}
variable (hN:Sands.Aliased (vantage L' d K H G U Γ Y A φ) qc (.inl Z))
variable (hV:Sight ((vantage L' d K H G U Γ Y A φ).fullA qc.val) (Brim.plate F' D₁).site 2 B' x₂ ((prescription L' d K A φ (Y.markers Z.val) q') ∘ (crude (vantage L' d K H G U Γ Y A φ) χ Ω).view (individual qc)) Y₂)
local notation "H★"=> (prescription L' d K A φ (Y.markers Z.val) q') ∘ (crude Tx χ Ω).view (individual qc)
variable {P₁:Plan j}
variable (hC: Coins B' O₁ P L'.L E₀ Q.halo N₀ H' τ β x₀ x η h a z₀ z a' h p₁ g₀ θ' mm p₂ x₁ x₀ θ P₁ N m) (hY:Y.Coins σ Φ x₀ O.threshold)
variable (hk: Trees.Ready (QCD.Jets.Touch.roof (G.equip N (radiusB τ)) P₀ Q.halo (radiusB τ)) (radiusB τ) (paidSet (G.equip N (radiusB τ)) P₀ (fun i=> Real.exp 1*terra G N (radiusB τ) x₀ x i) σ Φ x₁ (cashM L'.L θ τ) W₀ 1) α v₂ p W₁)(hD:1 ≤ cashM L'.L θ τ)
local notation "ψ₁"=> cashM L'.L θ τ
local notation "p!"=> paidSet (G.equip N (radiusB τ)) P₀ (Tz) σ Φ x₁ ψ₁ W₀ 1
include hO₁ F₁ hw htB hΓ hp hx hs hf hxP hzQ hN hB hL hP hW hV hY hv hC hk hy hD
lemma laurelsA (he:2 ≤ (leftE Z.val).card): Sight (X₁).support (X₁).site 2 B' x₂ H★ (valueH Z.val (caseT N₀ H' B' L'.L τ) (ψ₁) (p!)):=by
   let Rg:=trimP T O₁ δ β b
   let i:=Z.val; let pγ:= ψ₁; let x':ℝ := ∏ j∈i,p! j; let T:= caseT N₀ H' B' L'.L τ; have hp':0 < pγ:=zero_lt_one.trans_le hD; have hΨ':0 ≤ x':= prod_nonneg (fun i _=> hk.2.2.2.2.1 _); have hf':0 ≤ pγ⁻¹*x':=by positivity
   have hA : Indicia Tx B' N₀ F₁ χ E₀ g₀ (Sum.inl Z) D₁ 0 (arid τ*((pγ⁻¹)^(leftE Z.val).card*x')) 0 x₂ Ωv:= strideR L' d K H G U Γ Y A φ F' Z hF hw hp hY htB D₁ hx hs hv.le hp' hf F₁ hy -- order
   have hz':2≤ T:=caseN ..; have hpV:= (show coverNumber B'.B (X₁).support ≤ B'.B from hB.symm ▸ hy)
   obtain ⟨_,_,_,_,_,_,_,_,_,Ψ,hYn,h0⟩:=hΓ
   let n:=(leftE i).card; have hρ: (0:ℝ) ≤ (ops i).card := Nat.cast_nonneg _
   have htP:1≤ T*((ops i).card+1:ℝ):=one_le_mul_of_one_le_of_one_le (by linarith) (by linarith); have ht :0 ≤ valueH i T pγ (p!):= mul_nonneg hf' (zero_le_one.trans htP)
   change Sight (Brim.plate F₁ D₁).support (Brim.plate F₁ D₁).site _ _ _ _ _; apply grantsA (Rx:=Rg) (F':=F₁) Tx F' hO₁ rfl hL hW hP hB _ _ (sageT L' d K H G U Γ Y A φ F' Z hF hx) Ω hYn h0 hxP hzQ qc hN _ _ hv Y₂ hV hpV hA le_rfl ?_ le_rfl ht
   · simp only [Hera.lyreFee,Hera.ripple,mul_zero,zero_mul,add_zero]; change arid τ*(pγ⁻¹^n*x')*|p₁| ≤ _
     apply le_trans _ (le_mul_of_one_le_right hf' htP); calc
       _ ≤ arid τ*(pγ⁻¹^2*x')*|p₁|:=by
          have hx:pγ⁻¹^n ≤ pγ⁻¹^2:=pow_le_pow_of_le_one (inv_nonneg.mpr hp'.le) (inv_le_one_of_one_le₀ hD) he
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx hΨ') (sq_nonneg _)) (abs_nonneg _)
       _ = (arid τ*pγ⁻¹*|p₁|)*(pγ⁻¹*x'):=by ring
       _ ≤ _:=mul_le_of_le_one_left hf' hC.wood.swift
   · exact mul_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (inv_nonneg.mpr hp'.le) _) hΨ')
open QCD.Brick
variable (e:E)(hE:leftE Z.val={e})(hK:((lore (trimP T O δ β b)).activities.reg D₁).site = (P₀.row e).site) (hh:(Y.markers Z.val).Nonempty)
variable (he:Sight (P₀.row e).support (P₀.row e).site 2 O₁ x₀ (Elevator.tap (q:=q') P₀ Y e) ι')
variable (hι:ι' ≤ chip L'.L τ)
variable (hr:0 ≤ a)(hπ:x*fingers N*z≤ x₁*x₀)(hQ:∀ i,terra G N (radiusB τ) x₀ x i≤1)
variable (hS: Sea L' d (radiusB τ) η ρ z O.threshold G.Z G.V 2)(hhρ:4*((fingers N*ρ)*x) ≤ x₀/8)
include hO hr hπ hQ hι hS hhρ hE hK hh he
omit hY htB
local notation "K₁"=> ((lore (trimP T O δ β b)).activities.reg D₁)
set_option maxHeartbeats 550000 in
lemma pulseTwo (hJ:ops Z.val≠∅)(he':ι' ≤ σ e): Sight (X₁).support (X₁).site 2 B' x₂ H★ (valueH Z.val (caseT N₀ H' B' L'.L τ) (ψ₁) (p!)):=by
    let Rg:=trimP T O₁ δ β b
    let n' := deckP L'.L τ; let f₀:= fern L'.L^5; let XY:=(K₁).support; let i:=Z.val; let L:=L'.L
    obtain ⟨hh₁,hh₂⟩:=detailed Vx P₀ (sameT L' d K H G U Γ Z hF) D₁ hx hy
    have hxB:coverNumber O₁.B XY ≤ n':=by unfold XY; rw [hx, ← hO]; exact hh₁
    obtain ⟨ε,V,Q',ζ₀,ρ',hε,hR,hρ,hO,hMQ,hF0,hB',hQ',hz',heX,hρ',hA,hB0,hρV,hG',hw',hN',hX'⟩:= hC.law.purse
    let r' x := Hera.lyreFee N₀ x E₀ B' O₁ L XY (Q.halo+5) τ (gStep β); let H₀:=hC.planet
    have hb:0≤gStep β:=by unfold gStep; positivity
    have hΨ'(t)(ht':0≤t): r' t ≤ t*Hera.dueFee N₀ B' n':= Hera.tern H₀ hC.harp hC.hemp hb ht' _ hxB
    obtain ⟨f0,f1,v1,w1,w2,w3,w4,w5,w6,Ψ₀,hY,h0⟩:=hΓ
    have h'a:=he.travels; obtain ⟨h1,h2⟩:=hC.wood.dawn _ h'a hι; have hξ: 1≤ x₁:=hp.post
    have h'A: 4*(fingers N*ρ*x)≤ x₀/4:= hhρ.trans (by linarith [hp.bud]); have hf:= compassA (χ:=χ) L' d K H G U Γ Y A φ F' Z hF hw H' D₁ hx hs hv hf hp _ hE hK hh F₁ hO₁ he hr hπ hQ hy (fun U V H=> gridBeam _ (hB' f U V _ _ H) hz') hN' hX' hS h'A hP
    dsimp only at hf; simp only [if_neg hJ] at hf
    let b:= ∏ i'∈ ops i, Tz i'; let p_:= ψ₁; let x':= ∏ i'∈i,p! i'; let Z₀:=caseT N₀ H' B' L τ; let k:ℝ:=(ops i).card; let n:ℕ:= ( hooks (F:=N) (sliceL L' d) (coreW (Z') P₀ i)).card; let z' := z₀/(η/2); let D:= arid τ
    have hbk: 0 ≤ b:=prod_nonneg (fun i _=>hk.2.2.2.2.1 (.inl i)); have hv₀: 0 ≤ x':=prod_nonneg (fun i _=>hk.2.2.2.2.1 i); have hP1:0<p_:=zero_lt_one.trans_le hD; have hK0:0≤ k:=by unfold k; positivity
    have hZ': 2 ≤ Z₀:=caseN ..; let c:= ι'*b; have hc: 0 ≤ c:=by unfold c; positivity; -- indent
    have hR0:c ≤ p_⁻¹*x':=by
       have hd : x'=p_*b*(Real.exp (σ e)-1):=by unfold x' b i; rw [expensesW, invSize,hE, hF]; simp only [priceSet, hE,hF,sum_empty,Finset.card_empty, Nat.add_zero,Finset.card_singleton,pow_one,Nat.mul_zero,pow_zero,mul_one, prod_singleton,prod_empty]; ring
       rw [hd, ←mul_assoc, ←mul_assoc,inv_mul_cancel₀ hP1.ne',one_mul]; unfold c; rw [mul_comm]; apply mul_le_mul_of_nonneg_left _ hbk; linarith [Real.add_one_le_exp (σ e)]
    have htP:1≤ Z₀*(k+1):=one_le_mul_of_one_le_of_one_le (by linarith) (by linarith); have ht: 0≤ valueH i Z₀ p_ (p!):= mul_nonneg (by positivity : 0 ≤ p_⁻¹*x') (zero_le_one.trans htP)
    let V':= Hera.grandFee H'; have hV':0≤V':=sinR H'; have ht':0 ≤ D:=sq_nonneg _; have hz₂:0 ≤ z':=div_nonneg hN' (half_pos G.positive).le
    have hu:0 ≤ D*c:=mul_nonneg ht' hc; have hδ:0 ≤ (n:ℝ):=Nat.cast_nonneg _; have hx0:0 ≤ D*c*(n*(x₁*z')+k*z'):=by positivity
    have hzψ:0≤ Hera.dueFee N₀ B' n':=alert ..
    change Sight (Brim.plate F₁ D₁).support (Brim.plate F₁ D₁).site _ _ _ _ _; apply grantsA (Rx:=Rg) (F':=F₁) Tx F' hO₁ rfl hL hW hP hB _ _ (sageT L' d K H G U Γ Y A φ F' Z hF hx) Ω hY h0 hxP hzQ qc hN _ _ hv Y₂ hV (hB.symm ▸ hy) hf hu hx0 (mul_nonneg hV' hu) ht
    obtain ⟨h,hK⟩:= h2 n (Nat.cast_nonneg n) (Nat.cast_le.mpr hh₂)
    have hΓ0:f₀ ≤1:=pow_le_one₀ (fern_pos _).le (fern_one _)
    have hYn : D*c*(n*(x₁*z')+ k*z')*|p₁|+D*c*|p₂|≤ c+k*c:=by
       apply le_trans (b:=f₀*c+k*(f₀*c)) _ (add_le_add (mul_le_of_le_one_left hc hΓ0) (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hc hΓ0) hK0))
       apply le_trans _ (show _+ _ ≤ _ from add_le_add (show (D*ι'*(ι'*Real.exp ι'+n*(x₁*z'))*|p₁|+D*ι'*|p₂|)*b ≤ f₀*c from (mul_le_mul_of_nonneg_right h hbk).trans_eq (by unfold c f₀; ring)) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK hc) hK0))
       let κ' := D*c*(n*(x₁*z')+ k*z'); let u:=D*c*(ι'*Real.exp ι'); rw [show _+ k*(D*z'*|p₁| *c) = (κ'+u)*|p₁|+D*c*|p₂| from (by unfold κ' u c; ring)]
       gcongr; exact le_add_of_nonneg_right (show 0 ≤ u by unfold u; positivity)
    have hpK:= hΨ' (V'*(D*c)) (mul_nonneg hV' hu)
    apply (add_le_add hYn hpK).trans; apply le_trans _ (mul_le_mul_of_nonneg_right hR0 (zero_le_one.trans htP))
    unfold Z₀ caseT; change c+k*c+V'*(D*c)* Hera.dueFee N₀ B' n' ≤ c*((2+D*V'*Hera.dueFee N₀ B' n')*(k+1)); nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hu hV') hzψ) hK0,mul_nonneg hK0 hc]
end YM.MassiveQCD.Lyre
