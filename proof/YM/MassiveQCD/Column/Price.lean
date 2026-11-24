import YM.QCD.Purse.Farm
import YM.MassiveQCD.Column.Sector
import YM.MassiveQCD.Charter.Paint
/-! # Purchased homogeneous linear classification (Lin & other charges).
 uses Choker hull no fake neighboring flag reads. push outputs ticket on `Brim` masks only.
 The final Woven turn must pay if supports change, etc. This phase is used before projecting
 onto the mass primaries. -/
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
-- field-economies agile any H supportExponent; τ positive. Bulk/Rush in later ledger. This snapshot number.D. allows auxiliary quantities. E use G.F.
variable {E J: Type}[Countable E][Countable J]{d0 N₂ W₂ :ℕ}
variable {G:Flight n k}{H':f.val=c.val*G.L.val} (G₁:Rise f N E J) {i:Finset (Fj (Tr f) E J)} {a₀ a₁ b₀ b₁ m ξ g w' θ K α φ: ℝ}
variable {P₀ : Plan n}{T₁: Garden.Offer 1 a₀ a₁}{T₂: Garden.Offer 2 b₀ b₁}
variable (Y₀: Jets.Sun G c f H' t' u q η a d0 (pesto P₀ G H' (trunkM T₁ T₂ w m f)))
variable (Y': Jets.Sun G c f H' t' u q η a d0 (pesto P₀ G H' (trunkM T₁ T₂ w 0 f)))
variable {i':ι}{D:Heir.Record} (U: Cash W s μ L Q o C T (lore (trimP T R δ β B₀)))
local notation "ζ"=> radiusB s
set_option quotPrecheck false
local notation "Gz"=> Y₀.equip N (radiusB s)
variable {z p' α' τ ψ' χ₀ ρ x X Y₁:ℝ}
variable (Z: Hera.Rights su j)
variable (hL:Works P L s S T)(hO:O.B=radiusB s)(he:News P L s W Q o μ C j N' D χ O.power z p' g S.patch) (hp:Plays N' D O R P T s)
variable (Ω:Clusters Y.Bright → RegularAddress c)
variable (f':Flavor N) (β':E→ℝ)(κ:J→ℝ)
local notation "Jz"=> Lute.Plented N' D O R L (Q.halo+5) s (gStep β)
local notation "μ₀"=> fun i=>Real.exp 1*terra Y₀ N ζ x y i
local notation "ψ₁"=> cashM L θ s
variable {f'' : Flavor N}{ρ₀ e e' ψ σ α₂ Y₂ :ℝ}{p: Y.Bright}
variable (hy: Tone Y (Y₀.equip N (radiusB s)) G₁ i i')
variable (hh:Coins O R P L D Q.halo N' Z s β x y t' u η σ q a u z g ρ m p' ξ x θ P₀ N d0)
variable (hm:|m| ≤haloK L s)(ha: Peak (Y₀.equip N (radiusB s)) R.threshold x y ξ fun i=>Real.exp 1*terra Y₀ N (radiusB s) x y i)(hk:Sea G H' (radiusB s) t' φ q R.threshold Y₀.Z Y₀.V 2)(hK:0 ≤ φ)(hj:4*(fingers N*φ*y) ≤ x/8)(hu:y*fingers N*q ≤ ξ*x)(hQ:∀ i,terra Y₀ N (radiusB s) x y i ≤1)
variable (hf:G₁.Wave R.threshold) (hC:G₁.Reframe)(hr:0<η)
variable (hs:Seats H χ)(hP:Aliased Y p i') (hZ:Y.Famous)(hΨ:Colored Y)
variable (l':ℕ) (ht:α≤ y)(hz:0<α)(h'h:fareG 1 α N ≤ y)
local notation "U₀"=> ((lore (trimP T R δ β B₀)).activities.reg l')
local notation "A₀"=> Brim.plate U l'
variable (hU:( (lore (trimP T R δ β B₀)).activities.reg l').support=brimW (Y₀.equip N (radiusB s)) G₁ i)(hδ:coverNumber O.B (Brim.plate U l').support ≤ O.B)
local notation "A₁"=> ((crude Y χ Ω).view (individual p))
variable (hV: Woven (Brim.plate U l').site (Y.fullA p.val) O α ((crude Y χ Ω).view (individual p)) Y₂)
-- pricing principal. no Height test from Obr.Record eventually.
variable (e0:E)(hX:leftE i={e0})(hW:((lore (trimP T R δ β B₀)).activities.reg l').site=(G₁.row e0).site) (hG: Spice.Worth G₁ e0 R x τ) (hτ: τ ≤ chip L s)
local notation "M₀"=> G₁.row e0
local notation "n₀"=> coverNumber R.B (brimW (Y₀.equip N ζ) G₁ i)
include hL hO hp he hm ha hk hK hy hu hQ hj hf hΨ hr hs hP hZ hh hU hδ hV ht hz hX hW hG hτ
set_option maxHeartbeats 650000 in
lemma fair_temper (hm':ops i=∅)(hj':5≤j)(hΓ:Warp G.L (G₁.row e0).site ((sliceL G H').parent (G₁.row e0).site) (ply G H') N x y ψ ψ'){gain:Bool}(hI:Nonwrapping (M₀).support (M₀).site→Temper R (M₀).support (M₀).site gain (G₁.main e0) x τ)(hx:fareG 1 α N≤y)(hh': G₁.Reframe)(Y': Jets.Sun G c f H' t' u q η a d0 (pesto P₀ G H' (trunkM T₁ T₂ w 0 f))): Woven (A₀).site (A₀).support O α A₁ ((rampFee gain L)*(fern L^5*τ*fluteT N' Z O ψ' n₀)):=by
    let n' := n₀; let f₀:= fern L^5; let X:=(U₀).support; have hxB:coverNumber R.B X=n':=congr_arg (coverNumber R.B) hU
    have hS : S.patch.L = L:= H.laws.data.funds.length_eq; have hD: G.L=L:= (congr_arg Ratio.count hy.born).symm.trans hS
    obtain ⟨ε,V,Q',ζ₀,ρ',hε,hR,hρ,hN,hMQ,hF,hB',hQ',hz',he',hρ',hA,hB,hρV,hG',hv,hN',hX'⟩:= hh.law.purse
    have hθ:=hO ▸ hδ; have ht:R.B ≤ 2*radiusB s:= hh.harp
    let r' x := Hera.lyreFee N' x D O R L X (Q.halo+5) s (gStep β); let H₀:=hh.planet
    have hb:0≤gStep β:=by unfold gStep; positivity
    have hΨ'(t)(ht':0≤t): r' t ≤ t*Hera.dueFee N' O n':= Hera.tern H₀ ht hh.hemp hb ht' _ hxB.le
    obtain ⟨f0,f1,v1,w1,w2,w3,w4,w5,w6,Ψ₀,hY,h0⟩:=hs
    have h'a:=hG.travel; obtain ⟨h1,h2⟩:=hh.wood.dawn _ h'a hτ
    have hV2:= alertF N' Z O ψ' n'; have heE := alert N' O n'; let A:=1+(n':ℝ); have hN0:1 ≤ A^15:=one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
    have hV':0 ≤ f₀*τ*fluteT N' Z O ψ' n':=by have he:=hV2.2; positivity [fern_pos L]
    have hB0 := f₀; let y₀:=f₀*τ -- edit have real no type?
    have hp₀:1 ≤ rampFee gain L:=(rampFee_gate L gain).1.trans (rampFee_gate L gain).2
    by_cases hz₀ : Heir.Short S R (brimW Gz G₁ i)
    · have hQ0: 4*((fingers N*φ+ρ')*y) ≤ x/4:=by rw [add_mul]; linarith
      have hG: 0 ≤ q:=by obtain ⟨V,hV,hm,hH⟩:=(hk 0).1.stocks; exact (sum_nonneg (fun i _=> hV i)).trans hm
      have H' :=transmit (χ:=χ) Y G₁ Y₀ Y' i l' hy U hU _ hX hW Z D hp g ha hf hk hθ hN' hX' hz hx hΓ hρV hQ0 hv hK hρ' (hD.symm ▸ hB hG Y₀.stable.calf.le m hm) hA he' hr hj' hI hz₀ hm' hh' ε V Q' hε hR hMQ (hS.symm ▸ hF) hN hρ (hB' f) hQ'
      let B:= carryFee N' Z ψ'; have hΨψ := cin N' Z ψ'
      apply fundsL_colored Y hL he hp hO i' l' (grill Y G₁ hy hU) Ω hY h0 hZ hΨ p hP Y₂ hV hδ H' h'a (by positivity) (by rw [hD]; positivity [fern_pos L]) (mul_nonneg (zero_le_one.trans hp₀) hV')
      · change _+ r' (B*(τ*rampFee gain G.L)*fern G.L^5) ≤ _; rw [hD]; have hV₃: B*Hera.dueFee N' O n' ≤ max (carryFee N' Z ψ') (Hera.grandFee Z)*Hera.dueFee N' O n'*A^15:=by
         apply le_trans (b:=B*_*A^15) (le_mul_of_one_le_right (mul_nonneg hΨψ heE) hN0); gcongr; exact le_max_left ..
        let V:= rampFee gain L
        apply (add_le_add (h1.trans (le_mul_of_one_le_left (mul_nonneg (pow_nonneg (fern_pos _).le _) h'a) hp₀)) (hΨ' _ (by positivity [fern_pos L]))).trans
        have he : 1+B*Hera.dueFee N' O n' ≤ fluteT N' Z O ψ' n':= (add_le_add (by norm_num : (1:ℝ) ≤2) hV₃).trans hV2.1
        change V*_+(B*(_*V)*_)*_ ≤ V*_
        rw [show V*_+_ = V*(f₀*τ)*(1+B*Hera.dueFee N' O n') from by unfold f₀; ring]; exact (mul_le_mul_of_nonneg_left he (by unfold f₀ V; positivity [fern_pos L])).trans_eq (by unfold f₀; ring)
    have hzB: L.val ≤ n'^3:=hS ▸ le_of_not_gt hz₀
    have h'A: 4*(fingers N*φ*y)≤ x/4:= hj.trans (by linarith [ha.bud]); have hf:= islands χ Y G₁ Y₀ i l' hy U hU _ hX hW Z D hp g ha hr.le hf hu hQ hk h'A hθ (fun U V H=> gridBeam _ (hB' f U V _ _ H) hz') hN' hX' hG hz (by assumption)
    dsimp only at hf; simp only [hm',prod_empty,mul_one,if_true, Finset.card_empty,Nat.cast_zero,zero_mul,add_zero] at hf
    let n:ℕ:=(hooks (F:=N) (sliceL G H') (coreW Gz G₁ i)).card; let D':=Hera.grandFee Z; let z0:=σ/(t'/2); have heψ:=sinR Z
    have hξ : 1≤ ξ:=ha.post; have hz' : 0 ≤ z0 :=by unfold z0; positivity [Y₀.positive]
    apply Woven.stretches (A:=_) ?preFx (Subset.refl _) (le_mul_of_one_le_left hV' hp₀)
    apply fundsL_colored Y hL he hp hO i' l' (grill Y G₁ hy hU) Ω hY h0 hZ hΨ p hP Y₂ hV hδ hf h'a (by positivity [Y₀.positive]) (mul_nonneg heψ h'a) hV'
    have hf₀: arid s*τ*(τ*Real.exp τ + (n:ℝ)*(ξ*z0))*|z|+τ*|p'| ≤ y₀:=by
       have hx := (h2 n (Nat.cast_nonneg n) (Nat.cast_le.mpr (detailed Y G₁ hy l' hU hθ).2)).1; apply le_trans _ hx; gcongr; apply le_mul_of_one_le_left h'a; exact one_le_pow₀ (by linarith only [show 0≤(Malachite.radiusD s:ℝ) from Nat.cast_nonneg _])
    apply (add_le_add hf₀ (Hera.wide H₀ hh.harp hh.hemp hb (mul_nonneg heψ h'a) n' hxB.le hzB)).trans; change y₀+ D'*τ * _ * _ * f₀≤_
    rw [show y₀+ _ = y₀ * (1+D'*Hera.dueFee N' O n'*A^15) by unfold y₀ n' f₀ D' A; ring] -- check A unfold
    apply mul_le_mul_of_nonneg_left _ (by unfold y₀; positivity [fern_pos L]); apply le_trans _ hV2.1; apply add_le_add (by norm_num : (1:ℝ)≤2); gcongr; exact le_max_right ..
end YM.QCD.Shells
