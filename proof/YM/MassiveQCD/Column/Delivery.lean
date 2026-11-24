import YM.MassiveQCD.Column.Price
import YM.MassiveQCD.Column.Views
/-! # Propagating the flat spin read from the perturbed column.

This is a vacuum-sector *value* cost for the real marked principal part of the actual logarithm expansion. Only for a constant input; no arbitrary order/source-profile estimates from this calculation. Weight errors come from (i) gStep true fluctuating input against χ-gated profile (ii) large-sector scores as in `Relay ` (iii) approximate opal constant-integral on output identity. Gives **full** Sen price (all exterior) and support-radius tower cost without tying unmarked-flavor supports. -/
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
omit ht hu hQ hV
open PhysicalNext.Repeat.Cub
set_option maxHeartbeats 680000 in
lemma delivered
    (hp': ∀ V',G₁.main e0 V' =G₁.main e0 1) (hh':G₁.Reframe)
    (Y': Jets.Sun G c f H' t' u q η a d0 (pesto P₀ G H' (trunkM T₁ T₂ w 0 f)))
    (hn:5≤j) (hO' : Highlight D O R N' L (brimW Gz G₁ i) (Q.halo+5) s β (fern L^5)) (hy' : Heir.Short S R (brimW Gz G₁ i)) (hm':ops i=∅)
    (hΓ:Warp G.L (G₁.row e0).site ((sliceL G H').parent (G₁.row e0).site) (ply G H') N x y ψ ψ')(hx:fareG 1 α N≤y):
    Stew.plank (Brim.plate U l').site α ((A₁ 1).val - bill (ply G H') N (G₁.main e0 1)) ≤ 2*fern L^5*τ:=by
    let Ax:=Brim.plate U l'; let X:=(U₀).support
    let R':=(lore (trimP T R δ β B₀)); have hxB: X=brimW Gz G₁ i:=hU
    have hhS:Heir.Short S R X:=hxB.symm ▸ hy'
    have hS : S.patch.L = L:= H.laws.data.funds.length_eq; have hD: G.L=L:= (congr_arg Ratio.count hy.born).symm.trans hS
    obtain ⟨ε,V,Q',ζ₀,ρ',hε,hR,hρ,hN,hMQ,hF,hB',hQ',hz',he',hρ',hA,hB,hρV,hG',hv,hN',hX'⟩:= hh.law.purse
    have hθ:=hO ▸ hδ
    obtain ⟨f0,f1,v1,w1,w2,w3,w4,w5,w6,Ψ₀,hY,h0⟩:=hs
    have h'a:=hG.travel; obtain ⟨h1,h2⟩:=hh.wood.dawn _ h'a hτ
    let W:=G₁.main e0 1
    let Ω':= bill (ply G H') N W
    let g0:= A₁ 1
    let X':= g0.val- Ω'
    let ℒ := bias (Stew.lens (N:=N) (Ax.site)) α
    obtain ⟨F,hb,hc⟩:= Dust.commune (X:=ℒ X')
    let C:= F.comp (ℒ.restrictScalars ℝ)
    have hf:rootBill Ax.site α C:=fun i=> (F.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hb)
    let C':= lensQ Ax.site N C; let Zp:= C Ω'
    have hsite: Ax.site = (sliceL G H').parent ((M₀).site):=by
         rw [←hy.born]; exact congr_arg S.ratio.parent hW
    have h0q: 4*((fingers N*φ+ρ')*y) ≤ x/4:=by rw [add_mul]; linarith
    have hGq: 0≤q:= by obtain ⟨V,hV,hm,hH⟩:=(hk 0).1.stocks; exact (sum_nonneg (fun i _=> hV i)).trans hm
    have hΦ:= hD.symm ▸ hB hGq Y₀.stable.calf.le m hm
    have hK(k:Grid f): skimR ((1:Frame c) ∘ (sliceL G H').parent) (Spice.testG 1 C) (proton G H') (G₁.main e0) k=Zp:=by
        unfold skimR; rw [hp']; change C (Grass.changeVars (Dust.tor (Dust.ramp c 1)) Ω')=Zp -- name
        rw [show Dust.ramp c 1=Dust.pulseQ c 0 from ?_,Dust.holy]
        unfold Dust.pulseQ; apply congr_arg; ext1 i; simp
    have hX : ‖Zp‖ ≤ τ:= by
       have hz':= Spice.authored G₁ R i e0 Y₀ ha hX hG α C (hsite ▸ hf) (1:Lat.Frame c) (1:Grid f) hΓ (AnalyticBridge.VerifiedReset.flat_ok ..) hx hz
       rw [← hK (1:Grid f)]; exact hz'.2.2
    let Y0:=( (1+(Malachite.radiusD s: ℝ))^2*(Real.exp τ*τ^2)+ρ*τ)
    have htest: ‖C' g0-Zp‖ ≤ Y0*|z|+τ*|p'|+τ*fern L^5:=
        constant_hint Y hL he hp hO i' l' (grill Y G₁ hy hU) Ω hY h0 hZ hΨ p hP C' Zp hX hδ ?beam (by positivity) hhS (by omega) (show Highlight D O (trimP T R δ β B₀).p N' L X (Q.halo+5) s β (fern L^5) from hxB.symm ▸ hO') (t:=Y0)
    case beam =>
       intro F y U' S' hG V' hf' hB -- names W (frozen), X let; V'=U gauge
       rw [show C' (Y.works i' V' 1)= C (hue Gz G₁ R.threshold i V').val from congr_arg C' (hy.cash ..), ← hK V']
       apply lineage G₁ R i e0 Y₀ Y' ha (by assumption) (by assumption) hy.stops hm' hh' (by assumption) (1:Frame c) α C (hsite ▸ hf) hk (aboard Y G₁ Y₀ i l' hy U hU e0 hW hθ) hΦ hρV hρ' hv h0q hz hx V' (hxB ▸ hf') _ (by assumption) hA (by assumption) hr he' (by assumption)
       -- pose & projection
       let a:= mapcase U l' F
       have hU0:= Cub.posed N'.Z hp.rehearsed.wire (o:= Ax.site)
       have hbeamU: BeamRaw X (Lattice.gauge ((1:Lat.Frame c) ∘ S.ratio.parent) U') 1 (V * loom O (Heir.reach s) N'.C * (D.Q+N'.M+N'.M)):= printing (k:=y) (q:=χ) (d:=0) a hp (show Canvas O _ _ _ _ _ _ from hU0) hhS (by omega) (R'.activities.reg l').anchor 1  (inv_pos.mpr (Real.sqrt_pos.mpr (show 0<β from H.laws.intake.positive))).le hε hR hρ hN
       rw [show (sliceL G H').parent=S.ratio.parent from congr_arg Ratio.parent hy.born.symm]
       have hr := celia _ _ _ hB ((1:Lat.Frame c) ∘ S.ratio.parent); exact gridBeam _ (raysFort _ _ _ (hB' f _ _ (brimW Gz G₁ i) g (hxB ▸ hr)) (hB' f _ _ _ _ (hxB ▸ hbeamU))) hQ'
    change ‖ℒ X'‖ ≤ _; rw [hc]; change ‖C X'‖≤_; unfold X'; rw [map_sub]; exact htest.trans ((add_le_add_left h1 _).trans_eq (by ring)) -- name dagger
end YM.QCD.Shells
