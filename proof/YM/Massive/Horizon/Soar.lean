import YM.Massive.Horizon.Flat
import YM.Massive.Horizon.Wind
import YM.Massive.Horizon.Sign
/-! Step width and price of the principal regular output under the collar/grade3 condition. -/
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
variable (f':Bool) (β':E→ℝ)(κ:J→ℝ)
local notation "Jz"=> Lute.Plented N' D O R L (Q.halo+5) s (gStep β)
local notation "μ₀"=> fun i=>Real.exp 1*terra Y₀ N ζ x y i
local notation "ψ₁"=> cashM L θ s
variable {f'' : Flavor N}{ρ₀ e e' ψ σ α₂ Y₂ :ℝ}{p: Y.Bright}
variable (hy: Tone Y (Y₀.equip N (radiusB s)) G₁ i i')
variable (hh:Coins O R P L D Q.halo N' Z s β x y t' u η σ q a u z g ρ m p' ξ x θ P₀ N d0)
variable (hm:|m| ≤haloK L s)(ha: Peak (Y₀.equip N (radiusB s)) R.threshold x y ξ fun i=>Real.exp 1*terra Y₀ N (radiusB s) x y i)(hk:Sea G H' (radiusB s) t' φ q R.threshold Y₀.Z Y₀.V 2)(hK:0 ≤ φ)(hj:4*(fingers N*φ*y) ≤ x/8)(hu:y*fingers N*q ≤ ξ*x)(hQ:∀ i,terra Y₀ N (radiusB s) x y i ≤1)
variable (hf:G₁.Wave R.threshold) (hC:G₁.Reframe)(hr:0<η)
variable (hs:Seats H χ)(hP:Aliased Y p i') (hZ:Y.Famous)(hΨ:Stained.Framed Y)
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
include hL hO hp he hm ha hk hK hy hu hQ hj hf hΨ hr hs hP hZ hh hU hδ ht hz hX hW hG hτ -- hV unused cut. remove more
local notation "X0"=>((lore (trimP T R δ β B₀)).activities.reg l')
local notation "γ6"=> Cub.opal N' D O R L (X0).support (Q.halo+5) s (gStep β)
local notation "γ7"=> AnalyticBridge.LocalGaussian.Moments.meter (Lute.heads su R L (X0).support (Q.halo+5) s) 0 D.K (2*((j+1)+(j+1)))
-- for pure constant on full label at this hyp. adapt Ethos.sonnet witness.
omit hu hQ ht ha -- need ha for lineage etc. yes
include ha
set_option maxHeartbeats 780000 in
lemma soar (hm':ops i=∅)(hj':5≤j)(hΓ:Warp G.L (G₁.row e0).site ((sliceL G H').parent (G₁.row e0).site) (ply G H') N x y ψ ψ') (hx:fareG 1 α N≤y)(hh': G₁.Reframe)(Y': Jets.Sun G c f H' t' u q η a d0 (pesto P₀ G H' (trunkM T₁ T₂ w 0 f)))(hθ:γ6 ≤ 1)(hM:Cub.clocks N' 1*γ6*γ7 ≤ fern L^5) (Z₀:Crate c N→L[ℝ]ℝ) (hRz: rootBill (A₀).site α Z₀) (hG₁:Heir.Short S R (X0).support)(hmL:∀ i,G₁.main e0 i=G₁.main e0 1):
    ‖Z₀ (A₁ 1).val - Z₀ (bill (proton G H') N (G₁.main e0 1))‖ ≤2*(fern L^5*τ) :=by
    let P:= ((G₁.row e0).site)
    let n':= n₀; let f₀:= fern L^5; let K:=(U₀).support; have hxB:coverNumber R.B K=n':=congr_arg (coverNumber R.B) hU
    have hS : S.patch.L = L:= H.laws.data.funds.length_eq; have hD: G.L=L:= (congr_arg Ratio.count hy.born).symm.trans hS
    obtain ⟨ε,V,Q',ζ₀,ρ',hε,hR,hρ,hN,hMQ,hF,hB',hQ',hz',he',hρ',hA,hB,hρV,hG',hv,hN',hX'⟩:= hh.law.purse
    have ht:= hO ▸ hδ
    let R0:=(trimP T R δ β B₀); let p₁:= X0; let X:= p₁.support
    obtain ⟨f0,f1,v1,w1,w2,w3,w4,w5,w6,Ψ₀,hY,h0⟩:=hs
    have h'a:=hG.travel; obtain ⟨h1,h2⟩:=hh.wood.dawn _ h'a hτ
    have hKr :rootBill ((sliceL G H').parent P) α Z₀:= by rw [←hy.born,← show p₁.site=P from hW]; exact hRz
    have hQ0:4*((fingers N*φ+ρ')*y) ≤ x/4:=by rw [add_mul]; linarith
    have hD3: 0 ≤ q:=by obtain ⟨V,hV,hm,hH⟩:=(hk 0).1.stocks; exact (sum_nonneg (fun i _=> hV i)).trans hm
    let t₀:=(fun i: Site c=>(1:su.El)); let Zp:= skimR ((1:Site c→su.El) ∘ (sliceL G H').parent) (testG 1 Z₀) (proton G H') (G₁.main e0) -- constant assertion
    let B₂:=Z₀ (bill (proton G H') N (G₁.main e0 1)); have hJ t : Zp t=B₂:=by
       unfold Zp skimR; rw [hmL]; change Z₀ (Grass.changeVars (tor (Dust.ramp c 1)) _) = B₂
       rw [show Dust.ramp c 1=pulseQ c 0 from ?_,Dust.holy]
       unfold pulseQ; apply congr_arg; funext i; simp
    let U₀':=lensQ (A₀).site N Z₀; let z:ℝ:= arid s*(Real.exp τ*τ^2)+ρ*τ -- verify V from Tender q0 is? hρV rhs V? notes Room.dawn A=ρ. compare
    have hzB: ‖B₂‖≤τ:= (hJ 1) ▸ (authored G₁ R i e0 Y₀ ha hX hG α Z₀ hKr 1 1 hΓ (AnalyticBridge.VerifiedReset.flat_ok ..) hx hz).2.2
    have hT:=flatFunds (t:=z) (χ:=χ) Y hL he hp hO i' l' (grill _ G₁ hy hU) Ω hY h0 hZ hΨ p hP (by omega) U₀' B₂ hzB hδ hG₁ hθ hM (by unfold z arid;positivity) (fun F y0 hz₁ hp' Z' hU0 HX=>?_)
    · exact hT.trans ((add_le_add (h1) (le_refl _)).trans_eq (two_mul _).symm)
    let g':=(1:Site c→su.El) ∘ S.ratio.parent; let P'':=mapcase U l' F; let v:= homeQ F U χ (1:Grid c) l' y0 D
    have hq:0<gStep β := inv_pos.mpr (Real.sqrt_pos.mpr (U.laws.intake.positive))
    have hg: PhysicalNext.JointLoad.Heir.Canvas O (S.ratio.parent p₁.site) (Heir.reach s) 1 (1:Site c→su.El) j N'.C:= Cub.posed N'.Z hp.rehearsed.wire -- Namespace verify
    let D₂:=D.Q+N'.M+N'.M
    let K:=Heir.loom O (Heir.reach s) N'.C; let p3:= V*K*D₂
    have hb₀ : BeamRaw (brimW Gz G₁ i) (Lattice.gauge g' v) 1 p3 := hU ▸ printing (k:=y0) (q:=χ) (d:=0) P'' hp hg hG₁ (by omega) p₁.anchor (1:Grid f) hq.le hε hR hρ hN
    rw [←hJ Z']; change ‖Z₀ (Y.works i' Z' _).val-Zp Z'‖≤ z; rw [hy.cash]
    have hM:= lineage G₁ R i e0 Y₀ Y' ha hf hX hy.stops hm' hh' hG 1 α Z₀ hKr hk (aboard Y G₁ Y₀ i l' hy U hU e0 hW ht) (hD.symm ▸ hB hD3 Y₀.stable.calf.le m hm) hρV hρ' hv hQ0 hz hx Z' (hU ▸ hU0) ?_ hX' hA hN' hr he' hK
    · exact hM
    have hqg : g'= (1:Site c→su.El) ∘ (sliceL G H').parent:= congr_arg (fun t:Ratio c f=> _ ∘ t.parent) hy.born
    rw [←hqg]
    have hM:= raysFort _ _ _ (hB' _ _ _ _ _ (celia _ _ _ (hU ▸ HX) g')) (hB' _ _ _ _ _ hb₀)
    exact fun i a b=> (hM i a b).trans hQ'
end YM.QCD.Shells
#print axioms YM.QCD.Shells.soar
