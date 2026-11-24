import YM.Mural.Cab
/-! # Purchase identities for packed open line and propagation. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat PaletteT Ribbon Push.AbsoluteSums
variable {c f:Side} {j k N:ℕ}
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist Kites Creek Cove
open Massive Massive.PCAC
variable {I E:Type}(D:DeckV c N)(D':DeckV f N)(L: YM.Next.Free.Flight j k)(d:f.val=c.val*L.L.val)(K:KernelChoices)(r β:ℝ)(hk:L.patch.Branches K su)
variable (Z:PrintR f N Rank I E)
set_option quotPrecheck false
local notation "S'"=> (L.visit K d)
local notation "WE"=> DeckV.emblem
variable {Ic Ec:Type}(P: PrintR c N Rank Ic Ec)(C:ℂ)(Φ:Option Rank→Grid f→ Grid c→ℂ)
open QCD.Jets
local notation "sendV"=> Transfer.blockMap L K d β r hk
local notation "Ξ"=> (blankR f N)
variable {z α:ℂ}{y:ℝ}{S:Support c}
local notation "K₀"=> Keys f N
local notation "K₁"=> Keys c N
variable (W: Insertion f N)
-- Scalar weight in messages fixed per step.
variable (hw:∀ V, W V= α • D'.density V)
variable (x y:Site c)(p q:Site f)
local notation "ℒ"=> loaded p q L d x y
local notation "Cq"=> cleared p q L d x y
local notation "T!"=>texel L d 0 x p
local notation "U!"=>texel L d 0 y q
local notation "δp"=> (shadeM L d x y p q z)
local notation "J"=> arctic L.L j
local notation "σ"=> berthD j
local notation "un"=> (x,y)
local notation "δx"=> ((L.visit K d).ratio)
-- packed rates.Sem issued by canopy on all sectors.
variable (pα t:ℝ)
local notation "S₀"=> ({(L.visit K d).ratio.embed x}: Support f)
variable (B0 B1:ℕ) (v p₀ b0 height s w v₀ v₁ w₁ v₂ ξ Δ ζ:ℝ)
structure Boast (D:DeckV f N)(F :Rank→ Insertion f N)(x y:Site f)(P:Support f)(a t p k v w height:ℝ)(α:ℂ) :Prop where
    expo : ∃ (I E: Type)(_ :Countable I)(_ :Countable E)(Z: PrintR f N Rank I E),
      Z.Fides (fun _=>x) P D.O (fieldD x y) ∧ Z.Levy D.O a t p k v w height ∧∀ i U,F i U=α • WE D Z (.some i) sD U
-- form chamber parameter. normalize δx.Clock.Huts any. 
local notation "Λ"=> texel L d
noncomputable def ascend (F:Rank→Insertion f N)(i:Rank): Insertion f N:=⟨fun U=>∑ j:Rank,doll (T! U) (U! U) i j • (F j U),by unfold doll; refine continuous_finsetSum _ fun i _=>?_ ; fun_prop ⟩ -- tot requires normedCommRing! V=Fields noncomm ring.Our tot issue. define direct field sum fresh.
local notation "dλ"=> (texel L d 0 x p)
local notation "dμ"=> (texel L d 0 y q)
-- voucher `Wind` decoupled from queues. Supports. to allow post budgets `P` threshold gap smoothing.C.H
variable (kα Q' A:ℝ) (B:ℕ)
local notation "TAG"=>({(sliceL L d).embed x}: Support f)
local notation "SE"=> (halo B0 {p})
local notation "F!"=> (halo B1 {x})
variable (z)
structure Ark (w':ℝ) :Prop where
    store : ∀ (I' E':Type)[Countable I'][Countable E'] (Z0:PrintR f N Rank I' E'), PrintR.Fides Z0 (fun _=> (sliceL L d).embed x) ({(sliceL L d).embed x}) D'.O (fun g=> fieldD x y (g ∘ (sliceL L d).embed)) → PrintR.Levy Z0 D'.O v pα b0 b0 height s w → ∀ r':ℂ, ‖r'‖≤ w' →
       ∃ (I E:Type)(_ :Countable I)(_ :Countable E)(Z₁:PrintR c N Rank I E), PrintR.Fides Z₁ (fun _=>x) (halo B1 {x}) D.O (fieldD x y) ∧ PrintR.Levy Z₁ D.O v p₀ kα A Δ w₁ v₁ ∧ Strike D D' L d K r β Z0 Z₁ C (shadeM L d x y p q r')
-- prices. matching t from ledge, support PSk. note countable fossils. We re-anchor coordinates.
variable {wp height' δ:ℝ}
variable (hx: Ark D D' L d K r β C x y p q pα B1 v p₀ b0 height s w v₁ w₁ Δ kα A wp) -- order
variable (hf:∀ i,Summable fun j=> ‖D'.K.warp j i‖)(hV:∀ i,Summable fun j=> ‖D.K.warp j i‖)
variable (hb:1 ≤ v) (hq:1≤pα)(hVK:0≤height)(hl:1 ≤ s)(ht:0 ≤ w)(hB:0≤b0)
variable (hα:1 ≤p₀)(hkα:0 ≤ kα)(hzS:1 ≤w₁)(hA:0 ≤ A) (hR:0 ≤ wp)
local notation "Oq"=> D.emblem
include hf hV hw ht hb hVK hx hl hk hα hA hkα hzS hB hq hR
lemma aligner :∀ U,(sendV W) U= (α*C) • D.density U:=by
    obtain ⟨I,E,hI,hE,Z,hP,hF,hS⟩:=hx.store PEmpty PEmpty Ξ (blank_fides ..) (blank_lev (B1:=0) D'.O hVK ht ..) 0 (by simpa) -- order tweak
    let T:= (sliceL L d).embed x; have hv: (Ξ).Levy D'.O v pα b0 b0 height s w:= by exact blank_lev (B1:=0) D'.O hVK ht N f
    have hΞ:(Ξ).Fides (fun _=> T) ({T}) D'.O (fieldD T T):= blank_fides ..; exact plainLoad D D' L d K r β hk Ξ Z C _ W _ rfl hw hS none (fun U=>tiltP Ξ D' _ _ _ hΞ hf hv hb hq hB hB hl U none) (fun U=>tiltP Z D _ _ _ hP hV hF hb hα hA hkα hzS U none)
omit hV hR hα hA hkα hzS
noncomputable def rebirth (z:ℂ)(i:Rank): Insertion c N:= z • (sendV (scaleLoad W ℒ i (loaded_c ..))- scaleLoad (sendV W) Cq i (cleared_c ..))
lemma stocks (hr: ‖z‖≤ wp) : Boast D (rebirth L d K r β hk W x y p q z) x y (halo B1 {x}) v p₀ kα A Δ w₁ v₁ (α*C):=by
    have hp : (Ξ).Fides (fun _=> (sliceL L d).embed x) TAG D'.O (fun g=> fieldD x y (g ∘ (sliceL L d).embed)) := blank_fides ..; have hD : (Ξ).Levy D'.O v pα b0 b0 height s w:= blank_lev (B1:=0) D'.O hVK ht N f -- fix
    obtain ⟨I,E,hI,hE,Z,hP,hF,hS⟩:=hx.store PEmpty PEmpty Ξ hp hD z hr
    refine ⟨_,_,hI,hE,Z,hP,hF,fun i V=>?_⟩; rw [mul_smul]; exact pioneer D D' L d K r β hk Z C W hw x y p q hS (fun i U=>tiltP Ξ D' _ _ _ hp hf hD hb hq hB hB hl U i) hf i V
omit hVK ht hw
-- from old bounty.Currency p.T.Transfer.Proponent K. hStamp root p and old footprint.Carded.Mon. 
local notation "src"=> (halo D'.O.B {p})
local notation "gC"=> Fintype.card Rank
variable {e e' d' u' δ':ℝ}(Hq: pα=pα)(h0:2*L.patch.radius<f.val)(hp:separation ((L.visit K d).ratio.embed x) p≤arctic L.L j) (hp':separation ((L.visit K d).ratio.embed y) q ≤arctic L.L j) (hz:separation p q≤berthD j)
include hx h0 hp hp' hz hR
set_option maxHeartbeats 440000 in
lemma conveys (H:Rank→Insertion f N)(HR: Boast D' H p q src v pα e e' d' u' δ' α)(he:b0 ≤e)(hw:b0 ≤e')(hh: s ≤ u') (heB:2*J+σ ≤ D'.O.B)
   (z:ℂ)(Wi V:ℝ)(hW:∀ X:Mat,∀ i j:Hue,‖X i j‖≤ Wi*‖X‖)(hX:0≤Wi)(hΞ:‖z‖*(Wi*(Kit.scale L.L))^2≤ V)(hv:gC*(V*d')≤height)(hy:gC*(V*δ')≤ w) :
   Boast D (fun i=> z • sendV (ascend L d x y p q H i)) x y F! v p₀ kα A Δ w₁ v₁ (α*C):=by
    obtain ⟨I,E,hI,hE,Z,hP,hZ,hΩ⟩:= HR.expo -- ? HR structure vs prop. adjust constructors
    let Z':= trestle Z (T!) (U!) z; let Wc:= fun _ :Unit=> (sliceL L d).embed x; let F:= fieldD x y
    have hV: Z'.Fides Wc TAG D'.O (fun g=>fieldD x y (g∘ (sliceL L d).embed)):= stint L d x y p q hp hp' hz Z src (fun _=>p) z hP 0 (Subset.refl _) heB -- arg types
    have ht(i j):= hΩ i j; have hk' (U:Grid f)(i j):‖z‖*‖doll (T! U) (U! U) i j‖≤ V:=by
         unfold doll; rw[norm_mul]; apply le_trans _ hΞ; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [pow_two]; exact mul_le_mul ((hW ..).trans (mul_le_mul_of_nonneg_left (entryL L d 0 _ _ _ h0) hX)) ((hW ..).trans (mul_le_mul_of_nonneg_left ((norm_star _).le.trans (entryL L d 0 y q U h0)) hX)) (norm_nonneg _) (mul_nonneg hX (Kit.scale_pos _).le)
    have H₀: Z'.Levy D'.O v pα b0 b0 height s w:=grant_high Z' D' (esteem Z (T!) (U!) z D'.O e V e' pα u' d' δ' v hZ hk' s (zero_le_one.trans hl) hh b0 b0 he hw) hv hy
    have hc:∀ i V,(ascend L d x y p q H i) V=(∑ j:Rank,doll (T! V) (U! V) i j • (α • D'.emblem Z (some j) sD V)):=by intro i V; change (∑ j:Rank,doll (T! V) (U! V) i j • (H j V)) =_; apply sum_congr rfl; intro j _; exact congr_arg _ (ht j V)
    obtain ⟨I₁,E₁,hI,hE,P,hP₁,hZ₁,h₁⟩:=hx.store I E Z' hV (by exact H₀) 0 (by simpa) -- replace Z' 
    refine ⟨_,_,hI,hE,P,hP₁,hZ₁,fun i V'=>?_⟩
    have he(Y:Grid f): z • (ascend L d x y p q H i) Y=α • WE D' Z' (some i) sD Y:=by
         rw [hc]
         have hp0:= billP Z Y _ pα v e e' d' u' δ' hZ hq (hl.trans hh) hb (hB.trans he) (hB.trans hw); have hg:= billP Z' Y _ pα v b0 b0 height s w H₀ hq hl hb hB hB
         rw [show WE D' Z' (some i) sD Y=_ from stanzas Z T! U! z Y _ _ _ _ _ _ (hf _) hP (fun i=>(hp0 i).1) (fun i=>(hp0 i).2) (fun i=>(hg i).1) (fun i=>(hg i).2) i]; rw [smul_comm α]; apply congr_arg (z • ·); rw [Finset.smul_sum]; exact sum_congr rfl fun j _=> smul_comm ..
    have hV' := h₁.roll (some i) V' sD; simp only [ite_true, shadeM,zero_mul,zero_smul,add_zero] at hV'
    let Tz(V:Grid f):= Kit.sheath 1 (ater L d V) (WE D' Z' (some i) sD V)
    change z • (sendV (ascend L d x y p q H i) V')= (α*C) • _; rw [← paintD L d K, extendT L d K r β hk _ (fun V=> α • Tz V) ?_]; swap; · intro V; change Kit.sheath 1 (ater L d V) (z • _)=_; rw [he]; exact congr_fun (Transfer.soften_smul L d (fun _=> _) α) V
    let P':= engine r K₁
    rw [show ((S').push β (fun V=> α • Tz V) V')= α • ((S').push β Tz V') from ?_,map_smul, mul_smul]; · exact congr_arg _ hV'
    unfold StepData.push; simp_rw [smul_comm _ α]; exact integral_smul ..
end YM.QCD.Comet
#print axioms YM.QCD.Comet.conveys
#print axioms YM.QCD.Comet.stocks
