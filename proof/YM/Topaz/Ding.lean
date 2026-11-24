import YM.Topaz.Meter
import YM.Intag.Recode
import YM.HONE.Crude
import YM.Topaz.Premi
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Tarot
open Pilgrim Tess Hymnal MassiveQCD.Inky YM.Bloom QCD.Bera Massive.UV YM.Arise YM.Arise.Bill YM.Arise.Count YM.Arise.Range Arise.Parcel
open YM.Eden QCD.Lat Massive.Evo MassiveQCD MassiveQCD.TimesV UV UV.Free QCD.Grass QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
open Sample Quills Quills.Eden Cupola Ribbon Quills.Clover
open Massive.Elm.SparK.Arbor Massive.Elm.SparK.Arbor.Gallery
open QCD.Plum QCD.RP QCD.Cove QCD.Creek QCD.Bloom Metric Laurent Precision Bloch Exterior
open Column Massive.Evo
variable {S:Scheme}{R:Side}{i j k p N:ℕ}(A: Massive.Run S N R 6) {f l:Side}{D:ℕ}
namespace Vista
open YM.Bloom.Jar YM.Bank YM.Bank.Jule
open QCD.Acre.Stratum.MarchQ.Suburb.Sapphire
variable (R0:Vista (S.side R i) D) {I:Type} [Fintype I](P:I→ Glyph D)(x:I → Cover)(L:List I)
local notation "E"=> S.side R i
local notation "πt"=> S.side R p
variable (hv:p ≤ i) (he:i ≤ N) (ho:Even R.val) (sy:RawSym) (z:Site (S.side R i))(p₀:Site (S.side R p))
local notation "Hp"=> evenW S R ho p
local notation "Θ"=> mural (viewW S R hv) Hp z
local notation "S0"=> Column.sky S R p N (hv.trans he) Hp z
variable (Ωs: Finset (Glyph D))(X Mq U lℓ j₀ b:ℕ)(r ε Y Xv qv G:ℝ)
set_option quotPrecheck false
local notation "WU"=> Hymnal.jogs sy Ωs
-- Authentic payout end. no more calendar.Screen.New abstract Prop one Tile.Use.L marks.Update.
structure AspectA :Prop where
   costs : Vista.Credential A R0 he (Hymnal.jogs sy Ωs) X p lℓ Mq b j₀ r ε Y Xv qv true
   rental :1≤ qv ∧ Xv ≤ qv*G ∧ 0 ≤ G ∧ 0 ≤ Xv
   source : R0.r+1+50*(S.J i+10) ≤ X
   lease : p≤ j₀ ∧ j₀ ≤ i
   angular: U*(X+Mq*Mq +1) ≤ratioTo S j₀ p
   span:2*(Y*r^b)<((S.side R i).val:ℝ)
   extent:Y*r^b ≤ (ratioTo S i j₀:ℝ)
   tail : (4:ℝ)*X< ε*r^b
   positivity:0<r∧0 < ε ∧0<U
structure AspectB :Prop where
   costs: Vista.Credential A R0 he (Hymnal.jogs sy Ωs) X p lℓ Mq b j₀ r ε Y Xv qv false
   rental :0<qv ∧ Xv≤qv*G∧0 ≤G∧0 ≤Xv
   source :R0.r+1+50*(S.J i+10) ≤ X
   lease : p≤ j₀∧ j₀ ≤ i
   angular: U*(X+Mq*Mq+1) ≤ ratioTo S j₀ p
   positivity:1 ≤ lℓ∧0<ε ∧0<U
#print AspectA
set_option maxHeartbeats 800000 in
lemma ding (hp:AspectA A R0 he sy Ωs X Mq U lℓ j₀ b r ε Y Xv qv G (p:=p)) (hvI:0<Fintype.card I)(hξ:Fintype.card I ≤lℓ)(hF:∀ j,P j∈Ωs)(hZ:L.Nodup)(ht:∀ i,i∈L)(hx:∀ j,wrap (S.side R i) (x j) ∈ (Θ).margin p₀ (marginM S U p i)) (hJ:∀ u v:I,u≠v→ posT r b (x u) - posT r b (x v) ∈ Oasis ε Y): let t := ProbeWords P L ((posT r b) ∘ x) (fun i'=>Vista.leaf (i:=i) A R0 (P i') (x i')) (Vista.polLeaf A R0 P x he); Fence ((S0).chamber p₀) t ∧ Potion t ∧ topH S0 A.regulator t p₀ ≤ G :=by
      -- aperture.Use. j0 binders. Hero.Tartar.Ar.V.Pre
      obtain ⟨hP,⟨h1,h2,h3,h4⟩,hY,⟨hL,hM⟩,hU,h'₁,h'₂,h'₃,hη,hq,hZ'⟩:= hp -- flatten?
      intro t; have h:= Vista.canopy x b r ε Y hη hJ hv z ho p₀ L U Mq X lℓ hZ' hL hM hU hZ ht hξ hq h'₁ h'₂ h'₃ hx -- arity
      let k:= Fintype.card (Site (S.side R p)); have hp:0<qv:= zero_lt_one.trans_le h1
      have hX:Xv^k≤ qv^ (Fintype.card (Site (S.side R p)× I))* G^k:=le_trans (pow_le_pow_left₀ h4 h2 k) ((mul_pow ..).trans_le (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 (by rw [Fintype.card_prod]; exact Nat.le_mul_of_pos_right _ hvI)) (pow_nonneg h3 _)))
      obtain ⟨T,hτ,heP⟩:= Vista.actualA A R0 hv he ho sy z p₀ P x L X Mq (marginM S U p i) lℓ j₀ b r ε Y h Ωs Xv qv hF hY G h3 hp hP hX
      have hw:Function.Injective ((posT r b)∘x):=by
          intro i j hi; by_contra he; have H:= hJ i j he; apply door H hq; change posT r b (x i)=posT r b (x j) at hi; rw [hi,sub_self]
      have hc:= Vista.rootE A R0 P x he hv z ho sy p₀ L b r T hτ hZ ht hw; simp only [hc] at heP; exact heP
lemma singleB (hp:AspectB A R0 he sy Ωs X Mq U lℓ j₀ b r ε Y Xv qv G (p:=p)) (vp:Glyph D)(x:Cover)(hV:vp∈Ωs)(hzX: wrap (S.side R i) x∈ (Θ).margin p₀ (marginM S U p i)): Fence ((S0).chamber p₀) (leaf (i:=i) A R0 vp x) ∧ Potion (leaf (i:=i) A R0 vp x)∧topH S0 A.regulator (leaf (i:=i) A R0 vp x) p₀ ≤ G:=by -- shadow vp FIX
     obtain ⟨hk,⟨h1,h2,h3,h4⟩,hx,⟨hF,hF'⟩,hT,hU,hy,hz⟩:= hp
     have he':= Vista.pegR (i:=i) b r ε Y hv z ho p₀ U Mq X lℓ hz hF hF' hT x hU hy hzX
     exact Vista.oneRate A R0 hv he ho sy z p₀ (fun _:Unit=>vp) (fun _:Unit=>x) [()] X Mq (marginM S U p i) lℓ j₀ b r ε Y he' Ωs Xv qv (fun _=>hV) hx G h3 h1 () rfl (by simp) hk (le_trans (pow_le_pow_left₀ h4 h2 _) (le_of_eq (mul_pow ..)))
end Vista
end Tarot
end YM.Intag
#print axioms YM.Intag.Tarot.Vista.singleB
#print axioms YM.Intag.Tarot.Vista.ding

