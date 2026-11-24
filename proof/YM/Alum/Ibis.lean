import YM.Alum.Lit
import YM.Alum.Hoist
/-! Reading scales & geometry at vintage. Universal euclidean coordinates native stencil lifts presented at physical `resolution` r, independent of regulator beyond i. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Ibis
open QCD.Lat QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Sapphire
open YM.Bank.Jule YM.Bank.Kith YM.Bloom.Jar
open MintV Suburb.Melt Suburb.Melt.Lobby
variable (S:Scheme) (L:Side) {D:ℕ}(Hp:Dial D)(z:ℝ)
-- Tier. resolution Ob root widths. exact identities supported.
noncomputable abbrev Rf (z:ℝ):= WTop L Hp.ν Hp.H z^2
noncomputable def sharpM (i:ℕ):= S.spacing i * Rf L Hp z
variable (i ℓ j₀ p w:ℕ)
set_option quotPrecheck false
local notation "ω"=> measureV L
local notation "δ"=> Rf L Hp z
structure Tier : Prop where
   lower : j₀ ≤ p
   ascend : p < ℓ
   above : ℓ < i
   tempo : w < Hp.e
   epoch : i= Dial.vintage L Hp z j₀
   moment : ℓ= Dial.tailV L Hp z j₀
   view : p=Dial.viewAt L Hp z j₀ w
   counts : (ratioTo S i ℓ:ℝ)= Rf L Hp z / measureV L Hp.e z
   rep : (ratioTo S ℓ j₀:ℝ)= measureV L 4 z * (measureV L (Dial.βA Hp) z * measureV L Hp.e z)
   repB : (ratioTo S ℓ p:ℝ)= measureV L Hp.e z / measureV L w z
local notation "dT"=> Tier S L Hp z i ℓ j₀ p w
namespace Tier
lemma realG : 0 < Rf L Hp z:= pow_pos (zero_lt_one.trans_le (joy ..)) _ -- arity
lemma realH :0 < sharpM S L Hp z i :=mul_pos (inv_pos.mpr (show (0:ℝ) < (S.ratio i).val by exact_mod_cast (S.ratio i).pos)) (realG ..)
end Tier
variable {S L Hp z i ℓ j₀ p w}
section select
variable (h : Dial.ActiveV L Hp z)(hu:w<Hp.e)(hv:i= Dial.vintage L Hp z j₀)(hx:p=Dial.viewAt L Hp z j₀ w)(he:ℓ=Dial.tailV L Hp z j₀)
include h hv hu hx he
lemma ratesQ (hP:∀ k l:ℕ,j₀ ≤ k→ k ≤ l→ l ≤ i→ ratioTo S l k = L.val^(l-k)) : Tier S L Hp z i ℓ j₀ p w:=by
      obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩:= Dial.formerB L Hp z j₀ h w hu; simp only [←hx,←he,←hv] at h1 h2 h3 h4 h5 h7
      have h' : p < ℓ:= lt_of_le_of_lt (Nat.le_add_right p _) h3
      let P(k:ℕ):ℝ:= ratioTo S i k
      have hh(k:ℕ)(hk:j₀ ≤ k)(he:k ≤ i): P k= (L.val:ℝ)^(i-k):=by unfold P; rw [hP _ _ hk he le_rfl,Nat.cast_pow]
      have hu_(k l:ℕ)(hk:k ≤ l)(hl:l≤ i):P k=(ratioTo S i l:ℝ)* ratioTo S l k:=by unfold P; rw [← Nat.cast_mul]; exact_mod_cast (show ratioTo S i k=ratioTo S i l*ratioTo S l k from size_comp (viewW S 1 hk) (viewW S 1 hl) (viewW S 1 (hk.trans hl)))
      have hm : P ℓ = Rf L Hp z / measureV L Hp.e z:=by rw[hh _ h2 h4.le,h7]; exact prunes L _ _ _ z (h.2 w hu).stop.le -- arg check
      have hs :P p= Rf L Hp z/measureV L w z:=by rw [hh _ h1 (h'.trans h4).le,h5]; exact prunes L _ _ _ z (h.2 w hu).lives.le
      have htZ : i-j₀= rollA L Hp.ν Hp.H Hp.βA 4 z:=by rw [hv, Dial.vintage]; omega
      have ht0:P j₀=measureV L 4 z*(Rf L Hp z * measureV L Hp.βA z):=by rw [hh _ le_rfl (h2.trans h4.le), htZ]; exact rolls ..
      let a:= measureV L Hp.e z; let b:= Rf L Hp z; have hz:0<b:=Tier.realG L Hp z; have ht:0<a:=χone ..
      refine ⟨h1,h',h4,hu,hv,he,hx,hm,?_ ,?_⟩
      · have hf:= hu_ _ _ h2 h4.le; rw[← show P ℓ=(ratioTo S i ℓ:ℝ) from rfl,hm,ht0] at hf; change _= _*(_*a); change _*(b*_)= b/a* _ at hf; field_simp at hf; nlinarith only [hf,hz]
      have hf:=hu_ p ℓ h'.le h4.le; rw[← show P ℓ=(ratioTo S i ℓ:ℝ) from rfl,hm, hs] at hf; have hh:0 < measureV L w z := χone ..; change b/_= b/a*_ at hf; change _=a/_; field_simp at hf ⊢; nlinarith only [hf,hz]
end select
local notation "Pφ"=> sharpM S L Hp z i
noncomputable def rescaling (S:Scheme)(m:ℕ)(ρ:ℝ):ℝ:=S.spacing m /ρ
noncomputable def screen (S:Scheme)(m:ℕ)(ρ:ℝ)(x:Cover):E4:= rescaling S m ρ • vector x
local notation "Sm" m:arg=> S.spacing m
local notation "τ" m:arg=> rescaling S m Pφ
local notation "V" m:arg=> screen S m Pφ
namespace Tier
variable (hp:Tier S L Hp z i ℓ j₀ p w) (x:Cover)
include hp
omit hp in
lemma space0 (S:Scheme)(k:ℕ):0<S.spacing k:=by unfold Scheme.spacing; positivity
lemma rising {k:ℕ}: 0<rescaling S k (sharpM S L Hp z i):= div_pos (space0 ..) (realH ..)
lemma res_i : rescaling S i (sharpM S L Hp z i)=(Rf L Hp z)⁻¹:=by unfold rescaling sharpM; have hv:= space0 S i; field_simp
lemma rise_step {m k:ℕ}(he:m ≤ k): rescaling S k (sharpM S L Hp z i)*(ratioTo S k m)=τ m:=by have hf:=space0 S m; have hs:0 < ratioTo S k m := (odd_to he).pos; unfold rescaling Scheme.spacing; rw [factorize (S:=S) he,Nat.cast_mul]; have hD:= (S.ratio m).property; field_simp
lemma shadows : rescaling S ℓ (sharpM S L Hp z i)= (measureV L Hp.e z)⁻¹:=by rw [← hp.rise_step hp.above.le,hp.counts,hp.res_i]; have hZ:=Tier.realG L Hp z; field_simp
lemma shadowB : rescaling S p (sharpM S L Hp z i)= (measureV L w z)⁻¹ :=by rw [← hp.rise_step hp.ascend.le,hp.repB,hp.shadows]; field_simp [χone L z Hp.e] -- syntax Field.Prop
lemma sent_i: screen S i (sharpM S L Hp z i) x= posT (measureV L Hp.ν z) (2 * Hp.H) x:=by unfold posT; unfold screen; rw[hp.res_i]; congr 1; unfold Rf WTop; rw[Nat.mul_comm, pow_mul]
lemma joins {m n:ℕ}(h:m ≤ n): screen S m (sharpM S L Hp z i) x= (V n) (ratioTo S n m • x):=by
       unfold screen; rw [← hp.rise_step h, mul_smul]; refine congr_arg (fun Z=> τ n • Z) (?_); ext a; simp [vector]
lemma aims : screen S ℓ (sharpM S L Hp z i) x= Tarot.Vista.displayR S i ℓ L Hp z x:= (hp.joins x hp.above.le).trans (hp.sent_i _)
lemma scaleL :screen S ℓ (sharpM S L Hp z i) x= posT (measureV L Hp.e z) 1 x:=by unfold screen; rw [hp.shadows, posT, pow_one]; rfl
end Tier
end Ibis
end YM.Intag
#print axioms YM.Intag.Ibis.Tier.scaleL
#print axioms YM.Intag.Ibis.Tier.shadowB
#print axioms YM.Intag.Ibis.ratesQ
#print axioms YM.Intag.Ibis.Tier.aims
