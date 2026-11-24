import YM.Massive.Filament.Felt
import YM.Massive.Filament.Seal
/-! # Weighted analytic markers on the graph slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Struck
open Filter Function Finset Complex
open Massive.Filament
open scoped Topology BigOperators Classical
abbrev Dye:=ℕ×ℕ
def pigment (x:Dye)(z s:ℂ):ℂ:= s^x.2*z^x.1
-- Source high strictly paid3 (maybe total p=1? assume high charge itself ≥2). any descended credit of that weight.
-- include converse ∀ˆ0. zero slots remain actual for rollback.
def Ash (x:Dye): Prop:= (x=(0,0)∨ x=(1,2)∨ 2 ≤ x.1 ∧ 3 ≤ x.2)
lemma upperPaint (x:Dye)(z s:ℂ)(he:‖z‖≤1)(hv:‖s‖≤1): ‖pigment x z s‖ ≤1:=by unfold pigment; rw [norm_mul,norm_pow,norm_pow]; exact (mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) hv)).trans (pow_le_one₀ (norm_nonneg _) he)
lemma brightAdd (x y:Dye)(hx:Ash x)(hy:Ash y): Ash (x+y):=by
    obtain hx|hx'|hx':=hx -- preserve hx via duplicate? edit
    · rw [show x=0 from hx,zero_add]; exact (show Ash y from hy)
    · obtain hy|hy|hy:=hy
      · simp [hx',hy,Ash]
      · simp [hx',hy,Ash]
      apply Or.inr (Or.inr ?_); obtain ⟨he,hv⟩:=hy; simp only [hx',Prod.fst_add, Prod.snd_add]; omega
    obtain hy|hy|hy:=hy
    · rw [show y=0 from hy, add_zero]; exact (show Ash x from Or.inr (Or.inr hx'))
    · apply Or.inr (Or.inr ?_); simp only [hy,Prod.fst_add,Prod.snd_add]; omega
    exact Or.inr (Or.inr ⟨(show 2 ≤ x.1+y.1 from by omega),(show 3≤x.2+y.2 from by omega)⟩)
variable {ι:Type}
lemma bright_sum (B:Finset ι)(Q:ι→Dye)(h:∀ i∈B,Ash (Q i)): Ash (∑ i∈ B,Q i):=by induction B using Finset.induction_on with|empty=>exact Or.inl (by rw [sum_empty];rfl)|insert i B hi ih=> rw [sum_insert hi]; exact brightAdd _ _ (h i (mem_insert_self ..)) (ih (fun j hj=> h j (mem_insert_of_mem hj)))
def lane (z s:ℂ):Multiplicative Dye→* ℂ where
 toFun x:= pigment (Multiplicative.toAdd x) z s
 map_one':=by unfold pigment; simp
 map_mul' x y:=by unfold pigment; simp; ring
lemma pigment_sum (B:Finset ι)(Q:ι→Dye)(z s:ℂ): pigment (∑ i∈B,Q i) z s=∏ i∈B,pigment (Q i) z s:=by
    change (lane z s) (Multiplicative.ofAdd (∑ i∈B,Q i))=_; rw [ofAdd_sum,map_prod];rfl
lemma prime (x:Dye)(h:Ash x): Fused (pigment x):=by
    let f(z s:ℂ):= pigment x z s; refine (Fused.code (1:ℂ) x.1 x.2 ?_).congr f fun _ _ _ _=> (by simp [f,pigment])
    obtain h|h|h:=h; · subst x; exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr (Or.inl ⟨(congr_arg Prod.fst h),(congr_arg Prod.snd h)⟩)
    exact Or.inr (Or.inr ⟨lt_of_lt_of_le (by norm_num) h.1,h.2⟩)
lemma qr (x:Dye)(z s:ℝ): ↑(s^x.2*z^x.1)=pigment x (z:ℂ) (s:ℂ):=by unfold pigment; norm_cast
lemma idP (d:Dye)(z s:ℂ)(h:d.1=0)(he:Ash d): pigment d z s=1:=by
    unfold Ash at he; rcases he with he|he|⟨he,hk⟩; · simp [he,pigment]
    · simp [he] at h
    omega
lemma within_weight (d:Dye)(z s:ℂ) (hz:‖z‖≤1)(he:Ash d)(hb:‖s‖≤1): (d.1=1 → ‖pigment d z s‖≤ ‖s‖^2) ∧ (2 ≤d.1 → ‖pigment d z s‖≤ ‖s‖^3):=by
    unfold pigment; rw [norm_mul, norm_pow,norm_pow]; have ht:‖s‖ ^d.2*‖z‖^d.1≤ ‖s‖^d.2:=mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hz); obtain he|he|⟨he,h⟩:=he; · simp [he]
    · subst d; constructor; · exact fun _=>ht
      simp
    exact ⟨fun _=> (by omega),fun _=> ht.trans (pow_le_pow_of_le_one (norm_nonneg _) hb h)⟩
end YM.QCD.Struck
#print axioms YM.QCD.Struck.bright_sum
