import YM.OPE.Log.Moderate
import YM.QCD.Calm.Shoal
/-! # Expense of extracting monic labels from a well-budgeted nonscalar port

Mixed terms redeem after output depending on local multiplicity alone. One must account
for K terms which may simultaneously choose *many* coincident alternatives on estimating
absolute costs (even with the polyhedral quotient by exclusion). Distinguish here
separation WITHIN the monomial ONLY. This is a Bernoulli entropy estimate over all
feasible monomials; height ratio may be expensive like β^q at fixed choices. Reusable
on other available sparse systems.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cupola
open Lattice Finset Pressure ConnectedActivityE6 QCD Lat Wilson Filter
open scoped BigOperators Topology Classical
variable {n:Side}{I:Type}[Fintype I] (o:I→Site n) (X:Support n)
def Fires (H:ℕ):Prop:=∀ i, (Finset.univ.filter (fun j=> o j=i)).card ≤ H
def barn : Finset I:= X.biUnion (fun i=>Finset.univ.filter (fun j=>o j=i))
lemma inside (i:I): i∈barn o X↔ o i∈X:=by simp [barn]
def Spaced (t:Finset I)(B:ℕ):Prop:= ∀ i∈t,∀ j∈t,i≠j → B*B ≤ separation (o i) (o j)
def mixed (B:ℕ) := (barn o X).powerset.filter (fun s=>2 ≤ s.card ∧ Spaced o s B)
lemma shore (s:Finset I)(B:ℕ): s∈ mixed o X B ↔ s.image o ⊆ X ∧ 2 ≤ s.card ∧ Spaced o s B:=by simp only [mixed,mem_filter,mem_powerset]; rw [image_subset_iff]; simp only [Finset.subset_iff,inside]
lemma barncard (H B:ℕ)(h:Fires o H): (barn o X).card ≤ coverNumber B X*(B+B+1)^4*H:= (card_biUnion_le ..).trans ((sum_le_sum (fun i _=>h i)).trans (by rw [sum_const, smul_eq_mul]; gcongr; exact Corona.pays X B))
local notation "q#" a b B => Real.exp (a*b/(128:ℝ)*B)
-- vote clearance holds even if β ratios reach exp(a/128*B). common schedule delays.
lemma steam (B H:ℕ) (a b:ℝ)(hp:0<a)(hb:8≤B) (hm:0≤b)(ht:b ≤ Real.exp (a/128*(B:ℝ)))(hF:Fires o H)
    (he:(B+B+1:ℝ)^4*H*Real.exp (-a/128*B) ≤ a) :
    (∑ s∈ mixed o X B, b^s.card * Real.exp (-(2*a)*coverNumber B X)) ≤ 1:=by
    let D:=(coverNumber B X:ℝ); let k:ℝ:=(B:ℝ)*a/128; let f:ℝ:=Real.exp (-k)
    let g s:=(f^(s:Finset I).card); have hG s:0 ≤ g s:= pow_nonneg (Real.exp_nonneg _) _
    have h(s:Finset I) (hx:s∈mixed o X B): b^s.card * Real.exp (-(2*a)*D) ≤ g s*Real.exp (-a*D):=by
       obtain ⟨hx,hy,hz⟩:=(shore ..).1 hx; have hi:= OPE.Log.separatedMarks s o hz hb (by omega) hy X hx; have hh:(B:ℝ)*s.card≤64*D:=by unfold D; exact_mod_cast hi
       have hv:b≤Real.exp k:=ht.trans_eq (by unfold k; congr 1; ring)
       refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm hv _) (Real.exp_nonneg _)).trans ?_
       unfold g f; rw [← Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add,Real.exp_le_exp]; unfold k; nlinarith only [mul_le_mul_of_nonneg_left hh hp.le]
    let z:=barn o X; let y:=Real.exp (-a*D); apply (sum_le_sum h).trans; rw [← sum_mul]; refine (mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i _ _=> hG i)) (Real.exp_nonneg _)).trans ?_
    change (∑ s∈z.powerset,g s)*y ≤ _; have hy:(∑ s∈ z.powerset,g s)=(f+1)^z.card:=by simpa only [one_pow,mul_one] using sum_pow_mul_eq_add_pow f 1 z
    rw [hy]; have hQ:0 ≤ f:= Real.exp_nonneg _; refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith : 0 ≤ f+1) (Real.add_one_le_exp f) z.card) (Real.exp_nonneg _)).trans ?_
    have hz:(z.card:ℝ)≤ D*(B+B+1:ℝ)^4*H:=by unfold D; exact_mod_cast barncard o X H B hF
    have hD:0 ≤ D:=Nat.cast_nonneg _; rw [show (-a/128 * B)= -k from by unfold k; ring] at he
    rw [←Real.exp_nat_mul,← Real.exp_add, Real.exp_le_one_iff]; nlinarith only [mul_le_mul_of_nonneg_right hz hQ, mul_le_mul_of_nonneg_left (show _*f ≤ _ from he) hD]
variable (L:Side) {a t:ℝ}{b:ℝ→ℝ}
-- little β powers allowed even if relative β chosen before schedule. includes corner.Phantom χ unaffected.
lemma exsteam (hp:0<a)(H:ℕ)(he:Rate su L t b) : ∀ᶠ x:ℝ in atTop,∀ (n:Side)(I:Type)[Fintype I](o:I→Site n)(X:Support n), Fires o H →
    (∑ s∈mixed o X (radiusB x), |b x| ^ s.card * Real.exp (-(2*a)*coverNumber (radiusB x) X)) ≤ 1:=by
    let v x:= ((radiusB x:ℝ)+(radiusB x:ℝ)+1)^4*H
    have hv: Rate su L 0 v:=by simpa only [v,zero_mul] using! ((((Rate.radius_price.add Rate.radius_price).add (Rate.const 1)).pow 4).mul_right (H:ℝ))
    let u:=a/128; have hu:0<u:=by unfold u; positivity
    filter_upwards [(hv.mul (Calm.expHigh L (t:=-1) hu)).below (by norm_num) a hp, (he.mul (Calm.expHigh L (t:= -t-1) hu)).below (by linarith) 1 zero_lt_one, Work.E01.radiusB_tendsto.eventually_ge_atTop 8] with x h1 h2 h3
    unfold u at h1 h2; simp only [← neg_div] at h1 h2; intro n I _ o X hF; apply steam o X _ _ _ _ hp h3 (abs_nonneg _) ?_ hF ((le_abs_self _).trans h1); rw [abs_mul,abs_of_nonneg (Real.exp_nonneg _)] at h2; simpa [show -a/128 * (radiusB x:ℝ)= -(a/128 * (radiusB x:ℝ)) by ring, Real.exp_neg] using ((le_div_iff₀ (Real.exp_pos _)).mpr h2)
end YM.MassiveQCD.Cupola
#print axioms YM.MassiveQCD.Cupola.exsteam
