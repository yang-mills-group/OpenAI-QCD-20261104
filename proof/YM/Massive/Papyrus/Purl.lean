import YM.Massive.Papyrus.Kedge
import Mathlib.LinearAlgebra.Lagrange
/-! # Finite-extent multiindex stencils conserving (origin) derivatives in the ungauged Taylor reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Papyrus.Purl
open Lattice Wilson RG Source Function QCD Source.Drops UV Filter Work.G05 Finset Matrix Labels
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical
open Scan Paper Boat Polynomial
variable (d:ℕ) (c:ℕ) (z:ℤ)
abbrev teeth (d:ℕ):Finset ℤ:= Icc (- (d:ℤ)) (d:ℤ)
def ψ (n:ℕ) : ℤ→ℝ:= fun x=> (x:ℝ)^n / Nat.factorial n
lemma tooth : d < (teeth d).card:=by unfold teeth; rw [Int.card_Icc]; omega
def items (c :ℕ)(x:ℤ): ℝ:= if c=0 then (if x=0 then 1 else 0) else
   (Nat.factorial c:ℝ) * (Lagrange.basis (teeth d) (fun z=> (z:ℝ)) x).coeff c
lemma learns {n:ℕ}(h:n≤d) : ∑ x∈teeth d, items d c x* ψ n x=if n=c then 1 else 0:=by
   by_cases hh: c=0
   · subst c; simp only [items, if_true, ite_mul, one_mul, zero_mul]; rw [Finset.sum_ite_eq']; by_cases hv:n=0 <;> simp [ψ,hv]
   let F:= (Polynomial.X: Polynomial ℝ)^n * Polynomial.C ((Nat.factorial n:ℝ))⁻¹; have hd: (Nat.factorial n:ℝ) ≠0:= by positivity
   have hf(z:ℤ): F.eval (z:ℝ)=ψ n z:=by unfold F ψ; simp [div_eq_mul_inv]; ring
   have hv: F.degree < ↑(teeth d).card:=by
      unfold F; rw [degree_mul, degree_C (inv_ne_zero hd), degree_X_pow, add_zero]; exact_mod_cast h.trans_lt (tooth d)
   have hl:= Lagrange.eq_interpolate (f:=F) (v:=fun z:ℤ=>(z:ℝ)) ((Int.cast_injective (α:=ℝ)).injOn (s:=↑(teeth d))) hv; have he:= congr_arg (fun x:Polynomial ℝ=> x.coeff c) hl; change F.coeff c = _ at he; rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff] at he; simp_rw [hf, coeff_C_mul] at he
   simp_rw [items, if_neg hh, mul_assoc, mul_comm ((Lagrange.basis _ _ _).coeff _),← Finset.mul_sum, ← he]; unfold F; rw [coeff_mul_C, coeff_X_pow]; by_cases ht:n=c; · subst c; simp [hd]
   simp [ht,Ne.symm ht]
def swath (c:ℕ)(x:ℤ): ℝ:= (1/2:ℝ)*(items d c x+(-1:ℝ)^c*items d c (-x))
lemma swath_neg : swath d c (-z)=(-1:ℝ)^c*swath d c z:=by
   unfold swath; rw [neg_neg]; have hf:(-1:ℝ)^c*(-1:ℝ)^c=1:=by rw [← mul_pow]; simp
   rw [mul_left_comm, mul_add ((-1:ℝ)^c), ← mul_assoc ((-1:ℝ)^c) ((-1:ℝ)^c), hf, one_mul,add_comm] -- ?
lemma swath_eq : swath d 0 z=if z=0 then 1 else 0:=by by_cases hz:z=0 <;> norm_num [swath,items, hz]
lemma refl_teeth : (teeth d).image (fun i=> -i)=teeth d:=by ext i; simp only [mem_image,teeth,mem_Icc]; constructor; rintro ⟨x,⟨h,k⟩,rfl⟩; omega; intro h; exact ⟨-i,by omega, by omega⟩
lemma sum_swath {n:ℕ}(h:n≤d) : ∑ x∈teeth d, swath d c x* ψ n x=if n=c then 1 else 0:=by
   have hL:=learns d c h; let δ:ℝ:= if n=c then 1 else 0; let x:ℤ→ℝ:=fun i=> items d c (-i); have hd(i): ψ n (-i)=(-1:ℝ)^n* ψ n i:=by unfold ψ; push_cast; ring
   have hv: ∑ i∈ teeth d, x i*ψ n i=(-1:ℝ)^n*δ:=by
       conv_lhs=> rw [← refl_teeth d]
       rw [sum_image]; simp only [x,neg_neg,hd]; rw [show (fun y=>items d c y *((-1:ℝ)^n* ψ n y))=(fun y=>(-1:ℝ)^n*(items d c y * ψ n y)) from funext fun i=>mul_left_comm ..,← mul_sum, learns d c h]
       intro _ _ _ _; apply neg_injective
   unfold swath; simp_rw [mul_assoc (1/2:ℝ) _ _,add_mul,mul_assoc,  ← mul_sum (a:=(1/2:ℝ)),sum_add_distrib, ← mul_sum (a:=((-1:ℝ)^c)), hL]; unfold x at hv; rw [hv]; by_cases hh:n=c; · subst n; rw [← mul_assoc _ _ δ,← mul_pow]; norm_num [δ]
   simp [hh,δ]

-- `Gauge anchor box` lives in cover with arbitrary prescribed side extension
variable {d}
variable (p q:Multi d) (x:Cover)
def sample (p : Multi d) (x:Cover):ℝ:= if x∈ box d then ∏ i:Axis, swath d (power p i) (x i) else 0
def profileL (p:Multi d)(x:Cover):ℝ:= ∏ i:Axis, ψ (power p i) (x i)
lemma shrunk (s: Signed)(i:Axis): swath d (power p i) (s.act x (s.perm i))=(signT s i)^(power p i)*swath d (power p i) (x i):=by
   rw [Signed.act_at]; cases h:s.flip i <;> simp only [signT,h,if_true,if_false, Bool.false_eq_true]; · rw [one_pow,one_mul]
   exact swath_neg ..
lemma parcel (s: Signed): sample (hem s p) (s.act x)= marked s p * sample p x:=by
   unfold sample; have ht: s.act x∈ box d ↔ x∈box d:=⟨fun hx=>by rw [← s.inv_act x, ← box_covariant d s⁻¹]; exact mem_image_of_mem _ hx,fun hx=> by rw [← box_covariant d s]; exact mem_image_of_mem _ hx⟩
   by_cases he:x∈box d
   · rw [if_pos he, if_pos (ht.mpr he),← Equiv.prod_comp s.perm]; simp_rw [pinned, shrunk, prod_mul_distrib]; rfl
   rw [if_neg he, if_neg (he ∘ ht.mp), mul_zero] -- `∘` function type
lemma power_zero (i:Axis)(d: ℕ): power (0:Multi d) i=0:=rfl
lemma central (d:ℕ) : sample (0:Multi d) x=if x=0 then 1 else 0:=by
   unfold sample; split_ifs with h he h' -- cases
   · subst x; simp_rw [power_zero,swath_eq]; simp
   · obtain ⟨i,hi⟩:= Function.ne_iff.mp he; exact Finset.prod_eq_zero (mem_univ i) (by rw [power_zero,swath_eq,if_neg (show x i≠0 from hi)])
   · subst x; simp at h
   rfl
lemma sample_Φ : (∑ x∈box d, sample p x*profileL q x)=if q=p then 1 else 0:=by
    let f:=fun (i:Axis)(x:ℤ)=> swath d (power p i) x * ψ (power q i) x; have he(x:Cover)(h:x∈box d): sample p x * profileL q x=∏ i:Axis, f i (x i):=by rw [sample,if_pos h,profileL,← prod_mul_distrib]; -- rfl?
    have ht: box d= Fintype.piFinset (fun _ :Axis=> teeth d):= rfl
    rw [sum_congr rfl he, ht, ← Finset.prod_univ_sum]; simp_rw [show ∀ i:Axis, ∑ x∈teeth d,f i x=(if power q i=power p i then 1 else 0) from fun i=>sum_swath d _ (show power q i≤d from Nat.le_of_lt_succ (q.val i).isLt)]; by_cases h:q=p
    · simp [h]
    have hv:∃ i:Axis,power q i≠power p i:=by contrapose! h; apply Subtype.ext; funext i; apply Fin.ext; exact h i
    obtain ⟨i,hi⟩:=hv; rw [if_neg h]; exact Finset.prod_eq_zero (mem_univ i) (by rw [if_neg hi])
lemma ghost (h:x∉box d): sample p x=0:=if_neg h
lemma surveyor {u:Finset Cover}(h:box d⊆u) : (∑ x∈u,sample p x*profileL q x)= if q=p then 1 else 0:=by rw [← sample_Φ]; exact (sum_subset h (fun x _ h=>by rw [ghost _ _ h,zero_mul])).symm
end YM.Massive.Papyrus.Purl
#print axioms YM.Massive.Papyrus.Purl.surveyor
