import YM.Bloom.Tip
/-! # buying across every lift & contour, even powers.V & scaling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bloom.TreeP
open Function Lattice Laurent Bloch Metric RG Filter
open Finset YM.Bank Precision Matrix Exterior Arise Arise.Range Jar
open YM.Bank.Jule Ivo Pic Maxwell Hypnos Hypnos.Fruit
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {G:Gauge}{c f:Side}{k m j B r L n D d:ℕ}{a b u v t s W ε C:ℝ}
lemma expanse {v:ℝ}(ht:0<v) (ε s:ℝ): Set.Finite {x:Cover| posT v n x∈ Oasis ε s}:=by
     obtain ⟨M,hM⟩:=exists_nat_gt (s*v^n); let X(i:Axis):ℤ:=M
     refine (Set.Finite.pi fun i:Axis=> Set.finite_Icc (a:=-X i) (b:=X i)).subset ?_ -- type?
     intro x hx; have h:=consp hx; unfold posT at h; obtain ⟨hp,h⟩:=h; rw [norm_smul,Real.norm_of_nonneg (by positivity),mul_comm,← div_eq_mul_inv, div_le_iff₀ (pow_pos ht _)] at h
     intro i hi; have he:|(x i:ℝ)|≤ ‖Kith.rock x‖:=PiLp.norm_apply_le (Kith.rock x) i; have hy:|(x i:ℝ)| ≤ M:= he.trans (h.trans hM.le); obtain ⟨h1,h2⟩:=abs_le.mp hy; refine ⟨?_, ?_⟩; all_goals unfold X; first| exact_mod_cast h1| exact_mod_cast h2
lemma eachH {H:ℕ→ Type} {Z:Type*}(F:Filter Z) (d:ℕ) (f:∀ i j,H i→ H j→ Z→ Prop)(inst:∀ i,Fintype (H i))(h:∀ i≤d,∀ j≤d,∀ (p:H i)(q:H j),∀ᶠ x in F,f i j p q x):∀ᶠ x in F,∀ i≤d,∀ j≤d,∀ (p:H i)(q:H j), f i j p q x:=by
    have ht:∀ i≤d,∀ᶠ x in F,∀ j≤d,∀ (p:H i)(q:H j),f i j p q x:=by
         intro i hi; filter_upwards [(eventually_all_finset (Finset.range (d+1)) (p:=fun j x=>∀ (p:H i)(q:H j),f i j p q x)).2 (fun j hj=> eventually_all.mpr (fun p=>eventually_all.mpr (fun q=> h i hi j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) p q)))] with x hx; intro j hj; exact hx j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    filter_upwards [(eventually_all_finset (Finset.range (d+1))).2 (fun i hi=>ht i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))] with x hx; exact fun i hi=>hx _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
lemma booths (f:ℝ→Side→ Cover→Prop) (h:∀ᶠ W:ℝ in atTop,∀ z:Cover,posT W n z∈Oasis ε s →∀ᶠ c:Side in atTop,f W c z) : ∀ᶠ W:ℝ in atTop,∀ᶠ c:Side in atTop,∀ z:Cover,posT W n z∈Oasis ε s → f W c z:=by
    filter_upwards [h,eventually_gt_atTop (0:ℝ)] with W h hv; let P:=expanse (n:=n) hv ε s -- let syntax
    simpa only [Set.mem_setOf_eq] using (eventually_all_finite P).2 h
-- define scaled pair wrappers.Power n doubled.N.
noncomputable def favorU (W:ℝ)(p:Zinc G d) := W^(4+2*(stemP p).length)
noncomputable def pots (W:ℝ)(c:Side)(p:Zinc G d)(x:Cover) := (favorU W p:ℂ) • voteP c p x
variable (h:Eyes G D L (2*n) j a v b ε s C)
lemma scaled_pair (K:Matrix (Col G c) (Col G c) ℂ)(p: Zinc G d)(q:Zinc G m)(x y:Cover): pop1 (pots (W^n) c p x) (pots (W^n) c q y) K=(W^(2*n))^(4+(stemP p).length+(stemP q).length) • pop1 (voteP c p x) (voteP c q y) K:=by
    unfold pop1 pots; rw [Matrix.smul_mul,transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]; rw [show (W^(2*n):ℝ)= (W^n)^2 from by rw [mul_comm, pow_mul],show ((W^n)^2:ℝ)^(4+(stemP p).length+(stemP q).length)= (favorU (W^n) p)*(favorU (W^n) q) from ?_]; · rw [← Complex.ofReal_mul]; ext; simp [Complex.real_smul]
    unfold favorU; rw [←pow_add,←pow_mul]; congr 1; omega
structure Acquired (G:Gauge)(D n:ℕ)(a v b ε s C W:ℝ) (c:Side): Prop where
    title k(h:k ≤ D)m(ht:m ≤ D)(p:Zinc G k)(q: Zinc G m)(x y:Cover)(F:Bed)(ht':Grain a v b F c)(hq:posT W (2*n) (x-y)∈ Oasis ε s): ‖pop1 (pots (W^n) c p x) (pots (W^n) c q y) (heartP F G c) () () - viewK p q (posT W (2*n) (x-y))‖ ≤ C/W
include h
lemma acquires :∀ᶠ W:ℝ in atTop,∀ᶠ c: Side in atTop, Acquired G D n a v b ε s C W c:=by
     let P:=fun (k m:ℕ)(p:Zinc G k)(q:Zinc G m)(W:ℝ)(c:Side)=> ∀ z:Cover,posT W (2*n) z∈Oasis ε s→∀ x y F, x-y=z → Grain a v b F c→ W*‖(W^(2*n))^(4+(stemP p).length+(stemP q).length) • pop1 (voteP c p x) (voteP c q y) (heartP F G c) () ()-viewK p q (posT W (2*n) z)‖ ≤ C
     have he:= eachH atTop D (fun k m p q W=> ∀ᶠ c in atTop,P k m p q W c) (fun _=>inferInstance) (fun i hi j hj p q=> booths _ (h.compare i hi j hj p q))
     filter_upwards [he,eventually_gt_atTop (0:ℝ)] with W h hp; filter_upwards [eachH atTop D (fun i j p q c=>P i j p q W c) (fun _=>inferInstance) h] with c hc; refine ⟨fun i hi j hj p q x y F ht hz=>?_⟩; rw [le_div_iff₀ hp, scaled_pair, Matrix.smul_apply,mul_comm]; exact hc i hi j hj p q (x-y) hz x y F rfl ht
end YM.Bloom.TreeP
#print axioms YM.Bloom.TreeP.acquires
