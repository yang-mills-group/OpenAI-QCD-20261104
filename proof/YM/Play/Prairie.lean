import YM.Play.Yarn
import YM.Play.Joints
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bera
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix Next.Rank.Normal MvPolynomial Anomaly Cove
open scoped BigOperators Topology ContDiff Classical Matrix
variable {A B T Z P Y F R:Type*}
section cotton
variable [NormedCommRing F][NormedAlgebra ℂ F][NormedCommRing P][NormedAlgebra ℂ P]
-- inclusion mixed coefficients.
def outer (q:poly A) : F→ₗ[ℂ]Papers A F := (MvPolynomial.monomial (0:A→₀ℕ)).restrictScalars ℂ |> LinearMap.comp (LinearMap.mulRight ℂ (MvPolynomial.map (algebraMap ℂ F) q)) -- optional
lemma outP (x:F)(q:poly A): outer q x=C x*(MvPolynomial.map (algebraMap ℂ F) q):=rfl
lemma outCoin (x:F)(q:poly A)(i): coeff i (outer q x)= (coeff i q) • x:=by
    rw [outP,coeff_C_mul, coeff_map, mul_comm,Algebra.smul_def]
lemma outadd (x:F)(p q:poly A): outer (p+q) x=outer p x+outer q x:=MvPolynomial.ext _ _ (fun i=>by simp only [coeff_add,outCoin,add_smul])
lemma outs (x:F)(a:ℂ)(p:poly A): outer (a•p) x= a • outer p x:=MvPolynomial.ext _ _ (fun i=>by rw [coeff_smul]; simp_rw [outCoin,coeff_smul]; exact (mul_smul ..)) -- orientation
lemma outMul (x y:F)(p q:poly A): outer p x*outer q y=outer (p*q) (x*y):=by
    simp only [outP,map_mul]; ring
lemma outmono (x:F)(i:A→₀ℕ)(a:ℂ): outer (monomial i a) x=monomial i (a•x):=by
    ext1 j; rw [outCoin]; by_cases h:i=j; · subst i; simp only [coeff_monomial]; simp
    simp [coeff_monomial,h]
def casts (x:F) : poly A→ₗ[ℂ]Papers A F where
  toFun p:=outer p x
  map_add' := outadd x
  map_smul':= outs x
-- Moss
variable (L:poly A→ₗ[ℂ]poly B)(T0:F→ₗ[ℂ]P)
private def fees (x:Papers A F):= ∑ i∈ x.support,(outer (L (monomial i 1))) (T0 (coeff i x))
private lemma reach (p:Papers A F) (Q:Finset (A→₀ℕ))(h:p.support⊆ Q): fees L T0 p= ∑ i∈ Q,(outer (L (monomial i 1))) (T0 (coeff i p)):=sum_subset h fun i _ hi=> by rw [MvPolynomial.notMem_support_iff.mp hi,map_zero,map_zero]
def ferry : Papers A F→ₗ[ℂ] Papers B P where
  toFun:= fees L T0
  map_add' x y:=by
     rw [reach L T0 _ _ MvPolynomial.support_add,reach L T0 x (x.support∪y.support) Finset.subset_union_left,reach L T0 y (x.support∪y.support) Finset.subset_union_right]; simp_rw [coeff_add,map_add,sum_add_distrib]
  map_smul' r x:=by
     change fees L T0 (_ • _)= r • fees L T0 x; by_cases h:r=0; · simp [h,fees]
     unfold fees; rw [smul_sum, show (r • x).support=x.support from (by ext; simp [h])]; refine sum_congr rfl fun i _=>?_ ; rw [coeff_smul,map_smul,map_smul]
lemma ferried (i:A→₀ℕ)(b:F): ferry L T0 (monomial i b)=outer (L (monomial i 1)) (T0 b) :=by
   change fees L T0 _ = _; rw [reach L T0 _ {i} (show _ from ?_),sum_singleton]; swap
   · intro j hj; by_contra hn; rw [mem_singleton] at hn; apply MvPolynomial.mem_support_iff.mp hj; rw [coeff_monomial,if_neg (Ne.symm hn)]
   rw [coeff_monomial,if_pos rfl]
lemma covert (p:poly A) (b:F) : ferry L T0 (outer p b)= outer (L p) (T0 b):=by
    change ferry L T0 (casts b p) = casts _ _; rw [p.as_sum,map_sum,map_sum,map_sum,map_sum]; refine sum_congr rfl fun i _=> ?_
    change ferry L T0 (outer _ _) = outer _ _; rw [outmono,ferried,map_smul,map_smul]; let D:=(monomial i 1: poly A); let a:=coeff i p; conv_rhs => rw [show monomial i a=a•D from (by unfold D; rw [← map_smul, smul_eq_mul,mul_one]),map_smul,outs]
-- evaluation bound on monomials separately later.
lemma priced (p:poly A)(b:F): cents (outer p b) ≤ cents p *‖b‖:=by
    unfold cents; simp only [outCoin,norm_smul]; rw [Finset.sum_mul]; apply sum_le_sum_of_subset_of_nonneg; · intro i hi; rw [MvPolynomial.mem_support_iff]; rw [MvPolynomial.mem_support_iff,outCoin] at hi; exact fun h=>hi (by rw [h,zero_smul]) -- lemma
    exact fun _ _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _)
lemma outMask {u:Finset A}{q:poly A}{n:ℕ}(hp:q∈Camp u n)(x:F): outer q x∈Camp u n:=by
    intro i hi; apply hp i; apply MvPolynomial.mem_support_iff.mpr; rw [MvPolynomial.mem_support_iff,outCoin] at hi; exact fun h=>hi (by rw [h,zero_smul])
-- binder other conditions share `←Rim` etc
end cotton
section
variable {s t d u:ℝ}{X₀:Finset A}{X₁:Finset B}{n m i k:ℕ}{D:Finset Z}{E:Finset T}
variable [Fintype Z][Fintype T]
def vault (D:Submodule ℂ (Patio Z)): Submodule ℂ (Papers A (Patio Z)) where
    carrier := {p|∀ i, coeff i p ∈ D}
    zero_mem':=by simp
    add_mem' := by intro x y h g i; rw [coeff_add]; exact D.add_mem (h i) (g i)
    smul_mem' := by intro a x h i; rw [coeff_smul]; exact D.smul_mem a (h i)
lemma vaultUp {D E:Submodule ℂ (Patio Z)}{x:Papers A (Patio Z)}(he:x∈vault D)(h:D ≤ E): x∈vault E:= fun i=> h (he i)
lemma outVault (q:poly A) {D:Submodule ℂ (Patio Z)}{x:Patio Z}(h:x∈D): outer q x ∈ vault D:= by intro i; rw [outCoin]; exact Submodule.smul_mem _ _ h
lemma intoVault {X:Submodule ℂ (Patio Z)}{W:Submodule ℂ (Patio T)}{x:Papers A (Patio Z)}(h:x∈vault X) (L:poly A→ₗ[ℂ]poly B)(T0:Patio Z→ₗ[ℂ] Patio T)(hp: ∀ i∈ x.support,T0 (coeff i x)∈ W): ferry L T0 x∈vault W:=by
    rw [x.as_sum,map_sum]; apply Submodule.sum_mem; intro i hi; rw [ferried]; exact outVault _ (hp i hi)
-- Record compact state is rect width: total separate heights
abbrev vaultS (D:Finset Z)(n:ℕ) := Submodule.comap ((light Z).toLinearMap) (Rim D n)
def Ledger (D:Finset Z) (X:Finset A)(n m:ℕ) : Submodule ℂ (Papers A (Patio Z)):= vault (vaultS D m) ⊓ Camp X n
lemma edgeL (b: Patio Z){s:A→₀ℕ}(h:tags X₀ n s)(hv:b.val∈Rim D m): monomial s b∈Ledger D X₀ n m:=by
    refine ⟨?_,sparks b h⟩; rw [← one_smul ℂ b,← outmono]; exact outVault _ hv
lemma leaguer {p:Papers A (Patio Z)}(h:p∈Ledger D X₀ n m){D₃:Finset Z}{XA:Finset A}(hD:D⊆D₃)(hX:X₀ ⊆ XA)(hn:n ≤ i)(hm:m≤k): p∈ Ledger D₃ XA i k:= ⟨vaultUp h.1 (fun _ h=> Rim.monotone hD hm h), shadeC h.2 hX hn⟩
lemma careful {p:Papers A (Patio Z)}(h:p∈ Ledger D X₀ n m) i : (coeff i p).val ∈ Rim D m:=h.1 i
lemma harbored {p q:Papers A (Patio Z)}(h:p∈Ledger D X₀ n m)(hx:q∈Ledger D X₀ i k): p*q∈Ledger D X₀ (n+i) (m+k):=by
    rw [MvPolynomial.mul_def]; simp_rw [MvPolynomial.sum_def]; exact Submodule.sum_mem _ fun j hj=>Submodule.sum_mem _ fun k hk=>edgeL _ (adding j k (stampC h.2 j hj) (stampC hx.2 k hk)) (Rim.multiply (careful h j) (careful hx k))
lemma arrives (D:Finset Z): (1:Papers A (Patio Z))∈Ledger D X₀ n m:=by
    rw [← map_one (MvPolynomial.C:Patio Z→+* _)]; refine edgeL 1 (s:=0) ⟨?_,?_⟩ (Rim.one _)<;> simp [len]
variable (L:poly A→ₗ[ℂ]poly B)(T':Patio Z→ₗ[ℂ]Patio T)
lemma throughL (p:Papers A (Patio Z))(h:p∈Ledger D X₀ n m)(ht: ∀ q∈ Camp (F:=ℂ) X₀ n,L q ∈ Camp X₁ i)(hh:∀ x:Patio Z,x.val∈Rim D m →(T' x).val∈Rim E k): ferry L T' p∈ Ledger E X₁ i k:=by
    rw [p.as_sum,map_sum]; apply Submodule.sum_mem; intro j hj; rw [ferried]; exact ⟨outVault _ (hh _ (careful h _)),outMask (ht _ (sparks _ (stampC h.2 j hj))) _⟩
lemma worth (p:Papers A (Patio Z))(h:p∈Ledger D X₀ n m)(hp:∀ q∈Camp X₀ n,cents (L q) ≤ s * cents q)(hs:0≤s)(ht:∀ x:Patio Z,x.val∈Rim D m →‖T' x‖ ≤t*‖x‖): cents (ferry L T' p)≤ s*t*cents p:=by
    nth_rw 1 [p.as_sum]; rw [map_sum, mul_assoc]; apply (money ..).trans; unfold cents; rw [mul_sum,mul_sum]; -- caution order
    apply Finset.sum_le_sum; intro i hi; have hg :cents (L (monomial i 1)) ≤ s:=(by simpa only [solely,norm_one,mul_one] using hp _ (sparks (1:ℂ) (stampC h.2 i hi))); change cents _ ≤ _; rw [ferried]; exact (priced _ _).trans (mul_le_mul hg (ht _ (careful h i)) (norm_nonneg _) hs) -- a*s*b
lemma bronze (R:poly A→ₗ[ℂ]poly B)(A':Patio Z→ₗ[ℂ]Patio T)(p:Papers A (Patio Z)):
    ferry L T' p-ferry R A' p=ferry (L-R) T' p+ ferry R (T'-A') p:=by
    rw [p.as_sum]; simp only [map_sum,←sum_add_distrib, ← sum_sub_distrib]; refine sum_congr rfl fun i _=>?_ ; simp_rw [ferried]; change _-_=casts (T' _) (L _ -R _)+ outer _ (T' _ -A' _); rw [map_sub,map_sub]; change _-_ = outer _ _-outer _ _ + (outer _ _-outer _ _); -- metas
    abel
end
end YM.QCD.Bera
#print axioms YM.QCD.Bera.harbored
#print axioms YM.QCD.Bera.bronze
