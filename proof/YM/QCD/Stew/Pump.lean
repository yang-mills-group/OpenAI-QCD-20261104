import YM.QCD.Stew.Pot
/-! # Linear read Motions and charge. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ} {t:ℝ} {o: Site c}
variable {D K V E:Type*} [Fintype D][DecidableEq D][Fintype K][DecidableEq K]
section blade
variable {D:Type*} [Fintype D][DecidableEq D]
def panel (n:ℕ):Alg D→ₗ[ℂ] Alg D:= { toFun:=fun x=>∑ s :Finset D, (if s.card=n then coef s x • mono s else 0), map_add':=fun x y=>by rw [← Finset.sum_add_distrib]; exact sum_congr rfl fun i _=>by split <;> simp [add_smul], map_smul':=fun c x=>by rw [smul_sum]; refine sum_congr rfl fun i _=> ?_; split <;> simp [smul_smul] }
lemma chamber (n:ℕ)(x:Alg D): panel n x ∈ layer D n:= Submodule.sum_mem _ fun i _=>by split <;> rename_i h; exact Submodule.smul_mem _ _ (h ▸ homogeneous i); exact Submodule.zero_mem _
lemma angel (n:ℕ)(s:Finset D)(x:Alg D): coef s (panel n x)= if s.card=n then coef s x else 0:=by
   change coef s (∑ i: Finset D, if i.card=n then coef i x • mono i else 0)=_; rw [map_sum,sum_eq_single s]
   · split <;> simp
   · intro i _ hi; split; next _=> rw [map_smul, read_other _ _ hi.symm, smul_zero]
     next _=> exact map_zero _
   simp
lemma measured (s: Finset D) (h: s.card %2 =1) (x: Patio D): coef s x.val=0 :=by
   have he: coef s x.val=(-1:ℂ)^s.card • coef s x.val:=by
      have hh:=x.2; change Grass.grade x.val=x.val at hh
      let v:= x.val; have hv(j):Grass.grade (mono j)=(-1:ℂ)^j.card • mono (A:=D) j:=Grass.grade_mono (A:=D) j
      have hQ:coef s (Grass.grade v)=(-1:ℂ)^s.card • coef s v:=by
         nth_rw 1 [← write v]; simp only [map_sum,map_smul,hv]; rw [sum_eq_single s]
         · rw [Grass.read]; simp; ring
         · intro i _ hi; rw [read_other _ _ hi.symm]; simp
         simp
      unfold v at hQ; rwa [hh] at hQ
   rw [Odd.neg_one_pow (Nat.odd_iff.mpr h), neg_one_smul] at he
   apply Complex.ext
   · have hp:=congr_arg Complex.re he; rw [Complex.neg_re] at hp; rw [Complex.zero_re]; linarith
   have hp:=congr_arg Complex.im he; rw [Complex.neg_im] at hp; rw [Complex.zero_im]; linarith
lemma poster (x y:Alg D)(h:∀ s, coef s x=coef s y): x=y:=by nth_rw 1 [← write x,← write y]; exact sum_congr rfl fun i _=>congr_arg (fun c:ℂ=> c • mono i) (h i) -- recursive h issue
lemma past (n:ℕ){x:Alg D}(k:ℕ)(hx : x∈ layer D n):panel k x=if k=n then x else 0:=by
   refine poster _ _ fun i=>?_ ; by_cases h:k=n
   · rw [if_pos h,h,angel]; split; · rfl
     next h=> exact (spectrum hx i h).symm
   rw [if_neg h,angel,map_zero]; split; next he=> exact spectrum hx i (he ▸ h)
   next _=> rfl
lemma ponder {σ: ℂ →+* ℂ}(L: Alg D →ₛₗ[σ] Alg D)(hv:∀ i, L (mono i) ∈layer D i.card)(p:ℕ)(x:Alg D):panel p (L x)=L (panel p x):=by
   rw [← write x]; simp only [map_sum,map_smul, map_smulₛₗ]; refine sum_congr rfl fun i _=> ?_; rw [past _ _ (hv i),past _ _ (homogeneous i)]; split; · rfl
   rw [map_zero]
end blade
section Dir
lemma sport (B: Matrix D D ℂ)(x: Dirac D)(i:ℕ) : panel i (disguise B x)= disguise B (panel i x):=ponder (disguise B).toLinearMap (fun s=> exterior_layer _ (homogeneous s)) i _
lemma toned (x:Dirac D)(i:ℕ): panel i (surf _ x)=surf D (panel i x):=ponder (surf D) (fun s=> exterior_layer _ (cc_degree (homogeneous s))) _ _
lemma bush (x:Alg D): panel 0 x=coef ∅ x • 1:=by
   apply poster; intro i; rw [angel,map_smul,← mono_empty]; by_cases h:i=∅; · rw [h, Grass.read]; simp
   rw [if_neg (show ¬ _ from mt Finset.card_eq_zero.mp h), read_other i ∅ h,smul_zero]
lemma grazing (n:ℕ)(x:Patio D):Plus (panel n x.val):=by
    unfold Plus panel; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [map_sum]; refine sum_congr rfl fun i _=> ?_; split; swap; · exact map_zero _
    by_cases h:Even i.card; · rw [map_smul,Grass.grade_mono,Even.neg_one_pow h,one_smul]
    rw [measured _ (Nat.odd_iff.mp (Nat.not_even_iff_odd.mp h)),zero_smul,map_zero]
noncomputable def stage (n:ℕ): Patio D→ₗ[ℂ] Patio D:={ toFun:=fun x=>⟨panel n x.val,grazing n x⟩, map_add':=fun x y=> Subtype.ext (map_add _ x.val y.val), map_smul':=fun a x=>Subtype.ext (map_smul _ a x.val) }
end Dir
lemma absolute (o:Site c)(n:ℕ)(x:EvenA c N)(he:0≤t): Sen o t (stage n x)≤ Sen o t x:=by
   unfold Sen; rw [plank,pricesD _ he,pricesD _ he]; refine sum_le_sum fun i _=> ?_; change starch _ _ _*‖coef i (panel n x.val)‖≤_; rw [angel]; apply mul_le_mul_of_nonneg_left _ (starch_pos _ he _); split; · exact le_rfl
   rw [norm_zero]; exact norm_nonneg _
end YM.QCD.Stew
