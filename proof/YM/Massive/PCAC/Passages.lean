import YM.Massive.PCAC.Bias
/-! Pushing derivatives/contractions. No spin identity need here. `rear`=propagated insertion lap kernel matrix in actual code downstream, formula here for one pair old. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass.Ward
open Function Finset Module NormedSpace
open scoped BigOperators Topology Matrix Classical
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C]
open Kit
variable [DecidableEq B]
variable (Q:Matrix B A ℂ)
-- Gradient of coat gaussian lives on such near+far combinations.
private lemma atLobby (a:A) : lobby (coat Q) (Sum.inl a)= -(∑ b:B,Q b a • lobby (coat Q) (Sum.inr b)):=by
    have hh(u:A⊕B): coat Q u (.inl a)= -∑ b:B,Q b a * coat Q u (.inr b):=by rw [blocks]; cases u with | inl i=> simp [Matrix.mul_apply]; exact sum_congr rfl fun j _=> mul_comm .. | inr i=> simp [Matrix.one_apply]
    unfold lobby; simp_rw [hh,neg_smul,sum_smul,smul_sum,mul_smul,sum_neg_distrib]; rw [sum_comm] -- syntax Qᴴ i weird
private lemma atStation (a:A): station (coat Q) (.inl a)= -(∑ b:B, (Qᴴ) a b • station (coat Q) (.inr b)):=by
    have hh(u:A⊕B): coat Q (.inl a) u= -(∑ b:B,(Qᴴ) a b* coat Q (.inr b) u):=by rw [blocks]; cases u <;> simp [Matrix.mul_apply,Matrix.one_apply] -- sum neg
    unfold station; simp_rw [hh,neg_smul,sum_smul,smul_sum,mul_smul,sum_neg_distrib]; rw [sum_comm]
-- formula integrability on Grass marginal no jac assumption
lemma kernelP(a:A): vary (beforeK B (.inl a)) (kernel Q)= -(∑ b:B,Q b a • vary (besideK A (.inl b)) (kernel Q)):=by
    unfold kernel; simp only [beforeK,besideK,Sum.map_inl,varyP',atLobby Q a]; rw [mul_neg,mul_sum]; simp only [mul_smul_comm]
lemma kernelB(a:A): vary (beforeK B (.inr a)) (kernel Q)= -(∑ b:B,(Qᴴ) a b • vary (besideK A (.inr b)) (kernel Q)):=by
    unfold kernel; simp only [beforeK,besideK,Sum.map_inr,varyB',atStation Q a]; rw [mul_neg,mul_sum]; simp only [mul_smul_comm,smul_neg,neg_neg,sum_neg_distrib]

lemma transferD (i:Pairs A)(x:Dirac A)(s:B→Pairs B)(v:B→ℂ)(h:vary (beforeK B i) (kernel Q)= -(∑ b:B,v b • vary (besideK A (s b)) (kernel Q))): sheath 1 Q (vary i x)= ∑ b:B,v b • vary (s b) (sheath 1 Q x):=by
    let k:=kernel Q; let p:= near A B x; let y:=p*k
    have hv(b:B): vary (besideK A (s b)) y= grade p * vary (besideK A (s b)) k:=by unfold y p; rw [vary_mul,ignores_near, zero_mul,zero_add]
    have hA:vary (beforeK B i) y= near A B (vary i x)*k - ∑ b:B, v b • vary (besideK A (s b)) y:=by
        unfold y; rw [vary_mul, show vary (beforeK B i) p = _ from near_d i x, (show vary (beforeK B i) k= _ from h)]; rw [mul_neg,sub_eq_add_neg,mul_sum]; simp_rw [mul_smul_comm]; -- reflect hv
        change _= _+ -(∑ b:B,v b • vary (besideK A (s b)) y); simp_rw [hv]; rfl -- k defeq
    rw [crease,crease]; change _= ∑ b:B,v b • vary (s b) (marginal A B y); simp_rw [← lateral,← map_smul]; rw [← map_sum]; apply sub_eq_zero.mp; rw [← map_sub]; simp_rw [show ∀ b:B, vary (besideK A (s b)) (v b • y)=v b • vary (besideK A (s b)) y from fun _=> map_smul _ _ _]; exact (show _ from ((by rw [← hA]; exact vanishes i y) : marginal A B (near A B (vary i x)*k-∑ b:B,v b • vary (besideK A (s b)) y) = 0))
lemma pair_pass (a c:A)(x:Dirac A): sheath 1 Q (pairD a c x) = ∑ i:B,∑ j:B,(Q i a*(Qᴴ) c j) • pairD i j (sheath 1 Q x):=by
    let y:=vary (Sum.inr c) x; rw [show sheath 1 Q (pairD a c x)= _ from transferD Q (Sum.inl a) y Sum.inl (fun i=>Q i a) (kernelP Q a), show sheath 1 Q y= _ from transferD Q (Sum.inr c) x Sum.inr ((Qᴴ) c) (kernelB Q c)]; simp_rw [map_sum,map_smul,smul_sum,smul_smul]; rfl
end YM.QCD.Grass.Ward
#print axioms YM.QCD.Grass.Ward.pair_pass
