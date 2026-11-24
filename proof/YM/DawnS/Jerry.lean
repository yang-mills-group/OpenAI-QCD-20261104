import YM.DawnS.Winks
import Mathlib.Algebra.MvPolynomial.Funext
/-! Spatial-polynomial strictness. Full measures detect continuous rays. Polynomial cancellation of visible helicity cannot happen only positive radial: simultaneous extension at opposite directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix
local notation "K"=> timeAxis
local notation "I₀"=>Complex.I
local notation "P"=> RingS
local notation "Y"=>Vertex
local notation "Ω"=>muS
variable {d:ℕ}
section pol
open MvPolynomial
noncomputable def digit(p:chit d):Fin 3→₀ℕ:= Finsupp.equivFunOnFinite.symm fun i=> Massive.UV.power p.val i.castSucc
lemma digit_inj (d:ℕ): Injective (digit (d:=d)):=by
    intro p q h; apply Subtype.ext; apply Subtype.ext; ext1 i; refine Fin.lastCases ?_ (fun j=>?_) i; apply Fin.ext; exact (p.property).trans q.property.symm; apply Fin.ext; exact DFunLike.congr_fun h j
lemma countV (l: List (Fin 3))(w:Fin 3→ℂ): (l.map w).prod=∏ i, w i ^l.count i:=by
    induction l with
    | nil=> simp
    | cons a l ih=> rw [List.map_cons,List.prod_cons,ih]; simp_rw [List.count_cons,pow_add]; rw [prod_mul_distrib]; rw [Finset.prod_eq_single_of_mem (f:=fun i:Fin 3=>w i^(if a==i then 1 else 0)) a (mem_univ _)]; simp[mul_comm]; intro b _ h; simp[h, h.symm]
lemma digitV (p:chit d)(i:Fin 3) : (listP p).count i=digit p i:=by
    unfold digit; have h := Arise.spine_code p.val i.castSucc; rw [running] at h; unfold toAxes at h; rw[List.count_map_of_injective _ _ (Fin.castSucc_injective _)] at h; exact h
noncomputable def wSig(b:Bool):ℂ:=if b then -I₀ else I₀
lemma scoreG(p:chit d)(b:Bool)(r:ℝ)(s:PR):gleam b p r s = wSig b ^(listP p).length * MvPolynomial.eval (fun i:Fin 3=> (↑(((s.1 /r) • s.2.val : Vertex) i) :ℂ)) (monomial (digit p) 1):=by
      let l:= listP p; let R:= s.1/r; let u:=s.2
      let v(i:Fin 3):ℂ:= (↑(((R • ↑u : Vertex)) i)); rw[eval_monomial,one_mul];
      have h: Finsupp.prod (digit p) (fun i n=> v i^n)=(l.map v).prod:=by
             rw [countV l v]; simp_rw [show ∀ i,l.count i=digit p i from digitV p]; unfold Finsupp.prod; apply Finset.prod_subset (Finset.subset_univ _); exact fun i _ hi=> by simp[show digit p i=0 from Finsupp.notMem_support_iff.mp hi]
      change (↑R:ℂ)^ _ * (wSig b^_ * (stepTheta s.2 (listP p):ℂ))= _*Finsupp.prod (digit p) (fun i n=> v i^n); rw[h]
      have he:(l.map v).prod=(↑R:ℂ)^l.length*(stepTheta u l:ℂ):=by
          suffices hx:∀ l:List (Fin 3), (l.map v).prod=(↑R:ℂ)^l.length*(stepTheta u l:ℂ) from hx l
          intro l; induction l with
          | nil=>simp [stepTheta]
          | cons a l ih=> rw[List.map_cons,List.prod_cons,ih, List.length_cons, pow_succ, show stepTheta u (a::l)=thetaS (base a) u*stepTheta u l from (by simp[stepTheta])]; push_cast; rw[ray]; unfold v; push_cast; simp; ring
      rw [he]; change ↑R^_* (wSig b^l.length * (stepTheta u l:ℂ))=wSig b^l.length*_; ring
lemma wSig_ne(b:Bool):wSig b≠0:=by cases b <;> simp[wSig]
variable (b:Bool)(r:ℝ)(hr:0<r)(q:chit d→ℂ)
include hr
lemma declares(h:∀ x:PR,∑ i,q i*gleam b i r x=0):∀ i,q i=0:=by
     let W(i:chit d):MvPolynomial (Fin 3) ℂ:= C (q i * wSig b ^(listP i).length)*(monomial (digit i) 1); let PT:=∑ i,W i
     let U:=Set.range ((↑) : ℝ→ℂ); have he : U.Infinite:= infinite_range_of_injective Complex.ofReal_injective
     have hp:PT=0:=by
          apply MvPolynomial.funext_set (fun _=>U) (fun _=>he); intro x hx; choose z hz using fun i=> hx i (Set.mem_univ _); let v : Vertex:=WithLp.toLp 2 z
          have ht:∃ x:PR,v=(x.1/r)•(x.2: Vertex):=by
                by_cases hv: v=0; · exact ⟨(0,Classical.choice inferInstance), (by simp[hv])⟩
                have he:0<‖v‖:=norm_pos_iff.mpr hv
                refine ⟨(‖v‖*r,⟨‖v‖⁻¹ • v,(by rw[mem_sphere_zero_iff_norm,norm_smul,Real.norm_of_nonneg (inv_pos.mpr he|>.le),inv_mul_cancel₀ he.ne'])⟩),?_⟩; dsimp only; rw[mul_div_cancel_right₀ _ hr.ne', smul_smul,mul_inv_cancel₀ he.ne',one_smul]
          obtain ⟨t,hV⟩:=ht; unfold PT W; simp_rw[map_sum,map_mul,eval_C,map_zero]
          have hE:x=(fun i=> ((↑(((t.1/r) • t.2.val : Vertex) i)):ℂ)):=by rw[← hV]; exact funext fun i=> (hz i).symm
          rw[hE]; refine Eq.trans ?_ (h t); apply Finset.sum_congr rfl; intro i _; rw [scoreG, mul_assoc]
     intro i; have he := congr_arg (MvPolynomial.coeff (digit i)) hp; simp only [PT,W,C_mul_monomial,MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero] at he; simp [Function.Injective.eq_iff (digit_inj _),wSig_ne] at he; exact he
end pol
end YM.DawnS
