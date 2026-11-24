import YM.Poised.Prong
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Dolphin
/-!
# All-rank taper
Exact exponent through joint degrees. Permit delta floors for each assigned aperture.Vectors include bar/psi/F rank, any arity. Actual path-origin price.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n m r:ℕ}{c:Side}
namespace Pipes
open Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource MultiNext.SignedSource.Lyre
variable (F:Grid c→ Lat.Fields c 6) (P:BudgetPoint) (V:Support c) (b:Cover) [Fintype B] (x: Path c B)
variable (f : Faces (Site c) → ℝ) (g:B→ℝ) (Q:Hera.Rights su n){p C t:ℝ}
variable (R z:ℝ)(hR:1≤R)(hy:0<z)(hz:Healthy P.threshold V (increment 1 x.1))(hx:∀ e,Mom.needed V e → ‖x.1 e‖≤ 1 ∧ width P (wrap c b) e ≤1)
variable (hp:P.supBounds (wrap c b) V (framesF f∘ F) t) (hc:Ease.Charm P V F)(he:n ≤ P.order)(hk:k+1 ≤ n)(ht:∀ U,F U∈ layer (Faces (Site c)) a)(hf:∀ i,0<f i) {Y W:Fin k→ Path c B}
local notation "T"=> framesF g ∘ lotsF F
set_option quotPrecheck false
local notation "L"=> mouth (1+n+R) Q n a
variable (y:Path c B)(hr:∀ s∈Set.Icc (0:ℝ) 1,Healthy P.threshold V (increment 1 (x+s • y).1))(hu:∀ s∈Set.Icc (0:ℝ) 1,∀ e,Mom.needed V e → ‖(x+s • y).1 e‖ ≤ 1)(hS:∀ s∈Set.Icc (0:ℝ) 1,SeatD f g (x+s • y).2 R)
variable (hYP: Venture f g (P:=P) (o:=wrap c b) z y)
-- mouth n vs r
include hR
lemma bite (n' :ℕ)(h:n'≤ n): mouth (1+n+R) Q n' a ≤ L:= by unfold mouth; have he:=Q.large; gcongr <;> norm_num <;> linarith [Nat.cast_nonneg (α:=ℝ) n] -- local notation
include hy hp hc he hr hu hS hk hYP ht hf hx
variable (hw :1 ≤ p)(hYP':∀ i, Venture f g (P:=P) (o:=wrap c b) p (Y i))
include hw hYP'
lemma navigates : ‖iteratedFDeriv ℝ k T (x+y) Y - iteratedFDeriv ℝ k T x Y‖ ≤ z*p^n*L*t :=by
   let f' := T
   let q(s:ℝ):= x+s • y; let Xs:= Set.Icc (0:ℝ) 1
   have h t (h:t∈Xs): ContDiffAt ℝ (↑(k+1:ℕ)) f' (q t):= sighted _ _ F hc (hr t h) (hk.trans he)
   have hh(t:ℝ)(he:t∈Xs) : HasDerivAt (fun s:ℝ=> iteratedFDeriv ℝ k f' (q s) Y) (iteratedFDeriv ℝ (k+1) f' (q t) (Fin.cons y Y)) t:=by
       rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero,Fin.tail_cons]; exact (ContinuousMultilinearMap.apply ℝ _ _ Y).hasFDerivAt.comp_hasDerivAt t (((h t he).differentiableAt_iteratedFDeriv (m:=k) (Nat.cast_lt.mpr (Nat.lt_succ_self _))).hasFDerivAt.comp_hasDerivAt t (show HasDerivAt q y t from by unfold q; simpa using ((hasDerivAt_id' t).smul_const y).const_add x))
   have hB:t≥0:=hp.1; have hC:= Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun s:ℝ=> iteratedFDeriv ℝ k f' (q s) Y) (fun t ht=>(hh t ht).hasDerivWithinAt) (C:=z*p^n*L*t) ?_ (convex_Icc ..) (show 0∈ Xs by simp [Xs]) (show 1∈ Xs by simp [Xs]); swap
   · intro s hs; let f1 : Fin (k+1)→ℝ:=Fin.cons z (fun _:Fin k=>p); have hh :∀ i, Venture f g (P:=P) (o:=wrap c b) (f1 i) ((Fin.cons y Y : Fin (k+1)→Path c B) i):=Fin.cases (by simpa only [Fin.cons_zero,f1]) (fun i=>by simpa only [Fin.cons_succ,f1] using hYP' i)
     apply (risingW F (q s) f g Q hc hp hf (hr _ hs) (fun e h=>⟨hu s hs e h, (hx _ h).2⟩) a ht hk he (hS s hs) (Fin.cons y Y) f1 (Fin.cases (by simpa only [f1,Fin.cons_zero]) (fun i=>by simpa only [Fin.cons_succ,f1] using zero_lt_one.trans_le hw)) hh).trans; rw [Fin.prod_univ_succ]; simp only [f1,Fin.cons_zero,Fin.cons_succ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
     let C:=(1+(n:ℝ)+R); have hg:0 ≤ mouth C Q (k+1) a:=by unfold mouth C; have h:=Q.large; positivity
     exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hw (Nat.le_of_lt hk)) hy.le) (bite Q R hR _ hk) hg (by positivity)) hB
   simpa only [f',q,zero_smul,add_zero,one_smul,sub_zero,norm_one,mul_one] using hC
omit hr hu hS hYP
include hz hx W
lemma alters (hv:∀ i,Venture f g (P:=P) (o:=wrap c b) z (W i-Y i))(h:z≤p)(hC:SeatD f g x.2 R):
    ‖iteratedFDeriv ℝ k T x W-iteratedFDeriv ℝ k T x Y‖ ≤ (2:ℝ)^n*(z*p^n*L*t):=by
    let V':=iteratedFDeriv ℝ k T x; let Z'(s:Finset (Fin k)):= V' (s.piecewise (W-Y) Y)
    let C:=z*p^n*L*t; have hK:= Nat.le_of_lt hk; have hZ:=hp.1; let O:ℝ:=mouth (1+n+R) Q k a; have hO:0 ≤ O:=by unfold O mouth; have hx:=Q.large; positivity; -- indentation
    have hΦ : 0≤ C:=by unfold C; have hg: O≤L := bite Q R hR _ hK; have h0:= hO.trans hg; positivity
    have h (s:Finset (Fin k))(hs:s≠∅): ‖Z' s‖ ≤ C:=by
        obtain ⟨i,hi⟩:= Finset.nonempty_iff_ne_empty.mpr hs
        let f':=Function.update (fun _:Fin k=> p) i z
        have hF:∏ t,f' t=z * ∏ t∈Finset.univ.erase i,f' t:= by rw [← prod_erase_mul _ _ (Finset.mem_univ i),show f' i=z from update_self ..,mul_comm _ z]
        refine (risingW F x f g Q hc hp hf hz hx a ht hK he hC _ f' (fun j=>by unfold f'; rw [Function.update_apply]; split <;> linarith) (fun j=> ?_)).trans ?_
        · by_cases he':j=i
          · subst j; simp [hi,Finset.piecewise,f']; exact hv i
          unfold f'; rw [update_of_ne he']; by_cases h':j∈ s<;> simp [h',Finset.piecewise]; exact Venture.absorbedM _ f g (hv j) h; exact hYP' j
        have hp: ∏ j∈ Finset.univ.erase i,f' j= p^(k-1):= (Finset.prod_congr rfl (g:=fun _=> p) (fun j h=>update_of_ne (by simpa using! (Finset.mem_erase.mp h).1) ..)).trans (by simp)
        rw [hF,hp]; unfold C; exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hw (by omega)) hy.le) (bite Q R hR _ hK) hO (by positivity)) hZ
    change ‖V' W - V' Y‖ ≤ _; rw [show V' W-V' Y = ∑ j∈Finset.univ.erase ∅, Z' j from calc
     V' W-V' Y = ∑ j,Z' j-V' Y:=by rw [← V'.map_add_univ (W-Y) Y]; simp
     _ = _ := by rw [← sum_erase_add _ Z' (Finset.mem_univ ∅)]; unfold Z'; simp only [Finset.piecewise_empty,add_sub_cancel_right]]
    refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=>C) (fun j hj=>h _ (Finset.mem_erase.mp hj).1)).trans ?_)
    simp only [Finset.sum_const,nsmul_eq_mul]; refine mul_le_mul_of_nonneg_right ?_ hΦ
    have he : (Finset.univ.erase (∅:Finset (Fin k))).card ≤ 2^k:= by simp
    exact_mod_cast he.trans (Nat.pow_le_pow_right (by norm_num) hK)
end Pipes
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Pipes.alters
