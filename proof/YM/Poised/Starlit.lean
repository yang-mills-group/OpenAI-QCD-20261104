import YM.Poised.Reeds
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
-- Slots j=0…k, p powers with p∈(0,1]. expensive charges.Caller ∃ tolerance. reserve count exactly.
def shareout (i: Fin (k+1)):ℕ:=2+i.val
lemma pool_ge(i:Fin (k+1))(p C:ℝ)(h:0≤p)(ht:p≤1)(hC:0≤C) : C*p^shareout i≤ C*p^2:=by apply mul_le_mul_of_nonneg_left _ hC; exact pow_le_pow_of_le_one h ht (by unfold shareout; omega)
-- tail weight k (not stringent than needed, if 0..k). require all through k-1 slices.
def Heritage (k:ℕ) (w:Path c B)(p C:ℝ):Prop:=
   ∃ H:Fin (k+1) → Path c B,w=∑ i,H i ∧ (∀ i,Venture f g (P:=P) (o:= wrap c b) (C*p^(shareout i)) (H i))∧(∀ i,shareout i < k →Buoyant (H i) V b (shareout i))
variable (hp:0<p)(hp':p≤1)(hC:1≤C)
abbrev pup(k:ℕ)(C:ℝ):= (k+1:ℕ)*C
include hC
lemma pup_pos (k:ℕ) : 1≤ pup k C:= by unfold pup; exact one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr (by omega)) hC -- include hC
include hp hp' hC
lemma Heritage.purse(h:Heritage P V b f g k x p C): Venture (P:=P) (o:= wrap c b) f g (pup k C*p^2) x:=by
    obtain ⟨z,hz,h,h'⟩:=h; rw [hz]; apply Venture.absorbedM _ _ _ (Venture.togetherM f g _ _ _ (fun i _=> h i)); refine (sum_le_sum (fun i _=>pool_ge i p C hp.le hp' (zero_le_one.trans hC))).trans_eq ?_; rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; unfold pup; ring
omit hp hp' hC
def central (Q:Hera.Rights su n)(C:ℝ)(d k:ℕ):= ((pup k C)^n) * mouth (1+n+pup k C) Q n d
include hC
lemma mouth_one (n' d k:ℕ) : 1≤ mouth (1+n+pup k C) Q n' d:=by
    unfold mouth; have h:=pup_pos hC k; have hv:=Q.large; apply one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) _) (one_le_mul_of_one_le_of_one_le _ hv)
    · apply one_le_pow₀; refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) ?_; linarith [Nat.cast_nonneg (α:=ℝ) n]
    apply one_le_pow₀; linarith [Nat.cast_nonneg (α:=ℝ) n] -- indent
lemma central_one (d k:ℕ) : 1≤central Q C d k:=one_le_mul_of_one_le_of_one_le (one_le_pow₀ (pup_pos hC k)) (mouth_one Q hC ..)
lemma mouth_ge (i d k:ℕ)(hi:i≤n): mouth (1+n+pup k C) Q i d ≤ mouth (1+n+pup k C) Q n d:=by
    unfold mouth; have h:=pup_pos hC k; have ht:=Q.large; gcongr <;> norm_num <;> linarith [Nat.cast_nonneg (α:=ℝ) n, Nat.cast_nonneg (α:=ℝ) i]
variable (H:TaperHol)(hk:k≤ d+1)(hA:∀ (J:Labels.Jet su)(t:ℕ),t<k→ leading t (Beacon.moment (d:=d) H b J F)=0)
variable (hf:Ease.Charm P V F) (hg:P.supBounds (wrap c b) V (framesF f∘F) t) (he:∀ i,0<f i)(hh:∀ U,F U∈layer (Faces (Site c)) a)(h:∀ k U,slots 6 k (F (gauge k U))=F U)
variable (hV:∀ i,F i∈region (limits V)) (hx: Nonwrapping V (wrap c b))(hz:100 ≤ c.val) (hr:r≤n)(hN:n ≤ P.order)(hd:d≤P.order)
include hp hp' hC hA hf hg he hh h hV hx hz hk hr hN hd
lemma christal (h0:∀ i,Mom.needed V i→ Lyre.width P (wrap c b) i≤1) (Y:Fin r→ Path c B) (hY:∀ i,Heritage P V b f g k (Y i) p C): ‖iteratedFDeriv ℝ r (framesF g ∘ lotsF F) 0 Y‖ ≤ central Q C a k *t*p^k :=by
   have hy := AnalyticBridge.VerifiedReset.flat_ok (G:=su) P V
   choose Z' hZ hE hT using hY
   let A := iteratedFDeriv ℝ r (framesF g ∘ lotsF F) 0
   rw [funext hZ]; change ‖A _‖ ≤ _; rw [A.map_sum Z']; apply (norm_sum_le ..).trans; have hp0:= hg.1
   refine le_trans (b:=∑ i:Fin r→Fin (k+1), C^r*p^k*mouth (1+n+pup k C) Q n a*t) (sum_le_sum ?_) ?_
   · intro i _; let x j:=Z' j (i j); let w(j:Fin r):=shareout (i j); by_cases hb : (∑ i,w i)<k
     · have hh' : iteratedFDeriv ℝ r (lotsF F) 0 x=0:=cancels b H V hx hz F ⟨hf.1,hV⟩ h ((hf.smooth _ hy).of_le (Nat.cast_le.mpr hd)) k hk hA x w (fun i=>by unfold w shareout; omega) hb fun j=> hT j (i j) (lt_of_le_of_lt (single_le_sum (f:=w) (fun i _=> Nat.zero_le _) (mem_univ j)) hb)
       have hxC: A x=0:=by unfold A; rw [(framesF g).iteratedFDeriv_comp_left (lots_alive F (hf.smooth _ hy)) (Nat.cast_le.mpr (hr.trans hN))]; exact (congr_arg (framesF g) hh').trans (map_zero _)
       change ‖A x‖≤ _; rw [hxC,norm_zero]; have ht:= mouth_one Q hC n a k; positivity
     push Not at hb; change ‖A x‖ ≤ _
     refine (risingW F (0:Path c B) f g Q hf hg he (by rwa [show ((0:Path c B).1)=0 from rfl,Work.G07.at_zero_increment]) (fun i hi=>⟨by simp,h0 i hi⟩) a hh hr hN (show SeatD f g _ (pup k C) from ⟨zero_le_one.trans (pup_pos hC k),fun i=>by change (∑ j, ‖orderR f g 0 i j‖)≤_; simp only [orderR,Pi.zero_apply,mul_zero,norm_zero,sum_const_zero]; exact zero_le_one.trans (pup_pos hC k)⟩) x (fun i=>C*p^(w i)) (fun _=>by positivity) (fun j=>hE _ _)).trans ?_
     rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; simp only [prod_const,card_univ,Fintype.card_fin]
     exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hp.le hp' hb) (by positivity)) (mouth_ge Q hC r a k hr) (zero_le_one.trans (mouth_one Q hC r a k)) (by positivity)) hp0
   rw [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,nsmul_eq_mul, Nat.cast_pow]; have hm:0≤ mouth (1+n+pup k C) Q n a:=zero_le_one.trans (mouth_one Q hC n a k); calc
       _=(pup k C)^r *mouth (1+n+pup k C) Q n a *t*p^k:=by unfold pup; ring
       _≤_:=(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (pup_pos hC k) hr) hm) hp0) (by positivity))
lemma sedan (hXO: Heritage P V b f g k x p C) (h0:∀ i,Mom.needed V i→ ‖x.1 i‖ ≤1∧ Lyre.width P (wrap c b) i ≤1) (htY:∀ v∈ Icc (0:ℝ) 1,Healthy P.threshold V (increment 1 (v • x.1))) (Y:Fin r→ Path c B) (hY:∀ i,Heritage P V b f g k (Y i) p C)(hd':k ≤ 2*n):
    ‖iteratedFDeriv ℝ r (framesF g ∘ lotsF F) x Y‖ ≤ (n+1:ℝ)*central Q C a k*t*p^k:=by
   let Z:=central Q C a k*t*p^k; let f':=framesF g ∘ lotsF F
   have hh':1≤pup k C:=pup_pos hC k; have hφ:= Heritage.purse P V b x f g hp hp' hC hXO
   have hZ:0 ≤ Z:=by have hx:=central_one Q hC a k; have hy:=hg.1; unfold Z; positivity
   have hu(r:ℕ)(hr : r ≤ n) (Y:Fin r→Path c B) (hY:∀ i,Heritage P V b f g k (Y i) p C) (s:ℝ) (hs:s∈Icc (0:ℝ) 1): ‖iteratedFDeriv ℝ r f' (s • x) Y‖ ≤ ((n+1-r:ℕ):ℝ)*Z:=by
       induction hr using Nat.decreasingInduction generalizing s with
       | self =>
            simp only [Nat.add_sub_cancel_left,Nat.cast_one,one_mul]
            have hT:=Venture.scaledM x f g s hφ
            change Venture _ _ (P:=P) (o:=wrap c b) _ _ at hT
            rw [Real.norm_of_nonneg hs.1] at hT
            have hU := Venture.absorbedM _ f g hT (p:=pup k C) -- name
            refine (risingW F (s • x) f g Q hf hg he (htY s hs) (fun i hi=>?_) a hh le_rfl hN (show SeatD f g _ (pup k C) from ?_) Y (fun _=>pup k C*p^2) (fun _=>by positivity) (fun i=> Heritage.purse P V b (Y i) f g hp hp' hC (hY i))).trans ?_
            · rw [show (s • x).1 i=s • x.1 i from rfl,norm_smul, Real.norm_of_nonneg hs.1]; exact ⟨mul_le_one₀ hs.2 (norm_nonneg _) (h0 i hi).1,(h0 i hi).2⟩
            · exact (hU ((mul_le_of_le_one_left (by positivity) hs.2).trans (mul_le_of_le_one_right (by positivity) (pow_le_one₀ hp.le hp')))).2
            rw [prod_const,card_univ,Fintype.card_fin,mul_pow, ← pow_mul]; unfold Z central; have hx:= mouth_one Q hC n a k; have hh':= hg.1
            calc
              _=pup k C^n*mouth (1+n+pup k C) Q n a*t*p^(2*n):=by ring
              _≤_:=mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hp.le hp' hd') (by positivity)
       | of_succ j hj ih =>
           have ha : ∀ i : Fin (j+1), Heritage P V b f g k ((Fin.cons x Y : Fin (j+1) → Path c B) i) p C := Fin.cases (by simpa using hXO) (fun i=> by simpa using hY i)
           have hX t (hx : t∈Icc (0:ℝ) 1): ContDiffAt ℝ (↑(j+1:ℕ)) f' (t • x) := sighted (t • x) g F hf (htY t hx) ((show j+1 ≤ n from hj).trans hN)
           have H1:= Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun t:ℝ=>iteratedFDeriv ℝ j f' (t • x) Y) (fun t hx=> (Heir.along_deriv x Y t (hX t hx)).hasDerivWithinAt) (fun t hx=> ih (Fin.cons x Y) ha t hx) (convex_Icc ..) (show (0:ℝ)∈ Set.Icc (0:ℝ) 1 by simp) hs
           rw [zero_smul,sub_zero,Real.norm_of_nonneg hs.1] at H1
           have hh' : ‖iteratedFDeriv ℝ j f' 0 Y‖ ≤ Z := christal F P V b f g Q hp hp' hC H hk hA hf hg he hh h hV hx hz (Nat.le_of_lt hj) hN hd (fun i hi=>(h0 i hi).2) Y hY
           refine ((norm_le_norm_sub_add _ _).trans (add_le_add (H1.trans (mul_le_of_le_one_right (by positivity) hs.2)) hh')).trans_eq ?_; rw [show n+1-j=n+1-(j+1)+1 by omega,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
   have he:= hu r hr Y hY 1 (by simp); rw [one_smul] at he
   refine he.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le ..)) hZ).trans_eq ?_); unfold Z; push_cast; ring
end Pipes
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Pipes.sedan
