import YM.Massive.PCAC.Bead
import YM.QCD.Creek.Horizon
import YM.QCD.Cove.Wave
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
open Onsite Tide Creek QCD.Cove
open Finset
open scoped Kronecker
variable (a b:Flavor F)(u: Site c)(X:Spike)
local notation "Φ"=> localF u X a b
-- compatible on marks *at sites*; include Berezin null as well. Payload radius C non/post μ unweighted
structure Veins (v:Site c) (D: Lat.Fields c N→L[ℂ]Lat.Fields c N) (C:ℝ): Prop where
 product (x y:Fields c N) : D (x*y)= D x*y+x*D y
 grade (x:Fields c N): D (Grass.grade x)=Grass.grade (D x)
 empty_set (Y:Support c)(h:v∉ Y)(x:Fields c N) (hv: x∈region (limits Y)): D x=0
 localize (Y:Support c)(x:Fields c N)(hv:x∈region (limits Y)): D x∈region (limits Y)
 reflects(x:Fields c N)(j: Frame c):D (slots N j x)=slots N j (D x)
 law (x:Fields c N): ber _ (D x)=0
 nn : 0 ≤ C
 price (x:Fields c N)(t:ℝ)(ht:0<t):load (fun _=>t) (D x) ≤ C*load (fun _=>t) x
noncomputable def ore (v:Site c)(q:Bool)(a b:Flavor F)(T:Spike) : Lat.Fields c F→L[ℂ] Lat.Fields c F:= (applyMark q (localF v T a b)).toContinuousLinearMap
lemma positionQ (q:Bool)(x:Lat.Fields c F) (Y:Support c)(hv:x∈region (limits Y))(h:u∉Y): ore u q a b X x=0:=by
   change applyMark q Φ x= _; cases q
   · rw [column]; apply sum_eq_zero; intro i hi; apply sum_eq_zero; intro j hj; by_cases h1:i.1.1=u
     · have hz: vary (Sum.inl i) x=0:= lock (Sum.inl i) hv fun he=> h (h1 ▸ (show i.1.1∈Y from (mem_filter.mp he).2)); change Φ i j • (atom (Sum.inl j)* vary (Sum.inl i) x)=0; rw [hz,mul_zero,smul_zero]
     rw [focusL a b u X i j h1,zero_smul]
   rw [row]; apply sum_eq_zero; intro i hi; apply sum_eq_zero; intro j hj; by_cases h1:j.1.1=u
   · have hz:vary (Sum.inr j) x=0:= lock (Sum.inr j) hv fun he=> h (h1 ▸ (show j.1.1∈ Y from (mem_filter.mp he).2)); change Φ i j • (atom (Sum.inr i)*vary (Sum.inr j) x)=0; rw [hz,mul_zero,smul_zero]
   rw [focusR a b u X i j h1,zero_smul]
lemma positionP (q: Bool)(x:Lat.Fields c F) (Y:Support c)(hv:x∈region (limits Y)): ore u q a b X x∈ region (limits Y):=by
   by_cases h:u∈Y; swap; · rw [positionQ a b u X q x Y hv h]; exact Subalgebra.zero_mem _
   change applyMark q Φ x ∈ _; cases q
   · rw [column]; apply Subalgebra.sum_mem; intro i _; apply Subalgebra.sum_mem; intro j _; by_cases h1:j.1.1=u
     · exact (region _).smul_mem ((region _).mul_mem (marked (Sum.inl j) _ (mem_filter.mpr ⟨mem_univ _,show j.1.1∈ Y from h1.symm ▸ h⟩)) (preserves (Sum.inl i) hv)) _
     rw [focusR a b u X _ _ h1,zero_smul]; exact Subalgebra.zero_mem _
   rw [row]; apply Subalgebra.sum_mem; intro i _; apply Subalgebra.sum_mem; intro j _; by_cases h1:i.1.1=u
   · exact (region _).smul_mem ((region _).mul_mem (marked (Sum.inr i) _ (mem_filter.mpr ⟨mem_univ _,show i.1.1∈Y from h1.symm ▸ h⟩)) (preserves (Sum.inr j) hv)) _
   rw [focusL a b u X _ _ h1,zero_smul]; exact Subalgebra.zero_mem _
lemma L_grade (q:Bool)(T:Sour A)(x:Dirac A): applyMark q T (grade x)=Grass.grade (applyMark q T x):=by
     have hx(i j:Pairs A) : gen i j (grade x)=Grass.grade (gen i j x):= show atom j * vary i _=grade (atom j*vary i x) from by rw [show vary i (grade x)= -Grass.grade (vary i x) from anti ..,map_mul,grade_atom,neg_mul,mul_neg]
     cases q<;> simp only [column,row,map_sum,map_smul,hx]
lemma L_one (q:Bool)(T:Sour A):applyMark q T 1=0:=by cases q<;> simp [column,row,gen_one]
lemma L_slots (q:Bool)(X:Sour A)(Y:Sour A)(D:Sour A)(h:Commute X D)(hY:Commute D Y.transpose)(x: Dirac A): applyMark q D (adapter X Y x)=adapter X Y (applyMark q D x):=by
    let f:=adapter X Y; let g:=applyMark q D; suffices hh:∀ i:Pairs A,g (f (atom i))=f (g (atom i)) by
       have h (S:List (Pairs A)):g (f (S.map atom).prod)= f (g (S.map atom).prod):=by
            induction S with
            | nil=> simp [f,g,L_one]
            | cons i s ih=> simp only [List.map_cons,List.prod_cons,map_mul]; unfold g; rw [LMark q,LMark q,map_add,map_mul,map_mul]; exact congr_arg₂ (·+·) (congr_arg (·*_) (hh i)) (congr_arg (_*·) ih)
       have h (s:Finset (Pairs A)):g (f (mono s))=f (g (mono s)):=by obtain ⟨w,-,-,hp⟩:= expression s; rw [hp]; simpa only [List.map_ofFn] using h (List.ofFn w)
       change g (f x)= f (g x); rw [← write x]; simp_rw [map_sum,map_smul,h]
    have H (p:Sour A)(D:Sour A)(x:A→ Dirac A)(i:A) : ∑ j,p i j • ∑ k,D j k • x k= ∑ j,(p*D) i j • x j:=by
        simp_rw [smul_sum, smul_smul,Matrix.mul_apply,sum_smul]; rw [sum_comm]
    intro i; cases q
    · rcases i with i|i
      · change applyMark _ _ (adapter X Y (psi i)) =adapter X Y (applyMark _ _ (psi i)); rw [adapt_psi,leftP,map_sum,map_sum]; simp_rw [map_smul,adapt_psi,leftP,H,h.eq]
      change applyMark _ _ (adapter X Y (bar i))=adapter X Y (applyMark _ _ (bar i)); rw [adapt_bar,passB,map_zero,map_sum]; simp_rw [map_smul,passB,smul_zero,sum_const_zero]
    rcases i with i|i
    · change applyMark _ _ (adapter X Y (psi i))=adapter X Y (applyMark _ _ (psi i)); rw [adapt_psi,passP,map_zero,map_sum]; simp_rw [map_smul,passP,smul_zero,sum_const_zero]
    change applyMark _ _ (adapter X Y (bar i))=adapter X Y (applyMark _ _ (bar i)); rw [adapt_bar,leftB,map_sum,map_sum]; simp_rw [map_smul,adapt_bar,leftB]; change (∑ j,Y i j • ∑ k,D.transpose j k • bar k)= ∑ j,D.transpose i j • ∑ k,Y j k • bar k; rw [H,H]
    have hh:= congr_arg Matrix.transpose hY.eq; rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose] at hh; rw [hh]
lemma veinColor (q: Bool)(x:Lat.Fields c F) (T: Frame c): ore u q a b X (slots F T x) = slots F T (ore u q a b X x):=by
    let t:= Lat.rotates F T; have hp : Commute t Φ := (commute_zone u T |>.symm).mul_right (commuteSpin a b X T); change applyMark q Φ _= slots F T _; apply L_slots q t (star t).transpose Φ hp; rw [Matrix.transpose_transpose]; have hV: star t*t=1:=(Lat.rotates_law F T).1; have hX:t*star t=1:=(Lat.rotates_law F T).2; unfold Commute SemiconjBy; calc
         _=star t*t*Φ*star t:=by rw [hV,one_mul]
         _=star t*Φ:=by rw [mul_assoc (star t) t Φ,hp.eq,mul_assoc,mul_assoc,hX,mul_one]
lemma veinTicket (q:Bool)(D:Sour A)(v:ℝ)(ht:0<v)(x:Dirac A): load (fun _=>v) (applyMark q D x) ≤ (∑ i:A,∑ j:A,‖D i j‖)*load (fun _=>v) x:=by
    let g: Pairs A→ℝ:=fun _=>v
    have hh(i j:Pairs A): load g (gen i j x) ≤ load g x:=by
         change load g (atom j*vary i x) ≤_; refine (load_mul g _ _).trans ?_; rw [load_atom g (fun _=> ht)]; change v*load g (vary i x)≤_; exact (mul_le_mul_of_nonneg_left (fee g (fun _=>ht) i x) ht.le).trans_eq (mul_inv_cancel_left₀ ht.ne' _)
    have H (f r:A→A→Pairs A): load g (∑ i:A,∑ j:A,D i j • gen (f i j) (r i j) x)≤(∑ i,∑ j,‖D i j‖)*load g x:=by
         apply le_trans (load_sum ..); rw [sum_mul]; apply sum_le_sum; intro i _; apply le_trans (load_sum ..); rw [sum_mul]; apply sum_le_sum; intro j _; rw [load_scale]; exact mul_le_mul_of_nonneg_left (hh _ _) (norm_nonneg _)
    cases q
    · rw [column]; exact H (fun i _=>.inl i) (fun _ j=>.inl j)
    rw [row]; exact H (fun _ j=>.inr j) (fun i _=>.inr i)
open scoped Kronecker
noncomputable def veinFare(X:Spike):ℝ:= ∑ i:Lat.Fiber,∑ j:Lat.Fiber,‖Lat.wave X i j‖
lemma veinSum : (∑ i: Modes c F,∑ j: Modes c F,‖Φ i j‖)= veinFare X:=by
    change (∑ i: (Site c×Lat.Fiber) × Flavor F, ∑ j:(Site c×Lat.Fiber) × Flavor F, ‖Φ i j‖)= _
    conv_lhs=> rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
    rw [sum_eq_single u]; swap
    · intro x _ hx; apply sum_eq_zero; intro y _; apply sum_eq_zero; intro w _; apply sum_eq_zero; intro v hv; rw [focusL a b u X _ _ hx,norm_zero]
    rotate_right; · simp
    apply sum_congr rfl; intro v hv; rw [sum_eq_single a]; swap
    · intro x _ hx; apply sum_eq_zero; intro j hj; unfold localF; rw [zleft]; simp [flavorW,spot,hx]
    rotate_right; · simp
    rw [Fintype.sum_prod_type,Fintype.sum_prod_type,sum_eq_single u]; swap
    · intro x _ hx; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro k _; rw [focusR a b u X _ _ hx,norm_zero]
    rotate_right; · simp
    apply sum_congr rfl; intro j _; rw [sum_eq_single b]; swap
    · intro i _ hi; unfold localF; rw [zleft]; simp [flavorW,spot,hi]
    rotate_right; · simp
    unfold localF; rw [zleft]; simp [flavorW,spot,onSpin,rides]
lemma veinLaw (q: Bool)(h:a≠b): Veins u (ore u q a b X) (veinFare X):=by
   refine ⟨fun i j=> LMark q _ _ _,fun i=> L_grade q _ _,fun Y h x hv=> positionQ a b u X q x Y hv h,fun Y x hv=>positionP a b u X q x Y hv,fun x j=>veinColor a b u X q x j,fun x=> (integrated q Φ x).trans (by rw [near_trace a b X u h,zero_mul]),sum_nonneg fun i _=> sum_nonneg fun i _=>norm_nonneg _,fun x t ht=>?_⟩
   rw [← veinSum a b u X]; exact veinTicket q _ _ ht _
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.veinLaw
