import YM.Massive.PCAC.Mixed
import YM.QCD.Lattice.Stability
/-! # Single-site flavor/spin projectors, set localization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
variable (P:Flight j k)(K:KernelChoices)(h:f.val=c.val*P.L.val) (β w:ℝ)(hk:P.patch.Branches K su)
open Onsite Tide
open Finset
open scoped Kronecker
variable (a b:Flavor F)(u v: Site c) (X:Spike)
local notation "f'"=> flavorW X a b c
/-- site projector. -/
def zone (F:ℕ)(p:Site c):Sour (Modes c F):= Matrix.diagonal fun i=> if i.1.1=p then 1 else 0
lemma cells : ∑ p:Site c, zone F p =1 :=by
    ext i j; rw [Matrix.sum_apply]; simp [zone,Matrix.diagonal_apply,Matrix.one_apply]
lemma zstar (p:Site c): star (zone F p)=zone F p:=by unfold zone; rw [Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose]; ext i j; simp [Matrix.diagonal_apply,apply_ite star]
lemma zleft (i j:Modes c F)(X:Sour (Modes c F))(p:Site c) : (zone F p*X) i j=if i.1.1=p then X i j else 0:=by unfold zone; rw [Matrix.diagonal_mul,ite_mul,zero_mul,one_mul]
lemma zright (i j:Modes c F)(X:Sour (Modes c F))(p:Site c) : (X*zone F p) i j=if j.1.1=p then X i j else 0:=by unfold zone; rw [Matrix.mul_diagonal,mul_ite,mul_one,mul_zero]
lemma focused (i j:Modes c F)(h: i.1.1≠j.1.1) : f' i j=0:=by unfold flavorW onSpin rides; simp [h]
lemma commute_here: Commute (zone F u) f':=by unfold Commute SemiconjBy; ext i j; rw [zleft,zright]; by_cases h:i.1.1=j.1.1; rw [h]; simp only [focused a b X i j h, ite_self]
lemma commuteSpin(T: Frame c): Commute (rotates F T) f':=by
   unfold rotates copies flavorW; change Kit.choir F (siteRot T)*(onSpin c X ⊗ₖ spot a b) = _ -- Commute def
   change Kit.choir F (siteRot T)*(onSpin c X ⊗ₖ spot a b)= (onSpin c X ⊗ₖ spot a b)*Kit.choir F (siteRot T)
   rw [Sway.choir_in]; unfold Matrix.kronecker; rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,(rot_spin ..).eq]; simp
lemma commute_zone(T:Frame c): Commute (zone F u) (rotates F T):=by
   unfold Commute SemiconjBy; ext i j; rw [zleft,zright]; by_cases h:i.1.1=j.1.1; rw [h]; simp only [rotates,copies,Matrix.blockDiagonal_apply,siteRot,rr,Equiv.refl_apply]; simp [h]
noncomputable def localF (p:Site c)(X:Spike)(a b:Flavor F):= zone F p * flavorW X a b c
lemma local_sum : ∑ p:Site c,localF p X a b=f':=by unfold localF; rw [← sum_mul, cells,one_mul]
lemma near_trace (p:Site c)(he:a≠b) : Matrix.trace (localF p X a b)=0:=by
    unfold localF Matrix.trace; apply sum_eq_zero; intro i _; unfold Matrix.diag; rw [zleft]; rw [show flavorW X a b c i i=0 from ?_]; rw [ite_self]; change _* (if i.2=a ∧ i.2=b then (1:ℂ) else 0)=0; rw [if_neg (show ¬(i.2=a∧i.2=b) from fun h=> he (h.1.symm.trans h.2)),mul_zero]
lemma focusR (i j:Modes c F)(he:j.1.1≠u): localF u X a b i j=0:=by unfold localF; rw [(commute_here a b u X).eq, zright i j,if_neg he]
lemma focusL(i j:Modes c F)(he:i.1.1≠u): localF u X a b i j=0:=by unfold localF; rw [zleft,if_neg he]
lemma focus_slot (i j:Modes c F)(he:i.1.1≠u) : localF u X a b i j=0 ∧ localF u X a b j i=0:=⟨focusL a b u X _ _ he,focusR a b u X _ _ he⟩
lemma mark_site (D: Set (Site c))(he:u∉D)(y:Stud c F)(hv: Uses D y)(g: Bool)(U:Grid c): applyMark g (localF u X a b) (y U)= 0:=by
    let Z:=localF u X a b; obtain ⟨p,hp⟩:= hv.2 U; rw [hp]; let V:=pass (RP.setDay D) p
    have hh(i:Modes c F)(hk:i.1.1=u): vary (.inl i) V=0∧vary (.inr i) V=0:=by
         let B: Pairs (RP.Deck D F)→ Pairs (Modes c F):= Sum.map (RP.setDay D) (RP.setDay D)
         have h (j:RP.Deck D F): i ≠ RP.setDay D j :=by rintro ht; have hz : i.1.1 ∈ D:= congr_arg (fun i:Modes c F=> i.1.1) ht ▸ j.1.1.property; exact he (hk ▸ hz)
         constructor
         · exact vary_ignores (f:=B) (.inl i) (fun j=>by cases j with | inl j=> simpa [B] using h j | inr j=> simp [B]) p
         exact vary_ignores (f:=B) (.inr i) (fun j=>by cases j with | inr j=> simpa [B] using h j | inl j=> simp [B]) p
    cases g with
    | false=> rw [column]; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; change Z i j • (atom _* vary _ V)= _; by_cases h:i.1.1=u
              · rw [(hh i h).1,mul_zero,smul_zero]
              rw [show Z i j=0 from focusL a b u X i j h,zero_smul]
    | true=> rw [row]; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; change Z i j • (atom _* vary _ V)= _; by_cases h:j.1.1=u
             · rw [(hh j h).2,mul_zero,smul_zero]
             rw [show Z i j=0 from focusR a b u X i j h,zero_smul]
-- genuine exact-null at any level with spectators *away* from root acted on, before any marked matching, includes odd arguments
lemma clears (D:Set (Site c))(h:u∉D)(g:Bool)(he:a≠b)(A f:Stud c F)(ht: Uses D f) : joint ((⇑(applyMark g (localF u X a b))∘ A)*f)=0:=by
     let B:= applyMark g (localF u X a b); have hv(U): ber _ (B (A U)*(f U))=0:=by rw [show _ *(f U)= B (A U*f U) from ?_,integrated,near_trace a b X u he,zero_mul]; rw [show B _= _ from LMark g (localF u X a b) (A U) (f U),mark_site a b u X D h f ht g U,mul_zero,add_zero]
     unfold joint; change (∫ x,ber _ (B _ * f x)∂ prior su c)=_; simp_rw [hv]; exact integral_zero _ _
lemma mark_collect (g:Bool)(y:Stud c F)(U:Grid c): ∑ p:Site c,applyMark g (localF p X a b) (y U)= applyMark g f' (y U):=by
    conv_rhs => rw [← local_sum a b X]
    cases g
    · simp only [applyMark,LinearMap.sum_apply,LinearMap.smul_apply,Matrix.sum_apply,Bool.false_eq_true, ↓reduceIte,sum_smul];
      let f(u:Site c)(i j:Modes c F): Fields c F:= localF u X a b i j • gen (.inl i) (.inl j) (y U); change (∑ p,∑ i,∑ j,f p i j)=∑ i,∑ j,∑ p,f p i j; rw [sum_comm]; apply sum_congr rfl; intro _ _; rw [sum_comm]
    simp only [applyMark,LinearMap.sum_apply,LinearMap.smul_apply,Matrix.sum_apply,↓reduceIte,sum_smul]; rw [sum_comm]; apply sum_congr rfl; intro _ _; rw [sum_comm]
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.clears
