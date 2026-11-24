import YM.Massive.PCAC.Jolt
import YM.Massive.Reservoir.Pixels
import YM.QCD.Door.Twig

/-!
# Total-PCAC marks commute through the actual history only with a bias.
At every level of a Run (variable Patch allowed) and any true input
precision of joint `Actual`. Includes local equation/null identity before
moment estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
variable (P:Flight j k)(K:KernelChoices)(h:f.val=c.val*P.L.val) (β w:ℝ)(hk:P.patch.Branches K su)
open Sway
open scoped Kronecker
variable (X:Spike)(a b:Flavor F)
def spot (a b:Flavor F): Matrix (Flavor F) (Flavor F) ℂ:= fun i j=> if i=a ∧ j=b then 1 else 0
noncomputable def flavorW(c:Side): Sour (Modes c F):= onSpin c X ⊗ₖ spot a b
lemma traceF (H:a≠b) (c:Side): Matrix.trace (flavorW X a b c)=0:=by unfold Matrix.trace; apply Finset.sum_eq_zero; rintro ⟨i,j⟩ _; unfold flavorW spot; simp only [Matrix.diag_apply,Matrix.kronecker_apply]; rw [if_neg (fun h=>H (h.1.symm.trans h.2)),mul_zero]
local notation "Z"=> qmove P h F
local notation "F!"=> flavorW X a b
lemma braid (V:Grid f): Z V * (F!) f=(F!) c*Z V:=by unfold qmove flavorW; rw [Sway.choir_in]; unfold Matrix.kronecker; rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]; simp [Pine.tiedSpin P h]
lemma braids (V:Grid f): (F!) f*(Z V)ᴴ=(Z V)ᴴ*(F!) c:=by
    let q:= Flume.tied P h 0 V; have hx := congr_arg (·ᴴ) (Pine.tiedSpin P h 0 V (star X)); have he(Y:Side): (onSpin Y (star X))ᴴ =onSpin Y X :=by rw [← Matrix.star_eq_conjTranspose, on_spin_star,star_star]
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,he,he] at hx; unfold qmove flavorW; rw [← Kit.choir_star, Sway.choir_in]; unfold Matrix.kronecker; rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,hx]; simp

-- At stop every level has true continuous insertion for density assuming `Actual`. Define actor even outside this condition for recursion, with a proof.
variable {R:Side}{S:Scheme}(Y:Run S N R F) (g:Bool)
section film
noncomputable def actor (A:Run S N R F)(i:ℕ) : Insertion (S.side R i) F:= if h:Continuous (A.density i) then ⟨_,h⟩ else 0
lemma act {i:ℕ}(ht:Y.Actual)(h:i≤N): ⇑(actor Y i)= Y.density i:=by unfold actor; rw [dif_pos (Y.continuity ht h)]; rfl
local notation "V!"=> fun m=> Scheme.send S R Y.β Y.w m (F:=F)
-- within depths. formula
lemma moves {i:ℕ}(ht:Y.Actual)(h:i<N) : (V! i) (actor Y (i+1))=actor Y i:=by
    apply DFunLike.coe_injective; change transfer (S.step i) _ _ _ _ _=_; rw [act Y ht h.le, act Y ht (show i+1≤N from h)]; exact (ht.travels.eqn (Nat.zero_le _) h).symm
noncomputable def liftM (Y:Run S N R F) (X:Spike)(a b:Flavor F) (i:ℕ) (M:Deck (S.side R (i+1)) F) :=
    toward (S.step i) S.choices (S.sides_next R i) (Y.β (i+1)) (Y.w i) (S.admissible i) (flavorW X a b _) (actor Y i) M
noncomputable def film (i:ℕ) : Insertion (S.side R i) F := mark g ((F!) _) (actor Y i)
lemma exact_step {i:ℕ}(ht:Y.Actual)(H:a≠b)(M:Deck (S.side R (i+1)) F) (h:i<N) : (V! i) (film X a b Y g (i+1)-passenger M)= film X a b Y g i - passenger (liftM Y X a b i M):=by
    obtain he:= incident (S.step i) S.choices (S.sides_next R i) (Y.β (i+1)) (Y.w i) (S.admissible i) (ht.w_pos h) ((F!) (S.side R (i+1))) ((F!) (S.side R i)) (traceF X a b H _) (traceF X a b H _) (braid (S.step i) _ X a b) (braids (S.step i) _ X a b) g (actor Y (i+1)) M; unfold film liftM; change (V! i) _= mark g ((F!) _) ((V! i) _) - passenger (toward _ _ _ _ _ _ _ ((V! i) _) _) at he; rw [moves Y ht h] at he; exact he
-- Includes choosing marking at ANY `q≤N`, no projection cc relationships.
theorem deliver (ht:Y.Actual)(H:a≠b)(q:ℕ)(hq:q ≤ N) : ∃ M:∀ i:ℕ, Deck (S.side R i) F, M q=0 ∧ (∀ i<q,M i=liftM Y X a b i (M (i+1))) ∧ ∀ i≤q, let W:= S.toStop R Y.β Y.w q i; W (film X a b Y g q)= film X a b Y g i - passenger (M i):=by
    let M (x:ℕ) : Deck (S.side R x) F:= if h:x ≤ q then Nat.decreasingInduction (motive:=fun i (_ : i ≤ q)=> Deck (S.side R i) F) (fun i _=> liftM Y X a b i) 0 h else 0 -- argument order index
    have he:M q=0:=by unfold M; rw [dif_pos le_rfl,Nat.decreasingInduction_self]
    have hp:∀ i<q,M i=liftM Y X a b i (M (i+1)):= by intro i h; unfold M; rw [dif_pos h.le,dif_pos (by omega : i+1≤q),Nat.decreasingInduction_succ_left _ _ (show i+1≤q from h)] -- name
    refine ⟨M,he,hp,?_⟩; intro i hi W; induction hi using Nat.decreasingInduction with
    | self => unfold W; rw [Scheme.entrance,he,pax_zero,sub_zero]; rfl
    | of_succ i hi ih=> unfold W at *; rw [Scheme.next S R Y.β Y.w hi, ih, hp i hi]; exact exact_step X a b Y g ht H _ (hi.trans_le hq) -- W name binder scope induction
-- The transported mark still has zero partition. (`trace=0`, with functional exact identity.)
lemma mark_is_zero (H:a≠b)(f:Insertion c F): joint (⇑(mark g (flavorW X a b c) f))=0:=by unfold joint; simp only [mark, stroll_at, integrated, traceF X a b H c,zero_mul,integral_zero]
lemma pay_zero (M:Deck c F): joint (⇑(passenger M))=0:=by unfold joint; simp_rw [pax_apply, pairD,LinearMap.comp_apply,map_sum,integration,Finset.sum_const_zero]; exact integral_zero _ _ -- syntax
end film
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.deliver
