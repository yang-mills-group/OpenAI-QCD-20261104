import YM.Massive.Target.Calibration
import Mathlib.Data.List.Perm.Basic
import Mathlib.Logic.Equiv.Fin.Basic
/-!
# Exact averaging (factorization and geometry). Not a Gaussian shell claim.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice
open scoped ContDiff Topology BigOperators
namespace Rolls
variable {X Y:Type}[AddCommGroup X][Module ℝ X][AddCommGroup Y][Module ℝ Y]
variable {u:Averaging}{m n:ℕ} (v:Cover→X)(b:Cover)
abbrev PairS:=Axis× ℕ
abbrev Sail:= Axis→ Fin 7
def lanes (f:Sail)(a:Axis): List PairS:= (a,1)::List.replicate (f a).val (a,2)
def menu : Averaging → List PairS | .none=>[]|.some f=>(List.finRange 4).flatMap (lanes f)
abbrev centre (m:ℕ):ℤ:= ((m-1)/2:ℕ)
def stride (a:PairS)(m:ℕ)(i:Fin n) : Cover:= ((m*a.2:ℕ):ℤ) • ((i.val-centre n) • step a.1)
abbrev glance (a:PairS)(k m:ℕ)(v: Cover→X): Cover→X:= Averaging.axis (k*a.2) m a.1 v
def rolls (k m:ℕ): List PairS → (Cover→X)→Cover→X|[],v=>v| x::l,v=> glance x k m (rolls k m l v)
variable (k j M N:ℕ)(a x:PairS)(l l' :List PairS)
lemma sumG (m:ℕ) : glance a k m v b=(m:ℝ)⁻¹ •∑ i:Fin m, v (b+stride a k i):=rfl
lemma commute_axis : glance a k M (glance x j N v)= glance x j N (glance a k M v):=by
    funext b; simp_rw [sumG,← Finset.smul_sum]; rw [smul_comm,Finset.sum_comm]; congr 2; refine Finset.sum_congr rfl fun i _=>?_ ; exact Finset.sum_congr rfl fun y _=> congr_arg v (by rw [add_right_comm])
lemma rolls_axis : rolls k m l (glance a j N v)= glance a j N (rolls k m l v):=by
    induction l with|nil=>rfl | cons x l h=>rw [rolls,rolls,h, commute_axis]
lemma append : rolls k m (l++l') v=rolls k m l (rolls k m l' v):=by induction l with |nil=>rfl |cons i l ih=> simp only [List.cons_append,rolls,ih]
lemma roll_move : rolls k M l (rolls j N l' v)= rolls j N l' (rolls k M l v):=by
    induction l with| nil=>rfl | cons i l ih=> rw [rolls,rolls,ih,rolls_axis]
private abbrev oneLane (f:Sail)(m:ℕ)(v:Cover→X)(a:Axis):=Averaging.axis 1 m a ((Averaging.axis 2 m a)^[(f a).val] v)
private lemma enroll (a:Axis)(u:Sail) : rolls 1 M (lanes u a) v=oneLane u M v a:=by
    have he(n:ℕ):rolls 1 M (List.replicate n (a,2)) v=(Averaging.axis 2 M a)^[n] v:=by induction n with | zero=>rfl|succ n ih=>rw [List.replicate_succ,rolls,ih,iterate_succ_apply']; rfl -- likely rfl
    rw [lanes,rolls,he]; rfl -- lint
lemma roles : Averaging.filter u M v=rolls 1 M (menu u) v:=by
    cases u with | none=> rfl|some f=>
     have ht(s:List Axis)(v:Cover→X):s.foldl (oneLane f M) v = rolls 1 M (s.flatMap (lanes f)) v:=by
        induction s generalizing v with|nil=>rfl|cons i s h=> rw [List.foldl_cons,List.flatMap_cons, append,h,← enroll,roll_move]
     exact ht _ _
lemma chain_zero : rolls k 1 l v=v:=by
    induction l with|nil=>rfl|cons i l h=> rw [rolls,h]; funext x; rw [sumG]; simp [stride,centre]
-- Exact samples
variable {M N}
lemma equity (hM:Odd M)(hN: Odd N) : centre (M*N) = centre N+(N:ℤ)*centre M:=by
     obtain ⟨p,hp⟩:=hM; obtain ⟨q,hq⟩:=hN; have hg:(M*N-1)/2=q+N*p:=by
         have h:M*N=2*(q+N*p)+1:=by rw [hp,hq]; ring
         omega
     have hx:centre M=(p:ℕ):=by unfold centre; omega
     have hz:centre N=(q:ℕ):=by unfold centre; omega -- type infer ^erce
     rw [hx,hz]; unfold centre; rw [hg]; simp
lemma piece_at(i:Fin M)(j:Fin N)(hM:Odd M)(hN:Odd N):stride a k (finProdFinEquiv (i,j)) = stride a k j+stride a (k*N) i:=by
    unfold stride; rw [equity hM hN, show (finProdFinEquiv (i,j)).val=j.val+N*i.val from rfl]; simp only [Nat.cast_mul, Nat.cast_add]; have he : (j.val:ℤ)+N*i.val-(centre N+N*centre M) = j.val - centre N+ N*(i.val-centre M):= by ring
    rw [he,add_smul,smul_add,mul_smul]; -- weights associativity by abel?
    congr 1; simp_rw [← mul_smul]; ring_nf
lemma cut_axis (hM:Odd M)(hN:Odd N): glance a k (M*N) v=glance a (k*N) M (glance a k N v):=by
    funext i; simp_rw [sumG, ← Equiv.sum_comp (finProdFinEquiv (m:=M) (n:=N))] -- may rew both
    simp_rw [Fintype.sum_prod_type,piece_at k a _ _ hM hN,← Finset.smul_sum]; rw [smul_smul,Nat.cast_mul,mul_inv,mul_comm]; apply congr_arg₂ HSMul.hSMul ?_ ?_
    · simp [mul_comm]
    refine Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=> congr_arg v ?_ ; abel
lemma cut_space (hM:Odd M)(hN: Odd N): rolls k (M*N) l v=rolls (k*N) M l (rolls k N l v):=by
     induction l with|nil=>rfl | cons x l ih=> simp only [rolls, ih]; rw [cut_axis _ _ _ hM hN,rolls_axis]
variable (b' : Cover)
lemma drift_axis (c: Cover) : glance a k M (fun x=> v (x+c)) b=glance a k M v (b+c):=by
    simp_rw [sumG]; apply congr_arg; refine Finset.sum_congr rfl fun i _=> congr_arg v ?_ ; rw [add_right_comm]
lemma driftRoll(c: Cover) : rolls k M l (fun x=> v (x+c)) b=rolls k M l v (b+c):=by induction l generalizing b with| nil=>rfl|cons i l h=> rw [rolls,rolls,show rolls k M l _=(fun x=> rolls k M l v (x+c)) from funext h, drift_axis]
lemma rollLinear (G:X→ₗ[ℝ]Y): G (rolls k M l v b)=rolls k M l (fun t=> G (v t)) b:=by
     induction l generalizing b with|nil=>rfl|cons i l h=> simp only [rolls,sumG,map_smul,map_sum,h]
lemma training (v w:Cover→X) : rolls k M l (v+w)=rolls k M l v+ rolls k M l w:=by induction l with|nil=>rfl|cons i l h=> rw [rolls,h,rolls,rolls]; funext x; rw [Pi.add_apply]; simp_rw [sumG,Pi.add_apply,sum_add_distrib,smul_add]
lemma stride_dilate : (M:ℕ) • stride a k (n:=N) = stride a (k*M):=by -- smul Pi
     funext i; change M • (stride a k i)=_; unfold stride; rw [show M • _ = (M:ℤ) • (((k*a.2:ℕ):ℤ) • ((i.val-centre N) • step a.1)) from (by simp),← mul_smul]; push_cast; ring_nf -- typeclass ring components
lemma dilation (v:Cover→X) : rolls k N l (fun x:Cover=> v (M • x)) b = rolls (k*M) N l v (M • b):=by
     induction l generalizing b with| nil=>rfl|cons i l h=> rw [rolls,rolls,sumG,sumG]; apply congr_arg; apply sum_congr rfl; intro j _; rw [h,smul_add, show M • stride i k j= _ from congr_fun (stride_dilate (M:=M) k i (N:=N)) j] -- eq sig
end Rolls
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Rolls.dilation
