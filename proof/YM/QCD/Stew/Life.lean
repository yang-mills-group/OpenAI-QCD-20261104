import YM.QCD.Stew.Seal
/-! # Matrix representation for the Lie-flat bill.
No splitting flavors at the posterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {t:ℝ} {o: Site c}
variable {D K:Type*} [Fintype D][DecidableEq D][Fintype K][DecidableEq K]
local notation "J"=> Modes c N
local notation "V"=> EvenA c N
lemma rank_two (x:V) (h:Fit x): panel 2 x.val=form (grasp x.val):=by
   let p:= Complex.I • (1:Matrix (Flavor N) (Flavor N) ℂ); have hp:p∈unitary _:=unitaryV Complex.I _ (by simp)
   have hh: disguise (Complex.I • (1:Matrix J J ℂ)) x.val=x.val:=by
      have hv:flute (Lat.Row c) p=Complex.I • (1:Matrix J J ℂ):=by
         ext ⟨a,i⟩ ⟨b,j⟩; by_cases hf:a=b<;> by_cases hg:i=j<;> simp [p,flute, hf,hg,Matrix.one_apply,Matrix.smul_apply]
      have he:= h _ hp; rw [hv] at he; exact congr_arg Subtype.val he
   exact kent x.val (unbalanced _ hh) -- syntax
lemma adapted (L:Matrix J J ℂ)(x:V)(h: Fit x): grasp (disguise L x.val)= star L * grasp x.val * L:=by rw [←breast, sport,rank_two x h, disguise, form_map,Matrix.transpose_transpose,gravid,Matrix.mul_assoc]
lemma mirror (L:Matrix J J ℂ)(x:V)(h: Fit x): grasp (disguise L (surf _ x.val))= star L*star (grasp x.val)*L:=by rw [←breast,sport,toned, rank_two x h,Port.surf_form,disguise, form_map, Matrix.transpose_transpose,gravid,Matrix.mul_assoc]
lemma construe (x: V)(h:Fit x)(L:Matrix (Flavor N) (Flavor N) ℂ)(he:L∈unitary _) : Commute (flute (Lat.Row c) L) (grasp x.val):=by
   let M:=flute (Lat.Row c) L; have hg : disguise M x.val=x.val:=congr_arg Subtype.val (h L he)
   have he':= adapted M x h; rw [hg] at he'
   change M*grasp x.val= _; nth_rw 1 [he']; rw [← Matrix.mul_assoc,← Matrix.mul_assoc,(unit_f he).2, one_mul] -- .1? Unit check
section copies
-- classification by all unitary invariance. project via chosen flavor
variable {p:Matrix (D×Flavor N) (D×Flavor N) ℂ}
def spin (u:Equiv.Perm D): Matrix D D ℂ:=Matrix.of fun i j=> if u i=j then 1 else 0
lemma spun (u:Equiv.Perm D): spin u∈ unitary _:=by
   have he : star (spin u)=spin u.symm:=by ext i j; by_cases hf:u.symm i=j <;> simp only [spin,Matrix.of_apply, Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply] <;> simp [hf,u.apply_eq_iff_eq_symm_apply,eq_comm] <;> tauto
   have hh (v:Equiv.Perm D): spin v*spin v.symm=1:=by ext i j; by_cases hi:i=j <;> simp only [Matrix.mul_apply,spin, Matrix.of_apply,Matrix.one_apply,ite_mul,zero_mul,one_mul,Fintype.sum_ite_eq,Equiv.symm_apply_apply]
   constructor; · rw [he]; exact hh u.symm
   rw [he]; exact hh u
lemma lines (j:Flavor N) (i:Flavor N): star (if j=i then (-1:ℂ) else 1)=(if j=i then -1 else 1):=by split <;> simp
variable (p) (h: ∀ L:Matrix (Flavor N) (Flavor N) ℂ,L∈unitary _→ Commute (flute D L) p)
include h
lemma neutral (b:Flavor N):p=copies N (Matrix.of fun i j=> p (i,b) (j,b)):=by
   have he(v:Equiv.Perm (Flavor N))(i j:D)(k l:Flavor N): p (i,v k) (j,l)=p (i,k) (j,v.symm l):=by
      have hh:= congr_fun (congr_fun ((h _ (spun v)).eq) (i,k)) (j,l)
      have he a b u w: flute D (spin v) (a,u) (b,w)=if a=b ∧ v u=w then 1 else 0:=by by_cases hk:a=b <;> by_cases hp:v u=w <;> simp [flute,spin,hk,hp,Matrix.one_apply]
      let M:=flute D (spin v); have h1:(M*p) (i,k) (j,l)= p (i,v k) (j,l):=by
         rw [Matrix.mul_apply,sum_eq_single (i,v k)]
         · rw [show M _ _=(1:ℂ) from (he ..).trans (if_pos (And.intro rfl rfl)),one_mul]
         · rintro ⟨s,t⟩ _ hz; rw [show M _ _=(0:ℂ) from (he ..).trans (if_neg (fun g=> hz (Prod.ext g.1 g.2).symm)),zero_mul]
         simp
      have h2:(p*M) (i,k) (j,l)=p (i,k) (j,v.symm l):=by
         rw [Matrix.mul_apply,sum_eq_single (j,v.symm l)]
         · rw [show M _ _=(1:ℂ) from (he ..).trans (if_pos (And.intro rfl (v.apply_symm_apply _))),mul_one]
         · rintro ⟨s,t⟩ _ hz; rw [show M _ _=(0:ℂ) from (he ..).trans (if_neg (fun g=> hz (Prod.ext g.1 (v.apply_eq_iff_eq_symm_apply.mp g.2)))),mul_zero]
         simp
      exact h1.symm.trans (hh.trans h2)
   ext ⟨i,k⟩ ⟨j,l⟩; by_cases hk:k=l
   · subst l; simp only [copies,Matrix.blockDiagonal_apply,if_true, Matrix.of_apply]; let g:= Equiv.swap k b; have hp:= he g i j k b; rw [show g k=b from Equiv.swap_apply_left .., show g.symm b=k from Equiv.swap_apply_right ..] at hp; exact hp.symm
   simp only [copies,Matrix.blockDiagonal_apply,if_neg hk]; let R:Flavor N→ℂ:= fun i=> if k=i then -1 else 1; let L:= Matrix.diagonal R
   have hh:L∈unitary _:=by
       have hL : star L=L:=by
          ext a b; rcases eq_or_ne a b with hv|hv
          · subst b; simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,L,Matrix.diagonal_apply,if_true]; exact lines k a
          simp [hv,Ne.symm hv,L, Matrix.diagonal_apply, R,Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
       have hp:L*L=1:=by ext a b; by_cases he:a=b <;> by_cases hh:k=b <;> simp [L, R,Matrix.diagonal_apply, Matrix.diagonal_mul_diagonal,Matrix.one_apply,he,hh]
       constructor <;> rw [hL,hp]
   have hu:= congr_fun (congr_fun ((h _ hh).eq) (i,k)) (j,l)
   have hx : -p (i,k) (j,l)=p (i,k) (j,l):=by simpa [Matrix.mul_apply,flute,Matrix.kronecker_apply,L, Fintype.sum_prod_type, Matrix.one_apply, Matrix.diagonal_apply, mul_ite,ite_mul,R,hk] using hu
   apply Complex.ext; · have hp:=congr_arg Complex.re hx; rw [Complex.neg_re] at hp; rw [Complex.zero_re]; linarith
   have hp:=congr_arg Complex.im hx; rw [Complex.neg_im] at hp; rw [Complex.zero_im]; linarith
end copies
def feeF (b: Flavor N)(x:EvenA c N) : Sheet c := Matrix.of fun i j=>grasp x.val (i,b) (j,b)
lemma legal (v:V) (h:Fit v)(b: Flavor N): grasp v.val=copies N (feeF b v):=neutral (grasp v.val) (construe v h) b
lemma rite (v:V)(b : Flavor N)(X: Sheet c)(h:Fit v): feeF b (sways (copies N X) v)=star X * feeF b v*X:=by
   let T:=copies N X; have he:=adapted T v h; rw [legal v h b] at he; unfold T at he; rw [← copies_star,← copies_mul,← copies_mul] at he
   ext i j; change grasp _ (i,b) (j,b)=_; exact (congr_fun (congr_fun he (i,b)) (j,b)).trans (by simp [copies,Matrix.blockDiagonal_apply])
lemma burst (v:V)(b: Flavor N)(h:Fit v): feeF b (Regal c N v)=star (chirality c)*star (feeF b v)*chirality c:=by
   let X:=chirality c; have he:=mirror (copies N X) v h; rw [legal v h b,← copies_star,← copies_star,← copies_mul,← copies_mul] at he
   ext i j; have h: grasp (disguise (copies N X) (surf _ (Cove.light _ v))) (i,b) (j,b)= _ := congr_fun (congr_fun he (i,b)) (j,b); exact h.trans (show copies N (star X*star (feeF b v)*X) (i,b) (j,b)=(star X*star (feeF b v)*X) i j from by simp only [copies,Matrix.blockDiagonal_apply,if_true])
end YM.QCD.Stew
