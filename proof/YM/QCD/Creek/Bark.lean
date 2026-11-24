import YM.QCD.Creek.Flood
/-! # mixed operators calibrated -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Creek
open Grass Function Finset
open scoped Topology BigOperators Matrix
variable {A B M:Type*}[Fintype A][Fintype B][Fintype M]
abbrev bark:= barkG (head A B) (tail A B)
lemma across (f:Pairs A ↪ M)(g:B ↪ M)(h:∀ i j,f i ≠ g j)(K:Matrix A A ℂ)(S:Matrix (Pairs A) B ℂ): Commute (pond f K) (barkG f g S):=by
  refine finiteComm _ _ fun i _=> finiteComm _ _ fun j _=> timesComm (Commute.mul_right ?_ (vpet f K (f i)).symm) _
  exact sub_eq_zero.mp (skipped f K _ (by rintro ⟨k,hk⟩; exact h k j hk)) -- ∉ range
lemma pondB (K: Matrix A A ℂ)(S:Matrix (Pairs A) (Pairs B) ℂ): Commute (pond (head A B) K) (bark S):=across _ _ (heights A B) K S
variable (S T: Matrix (Pairs A) (Pairs B) ℂ)
-- collects outputs
lemma splits_index (p: Pairs (A⊕B)): (∃ i,head A B i=p)∨(∃ i,tail A B i=p):=by
  rcases p with (i|j)|(i|j); exact Or.inl ⟨.inl i,rfl⟩; exact Or.inr ⟨.inl j,rfl⟩; exact Or.inl ⟨.inr i,rfl⟩; exact Or.inr ⟨.inr j,rfl⟩
lemma sprig_eq (X Y : EndA A)(h : ∀ l:List A,X (l.map atom).prod=Y (l.map atom).prod): X=Y:=by
  have hv (i): X (mono i)=Y (mono i):=by obtain ⟨w,-,-,hw⟩:= expression i; rw [hw]; simpa only [List.map_ofFn] using h (List.ofFn w)
  refine ContinuousLinearMap.ext fun x=>?_ ; rw [← write x,map_sum,map_sum]; simp_rw [map_smul,hv]
variable [DecidableEq A][DecidableEq B]
lemma skinny (x:Dirac (A⊕B)): wipe A B S (birth (bark T) x)=wipe A B (S+T) x:=by
  have hp (L:List (Pairs (A⊕B))) : wipe A B S (birth (bark T) (L.map atom).prod)=wipe A B (S+T) (L.map atom).prod:=by
    induction L with
    | nil=>simp [ticks]
    | cons p L ih=>
      rw [List.map_cons,List.prod_cons,map_mul (wipe A B (S+T))]; rcases splits_index p with ⟨i,rfl⟩|⟨j,rfl⟩
      · rw [whistles_at (heights A B),map_mul,ih,map_add,wiper,wiper,map_sum]; simp_rw [Matrix.add_apply,add_smul,sum_add_distrib,map_smul,tails]
      rw [show birth (bark T) (_*_) = atom (tail A B j)* birth (bark T) (L.map atom).prod from DFunLike.congr_fun ((skirt (heights A B) T j).symm.eq) _,map_mul,tails,tails, ih]
  have hv (i): wipe A B S (birth (bark T) (mono i))=wipe A B (S+T) (mono i):=by obtain ⟨w,-,-,hw⟩:= expression i; rw [hw]; simpa only [List.map_ofFn] using hp (List.ofFn w)
  rw [← write x,map_sum,map_sum,map_sum]; simp_rw [map_smul,hv]

def bladesF (X:Matrix A B ℂ)(Y:Matrix B A ℂ): Matrix (Pairs A) (Pairs B) ℂ:=Matrix.fromBlocks X 0 0 Y.transpose
lemma shear_equals (X:Matrix A B ℂ)(Y:Matrix B A ℂ): (shear X Y).toLinearMap.toContinuousLinearMap= birth (bark (bladesF X Y)):=by
  let D:= bladesF X Y
  refine sprig_eq _ _ fun L=>?_ ; change shear X Y _= birth (bark D) _
  induction L with
  | nil=> simp [ticks]
  | cons p L ih=> rw [List.map_cons,List.prod_cons,map_mul,ih]; rcases splits_index p with ⟨i,rfl⟩|⟨j,rfl⟩
                  · rw [whistles_at (heights A B)]; congr 1; cases i with
                    | inl i =>
                       change shear X Y (psi (.inl i))=_; rw [shear,adapt_psi]; simp only [Fintype.sum_sum_type,D,bladesF]; simp [Pairs,Matrix.one_apply,ite_smul]
                    | inr i=>
                       change shear X Y (bar (.inl i))=_; rw [shear,adapt_bar]; simp only [Fintype.sum_sum_type,D,bladesF]; simp [Pairs,Matrix.one_apply,ite_smul]
                  have hx : atom (tail A B j)=far A B (atom j):=by change _=embed _ (atom j); rw [embed_atom]; rfl
                  rw [hx,shear_far,← hx]; exact DFunLike.congr_fun ((skirt (heights A B) D j).eq) _
end YM.QCD.Creek
