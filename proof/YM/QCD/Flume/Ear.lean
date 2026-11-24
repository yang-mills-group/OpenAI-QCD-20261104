import YM.QCD.Flume.Collect

/-! # the actual self-consistent free step at arbitrary volume and history -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free Metric Kit Free
open scoped Topology BigOperators Matrix Kronecker
variable {c f n : Side} {j k : ℕ}

def rangeD (v : Train k) (i : Site n) := model (Dir v (tuning i))
def rangeG (v : Train k) (i : Site n) := model (full v (tuning i))
def install (M : Site n→Bundle) : Sheet n := leaf n*lined M*star (leaf n)
def unbarred (v : Train k) (n : Side) := install (rangeD v (n:=n))
def stage (v : Train k) (n : Side) := install (rangeG v (n:=n))
lemma carries (M : Site n→Bundle) : peel (install M)=lined M:=by
  apply peel_eq; rw [install,mul_assoc _ (star _) (leaf n),(leaf_u _).1,mul_one]
lemma root_book (j : ℕ) (n : Side) : unbarred (.top j) n=bareD (0: Site n) 1 0:=by apply peel_injective; rw [peeled,unbarred, carries]; congr 1; funext x; rw [rangeD,Dir_top]; exact version _
lemma dog (i : Site n):tuning i ∈ realCube zone:= base_subset_realCube zone_pos (keyboard i)
lemma pairs (v : Train k) (i : Site n):rangeG v i*rangeD v i=1 ∧ rangeD v i*rangeG v i=1:=by
  unfold rangeD rangeG
  have hh := nonzeroD (v:=v) (dog i) (tune_nonzero i)
  rw [full_match (dog i) (tune_nonzero i)]
  exact ⟨Matrix.nonsing_inv_mul _ (Para.funds hh),Matrix.mul_nonsing_inv _ (Para.funds hh)⟩
lemma links_inv (v : Train k) (n : Side) : stage v n * unbarred v n=1 ∧ unbarred v n*stage v n=1:= by
  have ht:stage v n*unbarred v n=1:=by apply peel_injective; rw [peel_mul,stage,unbarred,carries,carries,lined_law,show rangeG v (n:=n)*rangeD v=(fun _=> 1) from funext fun i=> (pairs v i).1,peel_one]; exact ridden
  exact ⟨ht,mul_eq_one_comm.mp ht⟩
lemma stage_eq (v : Train k) (n : Side) : stage v n=(unbarred v n)⁻¹:=(Matrix.inv_eq_left_inv (links_inv v n).1).symm

/-- mixed peel to alias-coordinate weights -/
def violet (L : Rail c f) := star (leaf c) * L * leaf f
lemma approach (M : Rail c f) (X : Sheet f) : peel (M*X*Mᴴ)=violet M * peel X*(violet M)ᴴ := by
  unfold peel violet; rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,← Matrix.star_eq_conjTranspose (star _),star_star,← Matrix.star_eq_conjTranspose (leaf f)]
  simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (leaf f) (star _),(leaf_u _).2,Matrix.one_mul,← Matrix.mul_assoc (leaf f) (star _),(leaf_u _).2,Matrix.one_mul]

variable (P : Flight j k) (h : f.val=c.val*P.L.val)
abbrev conn := tied P h 0 1
abbrev rays := violet (conn P h)
lemma resonate (x p : Site c) (a b : Fiber) (l : Site P.L):
    rays P h (x,a) (twins (sliceL P h) p l,b)=(slope P.L:ℂ)*book P (tuning p) l*(1:Sheet c) (x,a) (p,b):=by
  have hg : star (leaf c)*leaf c=(1:Sheet c):=(leaf_u c).1
  unfold rays violet conn; rw [Matrix.mul_assoc,Matrix.mul_apply,← hg,Matrix.mul_apply,Finset.mul_sum]; apply sum_congr rfl; rintro ⟨i,y⟩ _; rw [tight]; ring
lemma resound (x p : Site c) (a b : Fiber) (l : Site P.L) :
    (rays P h)ᴴ (twins (sliceL P h) p l,b) (x,a)=(slope P.L:ℂ)*book P (tuning p) l*(1:Sheet c) (x,a) (p,b):= by
  rw [Matrix.conjTranspose_apply, resonate,star_mul,star_mul, book_real _ _ (keyboard _).1]; simp [Matrix.one_apply,mul_comm]
lemma valued (u v : Site c) (i y : Site P.L) : twins (sliceL P h) u i=twins (sliceL P h) v y ↔ (u=v ∧ i=y):= (tunes (sliceL P h) P.odd).injective.eq_iff.trans (Iff.of_eq (Prod.mk.injEq ..))
lemma pins (x p : Site c) (a b : Fiber) (X : Site f→Bundle) (l : Site P.L) :
    (rays P h * lined X) (x,a) (twins (sliceL P h) p l,b)=if x=p then (slope P.L:ℂ)* book P (tuning p) l * X (twins (sliceL P h) p l) a b else 0:=by
  let r:=sliceL P h; let i:=twins r p l
  rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single i]
  · by_cases he:x=p <;> simp only [i,r,resonate,Matrix.one_apply,Prod.mk.injEq,he,true_and,false_and,↓reduceIte,mul_one,mul_ite,mul_zero,ite_mul,zero_mul,lined,rides, Matrix.of_apply,Equiv.refl_apply, Finset.sum_ite_eq,Finset.mem_univ,sum_const_zero]
  · intro j _ hj; dsimp only [i,r] at hj; simp [lined,rides,hj]
  simp
lemma coin_l (L : Side) : (slope L:ℂ)^2=(L.val:ℂ)⁻¹:=by
  have he : slope L^2=(L.val:ℝ)⁻¹ := by rw [Kit.slope,inv_pow,Real.sq_sqrt (side_pos L).le]
  rw [← Complex.ofReal_pow, he]; simp
lemma spin_ray (P' : Momentum) (p : Site c) (hx : P'=tuning p) :
    rangeG P.land p=1+(∑ i : Site P.L, ((P.L.val:ℂ)⁻¹ *book P P' i^2) • rangeG P.wing (twins (sliceL P h) p i)) := by
  rw [rangeG,Flight.land,unfold_full,model_add,model_solo,one_smul]
  congr 1; unfold jump spool
  change model ((P.L.val:ℂ)⁻¹ • ∑ i, book P (tuning p) i^2 • full P.wing _) = _
  rw [model_smul]; change _ • Para.signal _= _; rw [map_sum,Finset.smul_sum]
  apply sum_congr rfl; intro i hi
  rw [map_smul,smul_smul,hx,rangeG,full_tune (sliceL P h) P.odd]; rfl
lemma hearing : (1:Sheet c)+conn P h * stage P.wing f * (conn P h)ᴴ=stage P.land c:=by
  apply peel_injective; rw [peel_add,peel_one,approach,stage,carries,stage,carries]
  let r:=sliceL P h; let e:=tunes r P.odd
  ext ⟨x,a⟩ ⟨y,b⟩
  rw [Matrix.add_apply, Matrix.mul_apply,Fintype.sum_prod_type,← Equiv.sum_comp e, Fintype.sum_prod_type]
  let Z:=rangeG P.wing (n:=f); let M:= rays P h
  change _ +(∑ z:Site c, ∑ l:Site r.count, ∑ i:Fiber, (M*lined Z) _ (twins r z l,i)*Mᴴ (twins r z l,i) _) = _
  rw [sum_eq_single y]
  · dsimp only [M,r]; rw [show lined (rangeG P.land) (x,a) (y,b)=(if x=y then rangeG P.land x a b else 0) from rfl]
    by_cases hx:x=y
    · subst x; rw [if_pos rfl,spin_ray P h (tuning y) y rfl,Matrix.add_apply,Matrix.sum_apply]; congr 1
      · simp [Matrix.one_apply]
      apply sum_congr rfl; intro l _; rw [sum_eq_single b]
      · rw [resound P h,pins P h]; simp only [if_true,Matrix.one_apply,Prod.mk.injEq,true_and,Matrix.smul_apply, smul_eq_mul,mul_one]; unfold Z
        rw [← coin_l]; ring
      · intro i _ hi; rw [resound P h]; simp [Matrix.one_apply,hi,Ne.symm hi]
      simp
    simp only [pins P h, hx,Matrix.one_apply,Prod.mk.injEq,false_and, ↓reduceIte,zero_mul,sum_const_zero,add_zero]
  · intro z _ hz; dsimp only [M,r]; simp only [resound P h,Matrix.one_apply,Prod.mk.injEq,Ne.symm hz,false_and, ↓reduceIte,mul_zero,sum_const_zero]
  simp

def father : Sheet f:= unbarred P.wing f+(conn P h)ᴴ*conn P h
lemma high_rank : IsUnit (father P h).det:= by
  let M:=conn P h; let X:=unbarred P.wing f; let Y:=stage P.wing f; let Z:=unbarred P.land c; let A:= stage P.land c
  have hA : 1+M*Y*Mᴴ=A:=hearing ..
  have hF : (X+Mᴴ*M)*(Y-Y*Mᴴ*Z*M*Y)=1:=by
    have hu : M*Y*Mᴴ=A-1:=by rw [← hA]; abel
    have hw : (1:Sheet c) - Z=(M*Y*Mᴴ)*Z:=by rw [hu,sub_mul,one_mul,(links_inv P.land c).1]
    have hx : M*Y-(M*Y*Mᴴ)*Z*M*Y= Z*M*Y:= by rw [← hw, Matrix.sub_mul, Matrix.one_mul,Matrix.sub_mul]; abel
    have he : X*Y=1:=(links_inv ..).2
    rw [Matrix.add_mul,Matrix.mul_sub,Matrix.mul_sub,← Matrix.mul_assoc,← Matrix.mul_assoc,← Matrix.mul_assoc,← Matrix.mul_assoc,he,Matrix.one_mul]
    have hK : Mᴴ*M*Y - (Mᴴ*M)*(Y*Mᴴ*Z*M*Y) = Mᴴ*(Z*M*Y):=by
      rw [← hx, Matrix.mul_sub]; simp only [Matrix.mul_assoc]
    rw [hK,← Matrix.mul_assoc,← Matrix.mul_assoc]; abel
  have hg := congr_arg Matrix.det hF; rw [Matrix.det_mul,Matrix.det_one] at hg
  refine IsUnit.mk0 _ (fun e=> ?_); change Matrix.det (X + Mᴴ*M)=0 at e; rw [e,zero_mul] at hg; exact zero_ne_one hg
lemma father_resp : (father P h)⁻¹*(conn P h)ᴴ=stage P.wing f*(conn P h)ᴴ*unbarred P.land c:= by
  let M:=conn P h; let X:=unbarred P.wing f; let Y:=stage P.wing f; let Z:= unbarred P.land c; let A:=stage P.land c
  have he: M*Y*Mᴴ=A-1:=by rw [← show 1+M*Y*Mᴴ=A from hearing ..]; abel
  have hp : (father P h)*(Y*Mᴴ*Z)= Mᴴ:=by
    unfold father; rw [Matrix.add_mul]
    change X*(Y*Mᴴ*Z)+Mᴴ*M*(Y*Mᴴ*Z)=_
    rw [← Matrix.mul_assoc X, ← Matrix.mul_assoc X,(links_inv P.wing f).2,Matrix.one_mul]
    rw [Matrix.mul_assoc Mᴴ M, ← Matrix.mul_assoc M, ← Matrix.mul_assoc M,he,sub_mul,(links_inv P.land c).1, one_mul,Matrix.mul_sub, Matrix.mul_one]; abel
  change (father P h)⁻¹*Mᴴ=Y*Mᴴ*Z; nth_rw 1 [← hp]; rw [← Matrix.mul_assoc (father P h)⁻¹,Matrix.nonsing_inv_mul _ (high_rank P h),Matrix.one_mul] -- orientation issue
lemma heir : 1-conn P h*(father P h)⁻¹*(conn P h)ᴴ=unbarred P.land c := by
  rw [Matrix.mul_assoc, father_resp, ← Matrix.mul_assoc,← Matrix.mul_assoc,show conn P h * stage P.wing f * (conn P h)ᴴ=_-1 from (by rw [← hearing P h]; abel : _= stage P.land c -1),Matrix.sub_mul, one_mul,(links_inv P.land c).1]; abel
end YM.QCD.Flume
