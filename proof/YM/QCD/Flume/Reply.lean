import YM.QCD.Flume.Ear

/-!
# Column and all first travel differences in Fourier
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set Matrix
open Laurent Bloch YM.Next.Free Metric Kit Free
open scoped Topology BigOperators Matrix Kronecker
variable {c f n : Side} {j k : ℕ} (P : Flight j k) (h : f.val=c.val*P.L.val)

local notation "r"=> sliceL P h
def inputM := lined (rangeG P.wing (n:=f))*(rays P h)ᴴ*lined (rangeD P.land)
def proton := (father P h)⁻¹*(conn P h)ᴴ
lemma ask : proton P h*leaf c=leaf f* inputM P h:=by
  unfold proton inputM; rw [father_resp,stage,unbarred]; unfold install rays violet; simp only [Matrix.conjTranspose_mul, ← star_eq_conjTranspose (star _), ← star_eq_conjTranspose (leaf _),star_star, Matrix.mul_assoc,(leaf_u c).1] --
  simp only [← Matrix.mul_assoc, (leaf_u c).1,Matrix.mul_one]

lemma ridge (X : Site f→Bundle) (p : Site c) (l : Site P.L) (y : Site c) (a b):
    (lined X*(rays P h)ᴴ) (twins r p l,a) (y,b)=if y=p then (slope P.L:ℂ)*book P (tuning p) l * X (twins r p l) a b else 0:= by
  rw [Matrix.mul_apply,Fintype.sum_prod_type, sum_eq_single (twins r p l)]
  · by_cases he:y=p
    · subst y; simp_rw [resound P h,lined,rr,Equiv.refl_apply]; simp [Matrix.one_apply,mul_comm]
    simp_rw [resound P h]; simp [he,Matrix.one_apply]
  · intro i _ hi; simp [lined,rides,hi,Ne.symm hi]
  simp

def gain (P : Flight j k) (p : Site c) (l : Site P.L) := ((P.L.val:ℂ)*(slope P.L:ℂ)) • shout false P (tuning p) l
lemma stored (p : Site c) (l : Site P.L) (y : Site c) (a b : Fiber) : inputM P h (twins r p l,a) (y,b) = if y=p then gain P p l a b else 0:=by
  unfold inputM; rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single y]
  · by_cases he:y=p; swap; · simp [ridge P h,he]
    subst y; rw [if_pos rfl]
    let q:=twins r p l
    have hh : gain P p l=((slope P.L:ℂ)*book P (tuning p) l) • (rangeG P.wing q*rangeD P.land p):=by
      unfold gain q rangeG rangeD
      rw [shout_match _ _ (dog _) (tune_nonzero _),full_tune r P.odd,Matrix.smul_mul,smul_smul,smul_smul]; congr 1; field_simp [side_ne P.L]
    rw [hh, Matrix.smul_apply,smul_eq_mul,mul_apply,mul_sum]; apply sum_congr rfl; intro i _
    rw [ridge P h,lined,rr,Equiv.refl_apply]; simp only [if_true,mul_assoc]; rfl
  · intro j _ hj; apply sum_eq_zero; intro i _; simp [lined,rides,hj]
  simp
lemma voice (p : Site c) (y : Site f) (a b : Fiber) : (proton P h*leaf c) (y,a) (p,b)=∑ i : Site P.L, scarf (twins r p i) y* gain P p i a b:=by
  rw [ask,Matrix.mul_apply,Fintype.sum_prod_type,← Equiv.sum_comp (tunes r P.odd),Fintype.sum_prod_type,sum_eq_single p]
  · apply sum_congr rfl; intro l _
    change (∑ i : Fiber, leaf f _ (twins r p l,i)*inputM P h (twins r p l,i) _)=_
    simp only [stored P h,bare_leaf,Matrix.one_apply,if_true,mul_ite,mul_one,mul_zero,ite_mul,zero_mul,sum_ite_eq,Finset.mem_univ]
  · intro j _ hj; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro a _; change _*inputM P h (twins r j i,a) (p,b)= _; rw [stored P h,if_neg (Ne.symm hj),mul_zero]
  simp

def after (A : Matrix (Lat.Row f) (Lat.Row c) ℂ) (i : Axis) := (shift (0 : Site f) 1 i-1)*A
def oldDiff (A : Matrix (Lat.Row f) (Lat.Row c) ℂ) : List Axis → Matrix (Lat.Row f) (Lat.Row c) ℂ
| []=>A
| a::u=> after (oldDiff A u) a
lemma afterwards (A : Matrix (Lat.Row f) (Lat.Row c) ℂ) (v) (x : Site f) (a : Fiber) (i) : after A v (x,a) i=seam 0 x v*A (x+step v,a) i-A (x,a) i:=by
  unfold after; rw [Matrix.sub_mul,Matrix.one_mul,Matrix.sub_apply,Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single (x+step v)]
  · simp [shift,rides,Free.travel,Matrix.one_apply]
  · intro j _ hj; simp [shift,rides,hj.symm]
  simp

lemma trailbill (u : List Axis) (p : Site c) (y : Site f) (a b : Fiber) : (oldDiff (proton P h) u*leaf c) (y,a) (p,b)=∑ i : Site P.L, scarf (twins r p i) y* (listChip (tuning (twins r p i)) u • gain P p i) a b:=by
  induction u generalizing y with
  | nil => simp only [oldDiff,listChip,List.map_nil,List.prod_nil,one_smul]; exact voice ..
  | cons i u ih=>
    rw [oldDiff, show after _ _ * leaf c= after ((oldDiff (proton P h) u)*leaf c) i from Matrix.mul_assoc ..,afterwards,ih,ih,Finset.mul_sum,← sum_sub_distrib]
    apply sum_congr rfl; intro k _; rw [← mul_assoc, onestep]
    have he : cis (menu (twins r p k) i) = chip (tuning (twins r p k) i)+1:=by unfold cis chip tuning; rw [sub_add_cancel,mul_comm]
    rw [he]; simp only [listChip, List.map_cons,List.prod_cons,Matrix.smul_apply,smul_eq_mul]; ring
end YM.QCD.Flume
