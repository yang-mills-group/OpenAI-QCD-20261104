import YM.QCD.RP.Arc

/-!
# Seam cocycle. Arbitrary affine transformations; descends exactly under embedding roots
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Revolve
open Lattice Wilson Lat RP Function Finset
variable {f n c : Side} {s : Signed} {t t' b : Site n} {d : Site n→ℂ}

def glint (t x : Site n) (i : Step) := seam t (i.used x).1 (i.used x).2
lemma glint_rev (x t : Site n) (i : Step): glint t (x+i.vec) i.rev=glint t x i:=by
  rcases i with ⟨i,_|_⟩ <;> simp [glint,Step.used,Step.vec,Step.rev,sub_eq_add_neg]
@[simp] lemma glint_sq (x t : Site n) (i : Step): glint t x i*glint t x i=1:= seam_sq ..

/-- base field seams `t`, image seams `t'` -/
structure Glare (s : Signed) (t t' b : Site n) (d : Site n→ℂ) : Prop where
 sign x : d x=1 ∨ d x= -1
 reflects (i : Axis) (x) : seam t x i*d (x+step i)=d x*glint t' (affine s b x) ((posDir i).rotate s)

lemma affine_add (s : Signed) (t x : Site n) (a : Step) : affine s t (x+a.vec)=affine s t x+(a.rotate s).vec := by rw [Step.vec_rotate]; simp [affine]; abel
lemma multi_tape (t v : Site n) : ∃ d : Site n→ℂ, (∀ x,d x=1 ∨ d x= -1)∧∀ i x,seam t x i*d (x+step i)=d x*seam v x i:=by
  let g i:= RP.Tape.mk i (t i) (v i)
  let l (x : Site n):=∏ i:Axis,(g i).stamp x
  refine ⟨l,?_,fun i x=>?_⟩
  · intro x; unfold l
    generalize (univ:Finset Axis)=s
    induction s using Finset.induction_on with
    | empty=> simp
    | insert a s hi ih=> rw [prod_insert hi]; rcases ih with ih|ih <;> rcases (g a).sign x with he|he <;> simp [ih,he]
  let k (x:Site n) := ∏ a∈univ.erase i,(g a).stamp x
  have he (y : Site n) : l y=(g i).stamp y*k y:= (mul_prod_erase _ _ (mem_univ _)).symm
  have ht : k (x+step i)=k x:=by unfold k; refine prod_congr rfl fun a ha=>?_ ; simp [g,Tape.stamp,ne_of_mem_erase ha]
  have hh : (g i).stamp x*seam t x i*(g i).stamp (x+step i)=seam v x i:=by
    rw [show _=seam (Function.update t i (v i)) x i from (g i).steady t rfl x]; simp [seam]
  rw [he,he,ht,← hh]; set A:=(g i).stamp x; have hv : A*A=1:= (g i).squared x
  calc _ = (A*A)*(seam t x i*((g i).stamp (x+step i)* k x)) := by rw [hv,one_mul]
       _ = _ := by ring

def veil (s : Signed) (b t : Site n) : Site n:= fun i=> if s.flip i then -t (s.perm i)+b (s.perm i)+1 else t (s.perm i)-b (s.perm i)
lemma glow_at (s : Signed) (b x t : Site n) (i : Axis) : glint t (affine s b x) ((posDir i).rotate s) = seam (veil s b t) x i := by
  let q:=s.perm i
  cases h : s.flip i
  · simp only [glint,Step.rotate,posDir,Step.used, h,Bool.xor_self,Bool.false_eq_true,↓reduceIte,seam,affine,Pi.add_apply,s.act_at,veil]; simp [add_right_comm,eq_sub_iff_add_eq]
  simp only [glint,Step.rotate,posDir,Step.used,h,Bool.false_xor, if_true,seam,affine,Pi.sub_apply,step_apply,Pi.add_apply,s.act_at,veil]
  change (if -x i+b q-1+1=t q then _ else _)=_
  have he : -x i+b q-1+1=t q↔x i+1= - t q+b q+1:=by rw [sub_add_cancel,add_left_inj]; simp [← sub_eq_neg_add,eq_sub_iff_add_eq,sub_eq_iff_eq_add']; exact eq_comm -- check signs
  simp only [he]; simp only [q] -- equality defeq
lemma shades (s : Signed) (t v b : Site n) : ∃ d, Glare s t v b d := by
  obtain ⟨d,h,H⟩:=multi_tape t (veil s b v); exact ⟨d,h,fun i x=> by rw [glow_at]; exact H i x⟩

variable (r : Ratio c f)
def shimmer (t x : Site n) : Walk → ℂ
 | []=> 1
 | a::l=> glint t x a*shimmer t (x+a.vec) l
lemma shone (t x : Site n) (p q : Walk) : shimmer t x (p++q) = shimmer t x p * shimmer t (stop x p) q := by
  induction p generalizing x with
  | nil=> simp [shimmer,stop]
  | cons a p ih=> simp [shimmer,ih,stop,mul_assoc]
lemma flick (t x : Site n) (w : Walk) : shimmer t (stop x w) (Lattice.reverse w)=shimmer t x w:= by
  induction w generalizing x with
  | nil=> rfl
  | cons a w ih=>
    rw [show Lattice.reverse (a::w)=Lattice.reverse w++[a.rev] by simp [Lattice.reverse], shimmer,stop,shone, ih,reverse_stop,shimmer,shimmer,mul_one,glint_rev,mul_comm]
lemma glared (h : Glare s t t' b d) (i : Step) (x) : glint t x i*d (x+i.vec)=d x*glint t' (affine s b x) (i.rotate s):=by
  rcases i with ⟨i,_|_⟩
  · exact h.reflects i x
  let a:= posDir i; let y:= x+a.rev.vec
  have hg : y+a.vec=x:=by simp [y,Step.vec_rev]
  have he : glint t y a*d x=d y*glint t' (affine s b y) (a.rotate s):=by rw [← hg]; rw [hg]; -- fails?
                                                                         exact hg ▸ h.reflects i y -- check
  change glint _ x a.rev * d y=d x* glint t' _ (a.rev.rotate s)
  rw [show glint t x a.rev=_ from hg ▸ glint_rev y t a,mul_comm (glint t y a)] -- should d y
  have hh : glint t' (affine s b x) (a.rev.rotate s) = glint t' (affine s b y) (a.rotate s):=by rw [← hg,affine_add,Step.rev_rotate,glint_rev]
  rw [hh]
  calc
    _ = glint t y a* (d y* (glint t' (affine s b y) (a.rotate s)*glint t' (affine s b y) (a.rotate s))) := by simp [mul_comm]
    _ = _ := by rw [← mul_assoc (d y),← he, ← mul_assoc (glint t y a), ← mul_assoc, glint_sq, one_mul]
lemma flare_path (h : Glare s t t' b d) (w : Walk) (x) : shimmer t x w*d (stop x w) = d x * shimmer t' (affine s b x) (w.map (·.rotate s)):=by
  induction w generalizing x with
  | nil=>simp [shimmer,stop]
  | cons a w ih=> rw [shimmer,List.map_cons,shimmer,stop,mul_assoc,ih,← mul_assoc (glint t x a),glared h, affine_add,mul_assoc]

lemma tone {a : Step} (k : ℕ) (x : Site f) : stop x (List.replicate k a)=x+k • a.vec:=by
  induction k generalizing x with
  | zero=>simp [stop]
  | succ k ih=> rw [List.replicate_succ,stop,ih,add_smul,one_smul]; abel
lemma root_vec (a : Step) (x : Site c) : r.embed (x+a.vec)= r.embed x+r.count.val • a.vec:=by
  change r.root _=_; rw [map_add, ← wrap_vec c a,r.root_embed (wrap _ _), Ratio.embed_wrap,map_nsmul,wrap_vec]; rfl
lemma cone (x : Site c) (a : Step): stop (r.embed x) (List.replicate r.count.val a)=r.embed (x+a.vec):=by rw [tone,root_vec]
lemma nothing_yet (k : ℕ) (hk : k<r.count.val) (i : Axis) (x t : Site c): shimmer (r.embed t) (r.embed x) (List.replicate k (posDir i))=1:=by
  have he (k : ℕ) (h : k+1<r.count.val): seam (r.embed t) (r.embed x + k • step i) i=1:=by
    unfold seam; rw [if_neg]; intro he
    let a : Site f := r.embed x +(k+1) • step i
    have hh : a i = r.embed t i := by
      unfold a; rw [add_smul,one_smul,← add_assoc,Pi.add_apply]; simpa using he
    have hm : r.residue a i = 0:= by unfold Ratio.residue; dsimp; rw [hh]; exact congr_fun (Ratio.residue_embed ..) _
    have hh : r.residue (step i)=step i:= by rw [← wrap_step f i, r.residue_wrap, wrap_step]
    simp only [a,map_add,map_nsmul, hh,r.residue_embed,zero_add] at hm
    have hr : (↑(k+1):Per r.count)=0:=by simpa [step_apply,Pi.smul_apply,nsmul_eq_mul] using hm
    have ht:= ZMod.val_natCast_of_lt h
    rw [hr,ZMod.val_zero] at ht; omega
  induction k with
  | zero => rfl
  | succ k ih=> rw [List.replicate_succ',shone,ih (by omega),tone,shimmer,shimmer,mul_one,one_mul]; exact he _ hk
lemma chord_yes (x t : Site c) (i : Axis): shimmer (r.embed t) (r.embed x) (List.replicate r.count.val (posDir i))=seam t x i:=by
  let k:= r.count.val-1; have hv : r.count.val=k+1:=by have := r.count.property; change r.count.val=r.count.val-1+1; exact (Nat.sub_add_cancel r.count.property).symm
  rw [hv,List.replicate_succ',shone,nothing_yet r k (by omega),one_mul,shimmer,shimmer,mul_one,tone]
  change seam (r.embed t) (r.embed x+k • step i) i=_
  have he : (r.embed x+k • step i : Site f) i+1=r.embed (x+step i) i:=by
    have h : r.embed (x+step i)=r.embed x+r.count.val • step i:=root_vec r (posDir i) x
    rw [h,hv,add_smul,one_smul,← add_assoc,Pi.add_apply]; simp
  have hh (x y:Site c):r.embed x i=r.embed y i ↔ x i=y i:=by
    constructor
    · intro h; have h' : lift (r.embed x) i=lift (r.embed y) i:=congr_arg ZMod.valMinAbs h; rw [r.lift_embed,r.lift_embed] at h'
      simp only [Pi.smul_apply,nsmul_eq_mul,mul_eq_mul_left_iff, Nat.cast_eq_zero, PNat.ne_zero,or_false] at h'; have h1:=congr_arg (fun x:ℤ=> (x:Per c)) h'; simpa [lift] using h1
    intro h; unfold Ratio.embed wrap lift; simp [h]
  simp only [seam,he,hh]; simp
lemma chord (x t : Site c) (a : Step): shimmer (r.embed t) (r.embed x) (List.replicate r.count.val a)=glint t x a:= by
  rcases a with ⟨i,_|_⟩; · exact chord_yes r x t i
  let y:=x-step i; let d:=posDir i
  have he : y+d.vec=x := by simp [y,d]
  rw [show List.replicate r.count.val (⟨i,true⟩:Step)=Lattice.reverse (List.replicate r.count.val d) from by simp [Lattice.reverse,d,negDir]]
  rw [show glint t x ⟨i,true⟩=seam t y i from he ▸ glint_rev y t d, show r.embed x=stop (r.embed y) (List.replicate r.count.val d) from by rw [cone,he],flick]; exact chord_yes ..
lemma shrouds {a y b : Site c} {d} {s} (h : Glare s (r.embed a) (r.embed y) (r.embed b) d): Glare s a y b (d∘r.embed) := by
  refine ⟨fun x=>h.sign _,fun i x=>?_⟩
  have he:=flare_path h (List.replicate r.count.val (posDir i)) (r.embed x)
  have hh : affine s (r.embed b) (r.embed x)=r.embed (affine s b x):=by unfold affine; rw [← r.signed]; exact (r.root.map_add ..).symm
  rw [hh,chord,List.map_replicate,chord,cone] at he; exact he
end YM.QCD.Revolve
