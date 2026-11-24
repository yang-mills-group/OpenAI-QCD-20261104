import YM.Bank.Merchant
import YM.QCD.Garden.Shout
/-! telescope retaining seams. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bank
open Matrix Function Wilson Lattice RG Next.Free Filter Metric
open Lat Flume Laurent Bloch Finset Kit
open YM.Bank
open QCD.Free Cost
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ComplexConjugate
variable {c f k: Side}{j i:ℕ}{H: Ratio c f}{D B V:Train j}
lemma father_bar (F:Flight j i)(h:f.val=c.val*F.L.val) : Garden.barP F h=unbarred F.land c*conn F h*stage F.wing f:=by
   let B:= father F h; let M:=conn F h; let D:=unbarred F.land c; let A:=stage F.wing f; have hx:= high_rank F h
   have he: (D*M*A)*B=M:=by
        have hb : B= unbarred F.wing f+Mᴴ*M:=rfl
        have hl : D*(1+M*A*Mᴴ) =1:=by rw [show 1+M*A*Mᴴ=stage F.land c from hearing F h]; exact (links_inv F.land c).2
        rw [hb, Matrix.mul_add, Matrix.mul_assoc (D*M), (links_inv ..).1, Matrix.mul_one]
        calc D*M+D*M*A*(Mᴴ*M) = (D*(1+M*A*Mᴴ))*M:= by rw [Matrix.mul_add,Matrix.add_mul, mul_one]; simp only [Matrix.mul_assoc]
             _ = M:=by rw [hl,Matrix.one_mul]
   change M*B⁻¹ = _; nth_rw 1 [←he]; rw [Matrix.mul_assoc,B.mul_nonsing_inv hx,Matrix.mul_one]

def mount (j:ℕ)(H:Ratio c f)(p:Site c)(l:Site H.count):ℂ:= (Kit.slope H.count:ℂ)*sprout j H.count (aliasAt (tuning p) l)
def Lance (j:ℕ)(H:Ratio c f)(Q:Kit.Rail c f) :=∀ (u p: Site c)(l:Site H.count) (a b:Fiber), (violet Q) (u,a) (twins H p l,b)= mount j H p l*(1:Sheet c) (u,a) (p,b)
lemma t_lance (P:Flight j i)(h : f.val=c.val*P.L.val): Lance j (sliceL P h) (conn P h) := fun u p l a b=> resonate P h u p a b l
lemma zeros_p (j:ℕ): Lance j (idle c) 1:=by
   intro u p l a b; rw [violet,mul_one,(leaf_u _).1, twins_r]; unfold mount Kit.slope; simp [idle,sprout]
lemma blends {Q: Kit.Rail c f}{R: Kit.Rail f k}: violet (Q*R)= violet Q*violet R :=by unfold violet; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (leaf f) (star _), (leaf_u f).2,Matrix.one_mul]
lemma clear_pin (f g:Side): Kit.slope (f*g)=Kit.slope f*Kit.slope g:=by unfold Kit.slope; rw [mul_side_real,Real.sqrt_mul (side_pos f).le, mul_inv]
lemma Lance.next {r:Ratio f k}{Q X}(ho:Odd H.count.val)(hu:Odd r.count.val)(h:Lance j H Q)(g:Lance j r X): Lance j (loom H r) (Q*X):=by
   intro u p l a b
   obtain ⟨⟨z,v⟩,rfl⟩:=(radices ho hu).surjective l
   rw [blends, Matrix.mul_apply,Fintype.sum_prod_type,twins_loom]; rw [sum_eq_single (twins H p z)];
   · rw [sum_eq_single b]; rw [h u p,g, mount,mount,mount]; unfold loom; dsimp only; rw [← alias_refine,full_tune H ho, clear_pin, box_bind ho hu, Matrix.one_apply_eq]; push_cast; ring
     · intro i _ hi; rw [g]; simp [Matrix.one_apply,hi]
     simp
   · intro i _ hi; apply sum_eq_zero; intro y _; rw [g]; simp [Matrix.one_apply,hi]
   simp
structure Giant (j:ℕ)(H:Ratio c f)(D B: Train j)(U:Matrix (Lat.Row f) (Lat.Row c) ℂ)(Y Q:Kit.Rail c f):Prop where
   odd: Odd H.count.val
   lands : Lance j H Q
   rise : U=stage D f*Qᴴ*unbarred B c
   fall : Y=unbarred B c*Q*stage D f
lemma single (P:Flight j j) (h : f.val=c.val*P.L.val): Giant j (sliceL P h) P.wing P.land (proton P h) (Garden.barP P h) (conn P h) :=⟨P.odd,t_lance _ _,father_resp _ _,father_bar _ _⟩
lemma Giant.next {U Y Q Q' U' Y'} {R:Ratio f k}(h:Giant j H D B U Y Q)(hp:Giant j R V D U' Y' Q'): Giant j (loom H R) V B (U'*U) (Y*Y') (Q*Q') :=by
   refine ⟨h.odd.mul hp.odd, h.lands.next h.odd hp.odd hp.lands, ?_,?_⟩
   · rw [hp.rise,h.rise,Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (unbarred D f) (stage _ _), (links_inv ..).2, Matrix.one_mul]
   rw [h.fall,hp.fall]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (stage D f) (unbarred _ _),(links_inv ..).1,Matrix.one_mul]
lemma Giant.unit : Giant j (idle c) D D 1 1 1:=by
   refine ⟨odd_one,zeros_p j,?_,?_⟩; all_goals simp [(links_inv ..).1,(links_inv ..).2] -- edit
-- spectra parameters coarse pair kernels, mechanize both via `Up` interface.
lemma Lance.stamp {Q:Kit.Rail c f}(h:Lance j H Q) (u p:Site c)(l:Site H.count)(a b:Fiber):
  (violet Q)ᴴ (twins H p l,b) (u,a)=star (mount j H p l)*(1:Sheet c) (u,a) (p,b):=by rw [Matrix.conjTranspose_apply,h]; by_cases hv:(u,a)=(p,b) <;> rw [Matrix.one_apply] <;> simp only [hv, ↓reduceIte] <;> simp -- try

lemma fiber_k {n:Side}(f:Site n→Bundle): lined f=Bloch.fiber f:=by ext ⟨x,i⟩ ⟨y,j⟩; rfl
lemma peel_cast {v u:Side}{Y:Site v→Bundle}{X:Site u→ Bundle}{A:Kit.Rail u v} :
   (install X *A*install Y)ᴴ= install (fun i=> (Y i)ᴴ)*Aᴴ*install (fun i=> (X i)ᴴ) :=by
    have he {n:Side}(Y:Site n→Bundle): (install Y)ᴴ=install (fun i=>(Y i)ᴴ):= by unfold install; rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul]; rw [← Matrix.star_eq_conjTranspose (star _),star_star, ←Matrix.star_eq_conjTranspose (leaf n)]; rw [fiber_k,fiber_H,fiber_k,Matrix.mul_assoc]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, he, he, Matrix.mul_assoc]
variable (H)
def tag (X: Site f→Bundle)(Y:Site c→Bundle) (j:ℕ)(p:Site c)(l:Site H.count) := (star (mount j H p l)) • (X (twins H p l)*Y p)
/-- covers U and conj of full bar answer. -/
lemma tariffs (X: Site f→Bundle)(Y:Site c→Bundle){Q:Kit.Rail c f}(h:Lance j H Q) (ho:Odd H.count.val)(l:List Axis)(x:Site f)(a:Fiber)(p:Site c)(b:Fiber):
     (oldDiff (install X*Qᴴ* install Y) l* leaf c) (x,a) (p,b)=∑ i: Site H.count, listChip (tuning (twins H p i)) l *scarf (twins H p i) x * tag H X Y j p i a b :=by
   let T:= lined X*(violet Q)ᴴ*lined Y
   have he: install X*Qᴴ*install Y*leaf c=leaf f*T:=by unfold install T violet; rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose (star _),star_star, ←Matrix.star_eq_conjTranspose (leaf f)]; simp only [Matrix.mul_assoc,(leaf_u _).1,Matrix.mul_one]
   have hi s (u p:Site c) a b: (lined X*(violet Q)ᴴ) (twins H u s,a) (p,b)=if p=u then star (mount j H u s) * X (twins H u s) a b else 0:=by
       rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single (twins H u s)]
       rw [sum_eq_single b,h.stamp]; simp only [fiber_k,Bloch.fiber,Matrix.of_apply,if_true,Matrix.one_apply,Prod.mk.injEq,and_true]; split_ifs
       · rw [mul_one,mul_comm]
       simp
       intro i _ hi; rw [h.stamp]; simp [hi,Ne.symm hi,Matrix.one_apply]
       simp
       intro i _ hi; simp [fiber_k,Bloch.fiber,hi,Ne.symm hi]; simp
   have ht s (u p:Site c) a b : T (twins H u s,a) (p,b) = if p=u then tag H X Y j u s a b else 0:=by
       unfold T; rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single p]; simp_rw [hi]; rw [fiber_k]
       by_cases he:p=u; subst p; simp [Bloch.fiber,tag,Matrix.smul_apply,Matrix.mul_apply, Finset.mul_sum,mul_assoc]
       simp [he]
       intro i _ hi; simp [fiber_k,Bloch.fiber,hi]; simp
   induction l generalizing x with
   | nil=> rw [oldDiff, he, Matrix.mul_apply,Fintype.sum_prod_type, ← Equiv.sum_comp (tunes H ho), Fintype.sum_prod_type,sum_eq_single p]; apply sum_congr rfl; intro i _
           change (∑ v:Fiber,leaf f (x,a) (twins H p i,v)*T (twins H p i,v) (p,b))=_
           simp_rw [ht,bare_leaf]; simp [listChip,Matrix.one_apply,ite_mul,mul_ite]
           intro i _ hi; apply sum_eq_zero; intro j _; change (∑ v:Fiber,_*T (twins H i j,v) (p,b))= 0; simp [ht,hi,Ne.symm hi]; simp
   | cons i l ih=> rw [oldDiff, show after _ _ * leaf c= after ((oldDiff (install X*Qᴴ* install Y) l)*leaf c) i from Matrix.mul_assoc ..,afterwards,ih,ih,Finset.mul_sum,← sum_sub_distrib]
                   apply sum_congr rfl; intro k _; simp only [listChip,List.map_cons,List.prod_cons]; have hp:= scarf_a (twins H p k) x i; rw [Exterior.factor] at hp; unfold Next.Free.chip; linear_combination ((l.map (fun i=>Complex.exp (Complex.I*tuning (twins H p k) i)-1)).prod*tag H X Y j p k a b)*hp
end YM.QCD.Bank
#print axioms YM.QCD.Bank.Giant.next
#print axioms YM.QCD.Bank.tariffs
