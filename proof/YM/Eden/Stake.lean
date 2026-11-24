import YM.Eden.Cool
import YM.Arise.Per
/-! # transfer signed kernels to compressed register one row.Behind Loom worst case.V -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior FreeResolvent
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free Bloom Arise Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Classical
variable {G:Gauge} {d' k i m:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}(h:Floor H t n a b)(ha:0<a)
variable (s:Signed)(x y z w:Cover)(p q:PlaqAxes)
variable (X Y:Parc) (A J:ℝ)
lemma tilted : p.rotate s=took s p:=by unfold PlaqAxes.rotate PlaqAxes.ordered took; rcases lt_or_gt_of_ne (s.perm.injective.ne p.property.ne) with ht|ht; simp [tw, ht, min_eq_left ht.le,max_eq_right ht.le]; simp [tw,ht.not_gt,min_eq_right ht.le,max_eq_left ht.le]
lemma signV : glyphO s p=turned s p:=by unfold turned glyphO hue; dsimp only; split_ifs <;> ring
lemma sale : Face.send s 0 (wrap n x,p) = (wrap n (s.act x+bend s p),took s p):=by unfold Face.send; rw [tilted]; congr 1; unfold Face.lower bend atFace affine dent; cases ha:s.flip p.val.1 <;> cases hb:s.flip p.val.2 <;> simp [*,Step.rotate, Step.vec, posDir,← wrap_signed] <;> abel
lemma p_full (c:Side)(F:Bed): pairP c (learned F c) x y (plaquette p) (plaquette q) (Finsupp.single z A) (Finsupp.single w J)= A * learned F c (wrap c (x+z),plaquette p) (wrap c (y+w),plaquette q) * J:=by
    simp only [pairP,stalk,Finsupp.linearCombination_single]; simp [Matrix.mul_apply,ite_mul,mul_ite]
-- mixed planner
local notation "Bh"=> pairP n (learned H n)
local notation "Qp"=> plaquette p
local notation "Qv"=> plaquette q
include h ha
lemma shift_pair (v: Cover): Bh (x+v) (y+v) Qp Qv X Y=Bh x y Qp Qv X Y:=by
     induction X using Finsupp.induction_linear with
     | zero=> simp [pairP]
     | add i j h hp=> unfold pairP at *; rw [map_add,map_add, Matrix.add_mul,Matrix.add_mul, Matrix.add_apply,h,hp, Matrix.add_mul, Matrix.add_mul, Matrix.add_apply] -- maybe orientation
     | single i a=>
       induction Y using Finsupp.induction_linear with
       | zero=> simp [pairP]
       | add i j h hp=> unfold pairP at *; simp only [map_add, Matrix.transpose_add,Matrix.mul_add, Matrix.add_apply,h,hp]
       | single j A=> rw [p_full,p_full,add_right_comm x,add_right_comm y, map_add (wrap n) (x+i), map_add (wrap n) (y+j)]; have he:= lofty h ha (wrap n v) (wrap n (x+i), Qp) (wrap n (y+j),Qv); exact congr_arg (fun z:ℝ=>a*z*A) he
local notation "Iφ"=> Bh (s.act x) (s.act y) (plaquette (took s p)) (plaquette (took s q))
local notation "τ"=> stake s (bend s p)
local notation "ι"=> stake s (bend s q)
lemma pinV (hs:Bid.Sworn H n G)(u:G.ColorIndex): glyphO s p * Iφ (τ X) (ι Y) * glyphO s q = Bh x y Qp Qv X Y:=by
    induction X using Finsupp.induction_linear with
    |zero=> simp [pairP]
    |add i j h hp=> unfold pairP at *; simp only [map_add, Matrix.add_mul, Matrix.add_apply,mul_add,add_mul,h,hp]
    |single i b=>
     induction Y using Finsupp.induction_linear with
     |zero=> simp [pairP]
     |add j v h hp=> unfold pairP at *; simp only [map_add, Matrix.transpose_add,Matrix.mul_add, Matrix.add_apply,mul_add,add_mul,h,hp]
     |single j c=>
       simp only [stake,Finsupp.linearCombination_single,Finsupp.smul_single',smul_eq_mul,mul_one]; rw[p_full,p_full,signV,signV]; let l:=wrap n (x+i); let m:=wrap n (y+j); let A:= Face.send s 0 (l,p); let V:= Face.send s 0 (m,q); let f(a: Face (Per n))(b: Face (Per n)):=learned H n (address n a) (address n b); have he: turned s p * f A V * turned s q= f (l,p) (m,q):= luminous s _ _ (l,p) (m,q) h ha hs u; have hp : (wrap n (s.act x+(s.act i+bend s p)), plaquette (took s p))=address n A:=by unfold A l; rw [sale]; unfold address; simp only [Signed.act_add, add_assoc]; rfl
       have hq : (wrap n (s.act y+(s.act j+bend s q)),plaquette (took s q))=address n V:=by unfold V m; rw [sale]; unfold address; simp only [Signed.act_add,add_assoc]; rfl
       rw [hp,hq]; change _= b*(f (l,p) (m,q))*c; rw[←he]; unfold f; ring
-- T pivot Self covariance. with weights later.St.Material
noncomputable def milky (x:Cover) (H:Bed)(n:Side): Matrix (Zinc G d') (Zinc G d') ℂ:= Matrix.of fun v w=> (pop1 (voteP n v x) (voteP n w x) (heartP H G n)) () ()
omit h ha
noncomputable def allP (x:Cover)(H:Bed)(n:Side) (i j : Motif d'):ℝ:= pairP n (learned H n) x x (plaquette i.2.1) (plaquette j.2.1) (came (chore d' (List.ofFn i.2.2) i.2.1)) (came (chore d' (List.ofFn j.2.2) j.2.1))
lemma milk_read (v w: Zinc G d') (H:Bed)(n:Side): milky x H n v w= if v.2=w.2 then (allP x H n v.1 w.1:ℂ) else 0:=by unfold milky; rw [of_apply]; unfold pop1 voteP pupil heartP; rw[coversU]; by_cases h:v.2=w.2 <;> simp only [h,↓reduceIte] <;> rfl
lemma stem_m (v:Motif d'): List.ofFn (swing s v.2).2= sways s (List.ofFn v.2.2):=by unfold sways swing; rw[List.map_ofFn]
include h ha
lemma silky : milky x H n (G:=G) (d':=d')=milky 0 H n:=by
    ext i j; rw[milk_read,milk_read]; by_cases h':i.2=j.2; swap; · rw [if_neg h', if_neg h'];
    rw [if_pos h',if_pos h']; congr 1; unfold allP; exact (by simpa only [zero_add] using! shift_pair h ha 0 0 i.1.2.1 j.1.2.1 (glimpse i) (glimpse j) x)
lemma shootsK (v w:Zinc G d')(hs:Bid.Sworn H n G): let L:ℂ:= stainK s v; let P:ℂ:= stainK s w; L*milky (s.act x) H n (tideK s v) (tideK s w)*P= milky x H n v w:=by
    intro u q; let p:=v.1.2.1; let k:=w.1.2.1; let Q:=stemP v; let T:=stemP w; let X:=glimpse v; let V:=glimpse w
    rw[milk_read,milk_read]; by_cases he:v.2=w.2; swap; · rw[if_neg (show (tideK s v).2 ≠ (tideK s w).2 from he),if_neg he]; simp
    rw [if_pos (show (tideK s v).2 = (tideK s w).2 from he),if_pos he]; unfold u q; rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]; congr 1
    unfold allP; rw[show List.ofFn (tideK s v).1.2.2= _ from stem_m s v.1,show List.ofFn (tideK s w).1.2.2= _ from stem_m s w.1]
    change (vane s Q*glyphO s p)*Bh _ _ (plaquette (took s p)) (plaquette (took s k)) (came (chore d' _ (took s p))) (came (chore d' _ (took s k))) * (vane s T*glyphO s k)=_
    rw[grouped,grouped]; let Z:= Bh (s.act x) (s.act x) (plaquette (took s p)) (plaquette (took s k)) (stake s (bend s p) X) (stake s (bend s k) V); have hm(i j:ℝ): Bh (s.act x) (s.act x) (plaquette (took s p)) (plaquette (took s k)) (i • (stake s (bend s p) X)) (j • (stake s (bend s k) V))=i*j*Z:=by unfold pairP Z; rw[map_smul,map_smul,Matrix.transpose_smul,Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_apply, Matrix.smul_apply]; unfold pairP; ring
    erw [hm]; let i:=vane s Q; let j:=vane s T; let v':=glyphO s p; let w:=glyphO s k; change (i*v')*(i*j*Z)*(j*w)= _; rw [show (i*v')*(i*j*Z)*(j*w)=(i*i)*(j*j)*(v'*Z*w) from by ring, show i*i=_ from vane_sq _ _,show j*j=_ from vane_sq _ _,one_mul,one_mul]; exact pinV h ha s x x p k X V hs v.2
end YM.Eden
#print axioms YM.Eden.silky
#print axioms YM.Eden.shootsK
