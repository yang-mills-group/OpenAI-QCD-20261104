import YM.Play.Quick
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Anomaly
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix
open scoped BigOperators Topology ContDiff Classical Matrix
variable {A B T: Type*}[Fintype A][Fintype B][Fintype T]{X U V:Finset A}{Z :Finset B}{n m i k:ℕ}
variable (Q:Matrix A A ℂ)
def clip (X:Finset A): Matrix A A ℂ:=of fun i j=> if i ∈ X ∧ j∈ X then Q i j else 0
lemma wandPosts (x:Alg A)(R: Matrix A A ℂ)(h:x∈region U)(hh:∀ i∈ U,∀ j∈U,Q i j=R i j): Wand Q x=Wand R x:=by
   unfold Wand; simp only [ContinuousLinearMap.sum_apply]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_; change Q i j • Creek.v j (Creek.v i x)= R i j • Creek.v j (Creek.v i x); by_cases hp:i∈ U; · by_cases ht:j∈U; rw [hh _ hp _ ht]; rw [lock j (preserves i h) ht]; simp
   rw [lock i h hp,map_zero]; simp -- after change.
lemma grainS (X:Finset A): Stays (Wand (clip Q X)) X:=by
   apply Stays.shine; intro i _; apply Stays.shine; intro j _; by_cases h:i∈ X∧j∈X; exact (gammaT h.2 h.1).pumps _
   rw [show clip Q X i j=0 from if_neg h]; erw [zero_smul ℂ (_:EndA A)]; apply Stays.paidO
lemma wand_keeps (x:Alg A)(h:x∈region X): Wand Q x∈region X:=by
   rw [wandPosts Q x (clip Q X) h (fun i hi j hj=> (if_pos (And.intro hi hj)).symm)]; exact (grainS Q X).keeps (Subset.refl _) x h
lemma breeze (P:Matrix A A ℂ)(x:Alg A)(hx:x∈region U)(hp:∀ i∈U,∀ j∈U,Q i j=P i j): birth (Wand Q) x= birth (Wand P) x:=by
    have h n: ((Wand Q)^n: EndA A) x∈region U:=by induction n with | zero=>simp [hx]| succ n he=> rw [pow_succ']; exact wand_keeps Q _ he
    have hz n : ((Wand Q)^n:EndA A) x=((Wand P)^n: EndA A) x:=by
        induction n with
        | zero=> simp
        | succ n hx=> rw [pow_succ',pow_succ',ContinuousLinearMap.mul_apply,wandPosts Q _ P (h n) hp,hx]; rfl
    exact (Stays.birther (Wand Q) x).unique ((Stays.birther (Wand P) x).congr_fun (fun i=>by simp only [ContinuousLinearMap.smul_apply,hz]))
lemma pantry (x y:Alg A)(h:x∈region U)(g:y∈region V)(hh:Disjoint U V)(hq:∀ i∈U,∀ j∈V,Q i j=0∧ Q j i=0)(hp: Plus x) (hr:Plus y):
   birth (Wand Q) (x*y) = birth (Wand Q) x* birth (Wand Q) y:=by
    let B:= clip Q U; let A':= clip Q V; have he : x*y∈region (U ∪ V):=Subalgebra.mul_mem _ (regionMon subset_union_left h) (regionMon subset_union_right g)
    rw [breeze Q (B+A') _ he (?_), breeze Q B x h (fun _ hi _ hj=> (if_pos (And.intro hi hj)).symm),breeze Q A' y g (fun _ hi _ hj=> (if_pos (And.intro hi hj)).symm),relay]; exact (grainS Q U).birthP.paysR (grainS Q V).birthP hh h g hp hr
    intro i hi j hj; let so := hh; have hb b(h:b∈ U): b∉ V:=Finset.disjoint_left.mp hh h; have ha b (h:b∈V):b∉ U:=Finset.disjoint_left.mp hh.symm h
    rcases mem_union.mp hi with hi|hi <;> rcases mem_union.mp hj with hj|hj
    · rw [Matrix.add_apply]; simp [B,A',clip,hi,hj,hb i hi]
    · rw [Matrix.add_apply]; simp [B,A',clip,hb i hi,ha j hj,(hq i hi j hj).1]
    · rw [Matrix.add_apply]; simp [B,A',clip,hb j hj,ha i hi,(hq j hj i hi).2]
    rw [Matrix.add_apply]; simp [B,A',clip,hi,hj,ha i hi]
open Cove
lemma bunk (M:Matrix A B ℂ)(x y:Patio A)(h:x.val∈region U)(g:y.val∈region V)(hh:Disjoint U V)(hq:∀ i∈U,∀ j∈V,Q i j=0∧ Q j i=0): splash M Q (x*y)= splash M Q x* splash M Q y:=by
   apply Subtype.ext; change changeVars M (birth (Wand Q) (x.val*y.val))=_; rw [pantry Q _ _ h g hh hq (bright x) (bright y),map_mul]; rfl
end YM.QCD.Anomaly
#print axioms YM.QCD.Anomaly.bunk
