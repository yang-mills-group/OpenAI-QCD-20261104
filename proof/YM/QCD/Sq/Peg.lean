import Mathlib.Topology.TietzeExtension
import Mathlib.Tactic
/-!
# Square face zero lemma for two coupling coordinates
Integer winding on square triangulation, using closed full-face boundary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sq
open Filter Function Set Finset
open scoped Topology Classical BigOperators
abbrev Tate:= Set.Icc (- (1:ℝ)) 1
abbrev Twin:= Tate × Tate
local notation "𝔹" => Twin
noncomputable def tail (z: Twin):ℝ:=z.1
noncomputable def mast (z:Twin):ℝ:=z.2
lemma shore (z:Twin): |tail z|≤1∧ |mast z| ≤1:=⟨abs_le.mpr z.1.2,abs_le.mpr z.2.2⟩
@[fun_prop] lemma cont_tail : Continuous tail:= continuous_subtype_val.comp continuous_fst
@[fun_prop] lemma cont_mast : Continuous mast:=continuous_subtype_val.comp continuous_snd
abbrev both:= ({ x:ℝ×ℝ|x.1∈ Tate ∧ x.2∈ Tate}: Set _)
inductive Dir where
 | right|up|left|down
 deriving Fintype, DecidableEq
open Dir
noncomputable def coat (v:𝔹):Dir:= if |mast v| ≤ |tail v| then (if 0 ≤ tail v then right else left) else (if 0 ≤ mast v then up else down)
def rev : Dir →Dir
 | right=>left|left=>right|up=>down|down=>up
def turn : Dir→Dir
 | right=>up|up=>left|left=>down|down=>right
def tick (i j:Dir):ℤ := if j=turn i then 1 else if i=turn j then -1 else 0
lemma invol (x:Dir): rev (rev x)=x:=by cases x<;>rfl
lemma cyclic (x y:Dir): tick x y= -(tick y x):=by cases x<;>cases y<;>decide
lemma reflx (x:Dir): tick x x=0:=by cases x<;>decide
lemma closes (x y z:Dir) : y≠rev x→ z≠ rev y→ z≠ rev x→ tick x y+tick y z=tick x z :=by
   cases x <;>cases y<;>cases z<;>decide
noncomputable def floor (z:Twin):ℝ:=max |tail z| |mast z|
noncomputable def tinted (x:Twin)(p:Dir):ℝ:=match p with
 | right=> tail x | left=> -tail x|up=>mast x|down=> -mast x
lemma tin (z:Twin):tinted z (coat z)=Sq.floor z:=by
    unfold coat Sq.floor; split_ifs with h hp hp₀; · rw [max_eq_left h,abs_of_nonneg hp]; rfl
    · rw [max_eq_left h,abs_of_nonpos (le_of_not_ge hp)]; rfl
    rw [max_eq_right (le_of_not_ge h),abs_of_nonneg hp₀]; rfl
    rw [max_eq_right (le_of_not_ge h),abs_of_nonpos (le_of_not_ge hp₀)]; rfl
lemma reverses (z:Twin)(p:Dir): tinted z (rev p)= - tinted z p:=by cases p<;> simp [rev,tinted]
lemma metric (x y:Twin): dist x y= max (dist (tail x) (tail y)) (dist (mast x) (mast y)):=rfl
lemma closeT (z w:Twin){t:ℝ} (h:dist z w<t)(hp:t≤ Sq.floor z)(ht:t≤Sq.floor w)(hz:0 <t): coat w ≠ rev (coat z):=by
   intro he; let i:=coat z; have hp' : -tinted w i=Sq.floor w:=by rw [← reverses,show rev i=coat w from he.symm,tin]
   have he' :dist (tinted z i) (tinted w i)<t:=by
       rw [metric,max_lt_iff] at h; cases i; exact h.1; exact h.2; · simpa [tinted] using h.1
       simpa [tinted] using h.2
   rw [Real.dist_eq] at he'; change _ <_ at he'; have hh:=tin z; linarith only [hp,hz,ht,hp', (abs_lt.mp he').2, (tin z)]
lemma leftX (x:Twin)(h:tail x= -1) : coat x=left:=by unfold coat; simp only [h,abs_neg,abs_one]; rw [if_pos (shore _).2, if_neg]; linarith
lemma rightX (x:Twin)(h:tail x=1) : coat x=right:=by unfold coat; simp only [h,abs_one]; rw [if_pos (shore _).2, if_pos]; norm_num
lemma downX (x:Twin)(h:mast x=-1) : coat x ≠ up:=by unfold coat; rw [h]; split_ifs with h hp hp; all_goals first | decide | linarith
lemma upX (x:Twin)(h:mast x=1) : coat x ≠ down:=by unfold coat; rw [h]; split_ifs with h hp hp; all_goals first| decide| linarith
def pl : Dir→ℤ|left=>0|down=>1|right=>2|up=>1
lemma lower (x y:Dir): x≠up → y≠up → y≠ rev x → tick x y=pl y-pl x:=by cases x<;>cases y<;> decide
lemma upper (x y:Dir): x≠down → y≠down → y≠rev x→ tick x y=pl x-pl y:=by cases x<;>cases y<;>decide
lemma rect (n:ℕ) (F:ℕ→ℕ→ Dir) (h:∀ i<n,∀ j<n,
        F (i+1) j≠ rev (F i j)∧ F i (j+1)≠rev (F i j)∧F (i+1) (j+1)≠rev (F i (j+1))∧ F (i+1) (j+1)≠rev (F (i+1) j)∧ F (i+1) (j+1)≠rev (F i j)) (hl:∀ i≤n,F 0 i=left)(hr:∀ i ≤ n,F n i=right)(hn:∀ i≤ n,F i 0≠up)(ht:∀ i≤ n,F i n≠down)(he:0 <n) : False :=by
     let k (i j:ℕ):= tick (F i j) (F (i+1) j); let x(i j:ℕ):=tick (F i j) (F i (j+1)); let t(j:ℕ):=∑ i ∈ Finset.range n,k i j
     have hK (j:ℕ)(hj:j<n): t (j+1)=t j:=by
           have hg(m)(hm:m < n): k m j+x (m+1) j=x m j+k m (j+1):=by
              obtain ⟨h1,h2,h3,h4,h5⟩:= h m hm j hj; exact (closes _ _ _ h1 h4 h5).trans (closes _ _ _ h2 h3 h5).symm
           have hh(m:ℕ)(hm:m ≤ n) : (∑ i∈ Finset.range  m,k i (j+1))+ x 0 j = (∑ i∈ Finset.range  m,k i j)+x m j:=by
                 induction m with | zero=>rfl | succ i ih=> rw [sum_range_succ,sum_range_succ]; linarith only [ih (by omega),hg i (by omega)]
           unfold t; have hp : x 0 j=0:=by unfold x; rw [hl j (by omega), hl _ (by omega),reflx];
           have he :x n j=0:=by unfold x; rw [hr j (by omega),hr _ (by omega),reflx]
           linarith only [hh n (by omega),he,hp]
     have hd (i:ℕ)(hi:i≤n):t i=t 0:=by induction i with|zero=>rfl|succ i ih=> rw [hK _ (by omega),ih (by omega)]
     have hg(i:ℕ)(hp:i ≤ n) :(∑ j∈ Finset.range  i,k j 0)=pl (F i 0)-pl (F 0 0)∧ (∑ j∈ Finset.range  i,k j n)=pl (F 0 n)-pl (F i n):=by
         induction i with
         | zero=> simp
         | succ i ih=>
             obtain ⟨hl,hr⟩:=ih (by omega); rw [sum_range_succ,sum_range_succ,hl,hr]
             have hz : F (i+1) n≠ rev (F i n):=by have hx:= (h i (by omega) (n-1) (by omega)).2.2.1; rwa [show n-1+1=n by omega] at hx
             unfold k; rw [lower (F i 0) _ (hn _ (by omega)) (hn _ hp) (h i (by omega) 0 he).1,upper (F i n) _ (ht _ (by omega)) (ht _ hp) hz]; omega
     obtain ⟨h0,h1⟩:= hg n le_rfl
     rw [hl 0 (by omega),hr 0 (by omega)] at h0; rw [hl n le_rfl,hr n le_rfl] at h1; have h:= hd n le_rfl; unfold t at h; rw [h0,h1] at h; norm_num [pl] at h
end YM.QCD.Sq
