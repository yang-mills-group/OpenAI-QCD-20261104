import YM.Lyre.Wick
import YM.Arise.Star
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV.Free.Lyre
open Function Filter MeasureTheory Lattice Wilson QCD QCD.Lat TensorProduct QCD.Grass Analysis YM.Arise.Range YM.Arise.Count Matrix Finset
open scoped Topology BigOperators ContDiff TensorProduct Matrix Matrix.Norms.L2Operator Kronecker Classical -- reorder
variable {d e n m:ℕ}(a:Axis) (p q:E4)
local notation "T"=> Ortho.motion (Signed.reflect a)
local notation "Ha"=> gamma a
lemma timbral (l:List Axis) :toneL a l = (-1:ℝ)^l.length * (-1:ℝ)^ (l.count a):=by
   induction l with
   | nil=> simp [toneL]
   | cons i l ih=> unfold toneL at *; rw [List.map_cons,List.prod_cons,ih]; rw [List.length_cons,pow_succ]; unfold tone; by_cases h:i=a; · subst i; rw [if_pos rfl,List.count_cons_self,pow_succ]; ring
                   rw [if_neg h,List.count_cons_of_ne h]; ring
lemma ears (P:Multi d): (steps P).count a= power P a:=by
   let F(t:Axis):= List.replicate (power P t) t
   have h(l:List Axis)(hl:l.Nodup): (l.flatMap F).count a=if a∈l then power P a else 0:=by
       induction l with
       | nil=>simp
       | cons i l ih=> rw [List.flatMap_cons,List.count_append,ih (List.nodup_cons.mp hl).2]; by_cases he:i=a; · subst i; simp [F,(List.nodup_cons.mp hl).1]
                       rw [show (F i).count a=0 from (by simp [F, List.count_eq_zero_of_not_mem,Ne.symm he])]; simp [Ne.symm he]
   simpa [steps,F] using h (List.finRange _) (List.nodup_finRange _)
noncomputable def boxL(x y:E4)(P:Multi d)(Q:Multi e):Spike:= ((-1:ℂ)^(steps Q).length) • deriveL (steps P++steps Q) spinor (x-y)
lemma coins (l:List Axis)(s t:Pinor)(hp:p≠0): derivatives l (dirac s t) p= deriveL l spinor p s t:=by
    let L:Spike→ₗ[ℝ]ℂ:= 
      { toFun:=fun i=> i s t,
        map_add':=fun _ _=>rfl,
        map_smul':=fun _ _=>rfl }
    have hl : dirac s t = L ∘ spinor:=funext fun i=> (spinor_at i s t).symm
    rw[hl]; exact spiral Maxwell.open_away spinor glow l L.toContinuousLinearMap p hp
lemma leds (h:p≠q)(i: SpinMode d)(j: SpinMode e): UV.Free.leg i j p q = if i.1.2.2=j.1.2.2 ∧ i.2=j.2 then boxL p q i.1.1 j.1.1 i.1.2.1 j.1.2.1 else 0:=by unfold UV.Free.leg boxL; rw [coins (p-q) _ _ _ (sub_ne_zero.mpr h)]; rfl
lemma led_box (h:p≠q)(x:E4) (P:Multi d)(Q:Multi e): let c:= (-1:ℂ)^(power P a+power Q a); c • (Ha*boxL (x+ T p) (x+ T q) P Q * Ha)=star (boxL q p Q P):=by
    intro c; unfold boxL; let l:=steps P; let r:=steps Q
    have he:(l++r).length = l.length+r.length :=List.length_append -- syntax
    let b:ℝ:=toneL a (l++r); have hz:q-p≠0:=sub_ne_zero.mpr (Ne.symm h)
    have hb : (b:ℂ) = (-1:ℂ)^(l.length+r.length)* c:=by unfold b c; rw [timbral, List.count_append,ears,ears,he]; push_cast; rfl -- match ears reduc
    let M:= deriveL (l++r) spinor (anti a (q-p)); let S:= deriveL (l++r) spinor (q-p)
    have h₂:deriveL (r++l) spinor (q-p)=S:= commute_a Maxwell.open_away spinor glow _ _ (List.perm_append_comm ..) _ hz
    rw [show x+T p-(x+T q)=anti a (q-p) from by change _= -(T _); rw[map_sub]; abel, show deriveL (steps Q ++ steps P) spinor (q-p)=S from h₂]; rw [Matrix.mul_smul,Matrix.smul_mul]
    rw [star_smul]; simp only [star_pow, star_neg,star_one]; change c • (-1:ℂ)^r.length • (Ha*M*Ha)=(-1:ℂ)^l.length • star S; rw [show star S = b • (Ha*M*Ha) from (pitchL a (q-p) hz (l++r)).symm]; change c • (-1:ℂ)^r.length • (Ha*M*Ha)=(-1:ℂ)^l.length • (b:ℂ) • (Ha*M*Ha); rw [smul_smul,smul_smul]; congr 1; rw [hb,pow_add]; have hh: (-1:ℂ)^l.length * (-1:ℂ)^l.length=1:=by rw[←sq,← pow_mul, mul_comm, pow_mul]; simp
    calc _= ((-1:ℂ)^l.length * (-1:ℂ)^l.length)* c*(-1:ℂ)^r.length:=by rw [hh,one_mul]
         _ = _:=by ring
-- flip transforms of block
lemma wire (i j: SpinMode d) (S:Spike): flipTable a S i j=(if j.2=i.2 ∧ j.1.1=i.1.1 ∧ j.1.2.2=i.1.2.2 then (-1:ℂ)^power i.1.1 a * S i.1.2.1 j.1.2.1 else 0):=by unfold flipTable spinTable wave; simp only [Matrix.of_apply]; split_ifs with hs he ht <;> simp_all [Matrix.kroneckerMap_apply,Matrix.one_apply,Ne.symm] -- edit
lemma plugged (X:Spike)(V: SpinMode d→ℂ) (i:SpinMode d):∑ j:SpinMode d, flipTable a X i j * V j=∑ j:Pinor, (-1:ℂ)^power i.1.1 a* X i.1.2.1 j * V ((i.1.1,(j,i.1.2.2)),i.2):=by
    simp_rw [wire a]; rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; simp only [ite_mul,ite_and]; simp
noncomputable abbrev axisL (p q:E4)(d e:ℕ): Matrix (SpinMode d) (SpinMode e) ℂ:= Matrix.of fun i j=> UV.Free.leg i j p q
lemma oriented (h:p≠q)(x:E4) (d e:ℕ) : flipTable (d:=d) a (-Ha) * axisL (x+T p) (x+T q) d e * (flipTable (d:=e) a (-(Ha).transpose)).transpose=(axisL q p e d)ᴴ:=by
    let P:= x+T p; let Q:=x+T q; let V:=axisL P Q d e; let U:=flipTable a (-Ha) (d:=d); let W:=flipTable a (-Haᵀ) (d:=e)
    apply Matrix.ext; intro i j
    let X:= i.1.1; let Y:=j.1.1; let u:= i.1.2; let v:=j.1.2
    have h₁(k:SpinMode e): (U*V) i k=∑ s:Pinor,(-1:ℂ)^power X a* (-Ha u.1 s)* V ((X,(s,u.2)),i.2) k:=by change ∑ s:SpinMode d, U i s* V s k=_; exact plugged a (-Ha) (fun s=>V s k) i
    change (U*V*Wᵀ) i j=_; rw [Matrix.mul_apply]; simp_rw [Matrix.transpose_apply,mul_comm ((U*V) i _)]
    rw [show (∑ k:SpinMode e,W j k * (U*V) i k)= _ from plugged a (-(Ha).transpose) (fun k=>(U*V) i k) j]; simp_rw [h₁]; let c:=(-1:ℂ)^power X a; let b:=(-1:ℂ)^power Y a
    change ∑ t:Pinor,b* (-Ha t v.1)* (∑ s:Pinor,c *(-Ha u.1 s)* UV.Free.leg ((X,(s,u.2)),i.2) ((Y,(t,v.2)),j.2) P Q) = star (UV.Free.leg j i q p)
    have h₂:P ≠ Q:= fun he=> h ((T).injective (add_left_cancel he)); simp_rw [leds P Q h₂, leds q p (Ne.symm h)]; by_cases he: u.2=v.2 ∧ i.2=j.2
    · simp_rw [if_pos he]; rw [if_pos (And.intro (show j.1.2.2=i.1.2.2 from he.1.symm) he.2.symm)]
      let G:=boxL P Q X Y; let Z:=boxL q p Y X
      have hw: (c*b) • (Ha*G*Ha)=star Z:=by have hw:=led_box a p q h x X Y; dsimp only at hw; rw[pow_add] at hw; exact hw
      change _=star (Z v.1 u.1); have hx:star (Z v.1 u.1)=(c*b)* (Ha*G*Ha) u.1 v.1:= (congrFun (congrFun (show (c*b) • (Ha*G*Ha)=star Z from hw) u.1) v.1).symm; rw [hx]
      simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]; refine sum_congr rfl fun t _=> ?_; refine sum_congr rfl fun s _=> ?_; change _*(_*G s t)=_; ring
    simp_rw [if_neg he]; rw [if_neg (fun ⟨hV,hQ⟩=> he ⟨hV.symm,hQ.symm⟩)]; simp
end YM.Massive.UV.Free.Lyre
#print axioms YM.Massive.UV.Free.Lyre.oriented
