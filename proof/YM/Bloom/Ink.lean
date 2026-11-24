import YM.Bloom.Pulse
import YM.Arise.Gam
import YM.Arise.Star
/-! # Ledger of every basis participant. Family preselection. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bloom
open Function Lattice Laurent Bloch Metric RG Filter
open Finset YM.Bank Precision Matrix Exterior Arise Arise.Range Jar
open YM.Bank.Jule Ivo Pic Maxwell Hypnos Hypnos.Fruit TreeP
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {G:Gauge}{c f:Side}{k m j B r n D d:ℕ}{X Y Z:Type}
abbrev Zinc (G:Gauge)(d:ℕ) := Arise.Range.Tube G d
abbrev stemP {G: Gauge} (p: Zinc G d):=List.ofFn p.1.2.2
noncomputable def glimpse (p:Zinc G d):Parc:=came (chore d (stemP p) p.1.2.1)
lemma pongs (p:Zinc G d): (stemP p).length=p.1.1.val:=List.length_ofFn
lemma rare (p:Zinc G d) : (stemP p).length ≤ d:=(pongs p).trans_le (Nat.le_of_lt_succ p.1.1.isLt)
lemma gems (p: Zinc G d): Rocky (some p.1.2.1) (stemP p) d (glimpse p):=per_goal _ _ (rare p) -- syntax
lemma laid (p:Zinc G d): glimpse p∈tails (stemP p).length (d+1):=recovered _ _ _ _ (rare p) (gems p)
noncomputable def voteP (c:Side)(p: Zinc G d)(x:Cover): Matrix Unit (Col G c) ℂ:= pupil G c x p.1.2.1 p.2 (glimpse p)
noncomputable def tollP (p: Zinc G d):=fareV G 2 (flet (glimpse p))*pattern (glimpse p)
lemma toll_pos (p: Zinc G d): 0 ≤ tollP p:=by unfold tollP fareV; exact mul_nonneg (by positivity) (valor_g _)
lemma venture (c:Side)(p:Zinc G d)(x:Cover): cusp (voteP c p x) () ≤ tollP p:= purse0 (glimpse p) x p.2 p.1.2.1
noncomputable def viewK (p:Zinc G d)(q: Zinc G m)(x:E4):ℂ:=(legKernel (runeV p) (runeV q) x:ℝ)
lemma vicar (p:Zinc G d) (q:Zinc G m) (x:E4): viewK p q x= (legKernel (dollar (stemP p).length (p.1.2.1,(stemP p).get) p.2) (dollar (stemP q).length (q.1.2.1,(stemP q).get) q.2) x:ℂ):=by
    let M(n:ℕ)(p:Arise.Range.Proto n)(i:G.ColorIndex) := dollar n p i
    have ht(k j:ℕ)(hm: j=k)(p:Proto k)(i:G.ColorIndex)(l:PlaqAxes)(f:Fin j→Axis)(h₁:l=p.1)(hx:∀ v,p.2 (Fin.cast hm v)=f v): HEq (dollar k p i) (dollar j (l,f) i):=by
            subst hm; apply heq_of_eq; apply congr_arg (fun (a:Proto j)=> dollar j a i); exact Prod.ext h₁.symm (funext hx)
    have hx {d:ℕ}(p:Zinc G d) : HEq (runeV p) (dollar (stemP p).length (p.1.2.1,(stemP p).get) p.2):=ht _ _ (pongs p) _ _ _ _ rfl (fun v=>by ext <;> simp [stemP] <;> rfl)
    have hi(i j k l:ℕ)(u:Probe G i)(v:Probe G j)(w:Probe G k)(t:Probe G l)(hi:i=k)(hj:j=l)(hw:HEq u w)(hv:HEq v t): legKernel u v x=legKernel w t x:=by subst hi; subst hj; rw [eq_of_heq hw,eq_of_heq hv]
    exact congr_arg Complex.ofReal (hi _ _ _ _ _ _ _ _ (pongs p).symm (pongs q).symm (hx _) (hx _))
lemma collection {H:Type*}[Fintype H] (f:H→ℝ→Prop)(h:∀ i,∃ C:ℝ,0≤ C∧f i C)(hm:∀ i s t, f i s→s ≤ t→ f i t) :∃ C:ℝ, 0≤ C ∧ ∀ i,f i C:=by
     choose C hc H using h; exact ⟨∑ i,C i,sum_nonneg fun i _=>hc i,fun i=>hm i _ _ (H i) (single_le_sum (fun i _=>hc i) (mem_univ _))⟩
lemma firstP {H:ℕ→ Type}(f:(i:ℕ)→H i→ℝ→ Prop) (inst:∀ i,Fintype (H i))(h:∀ i≤ D,∀ v:H i,∃ C:ℝ,0≤ C ∧ f i v C)(ht:∀ i (h:i ≤ D) (j:H i) (u v:ℝ), f i j u→ u ≤ v→f i j v): ∃ C:ℝ,0≤ C ∧ ∀ i≤D,∀ v:H i, f i v C:=by
     let K:= Sigma (fun i:Fin (D+1)=>H i.val); let T:=fun i:K=>f i.1.val i.2
     obtain ⟨C,hc,h'⟩:= collection T (fun i=> h _ (Nat.le_of_lt_succ i.1.isLt) _) (fun i=> ht _ (Nat.le_of_lt_succ i.1.isLt) _); exact ⟨C,hc,fun i hi v=>h' ⟨⟨i,Nat.lt_succ_of_le hi⟩,v⟩⟩
lemma pairBill {H:ℕ→ Type}(f:(i j:ℕ)→ H i→H j→ℝ→ Prop)(inst:∀ i,Fintype (H i))(h:∀ i≤D,∀ j≤D,∀ (u:H i)(v:H j),∃ C:ℝ,0≤ C ∧ f i j u v C)(ht:∀ i≤D,∀ j≤D,∀ (u:H i)(v:H j) x y, f i j u v x→ x≤ y→ f i j u v y):∃ C:ℝ,0 ≤ C∧∀ i≤D,∀ j≤D,∀ (u:H i)(v:H j), f i j u v C:=by
     let K:= fun (i:ℕ) (u:H i)(C:ℝ)=>∀ j≤D,∀ v:H j,f i j u v C
     obtain ⟨C,hc,H'⟩:=firstP K inst (fun i hi u=>firstP (D:=D) (fun j v=>f i j u v) inst (fun j hj v=>h i hi j hj u v) (fun j hj v=>ht i hi j hj u v)) (fun i (hi:i ≤ D) j u v he hp i' hi' j'=>ht i hi i' hi' j j' u v (he i' hi' j') hp)
     exact ⟨C,hc,fun i hi j hj u v=>H' i hi u j hj v⟩
end YM.Bloom
#print axioms YM.Bloom.pairBill
#print axioms YM.Bloom.vicar
