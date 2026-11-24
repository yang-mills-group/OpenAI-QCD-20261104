import YM.Topaz.Room
import YM.Alum.Greet
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace CardsT
open QCD QCD.Lat Tide Plum QCD.Grass MassiveQCD Cupola Sample LoomT
variable (S:Scheme){c:Side}{F:ℕ}{j k p N:ℕ}(x:Cover)(a:Averaging)(X: Cover→ Stud c F)
variable (T:Tiling c)(R:Regulator c F)(v:T.Cell) (z:ℝ)
set_option quotPrecheck false
local notation "V" k:arg=> Hole Unit S j k
-- Recover sparse average at fixed ℓ as probability on any BOX flex. neutral orientation simultaneous. no L^ step issues
variable {Y:Type} [AddCommGroup Y][Module ℝ Y]
local notation "Au"=> (fun _ : Unit=>a)
local notation "L"=> (fun _:Unit=>x)
local notation "Ψ" k:arg=>showX S j k (fun _:Unit=>x)
variable (hy: Cover→ Y)
-- weights may depend actual insertion. no issue.
lemma fortune (hi:j≤ p)(he:p ≤ k)(u:Hole Unit S j p):∃ t:Hole Unit S j k→ℝ,(∀ i,0≤ t i) ∧ (∑ i,t i)=1 ∧ earnL S j k p L (fun _:Unit=>a) (fun _=> hy) u=∑ i,t i • hy ((Ψ k) i):=by -- arg order Check.B
       induction he using Nat.decreasingInduction with
       | self=>
              let g(i:Hole Unit S j k):= if i=u then (1:ℝ) else 0; refine ⟨g,fun i=>by dsimp[g]; split <;> norm_num, by simp[g],?_⟩; simp_rw[receive S j k L Au]; simp[g,ite_smul]
       | of_succ m hm ih=>
              obtain ⟨g,h⟩:= allS S j m L (fun _=>a) hi
              let E:= To (link S j m L) u; choose f h1 h2 h3 using fun i:E=> ih (show j ≤ m+1 from Nat.le_step hi) i.val
              let d(i:E):= g i.val u; let b(v:Hole Unit S j k):= ∑ i:E,d i*f i v
              refine ⟨b,fun i=> Finset.sum_nonneg (fun _ _=>mul_nonneg (h.cash ..) (h1 ..)),?_,?_⟩
              · unfold b; rw [sum_comm]; conv_lhs=> arg 2; intro i; rw [← mul_sum,h2 i,mul_one]
                exact h.bill u
              rw [towers S j k m L Au g h (fun _=>hy) hm]; change ∑ i:E, d i • _=_
              simp_rw[h3, Finset.smul_sum]; rw [sum_comm]; exact sum_congr rfl fun i _=>by unfold b; rw [sum_smul]; exact sum_congr rfl fun k _=>(mul_smul ..).symm
lemma strummed (hp:j≤ k):∃ t:↥(box (CardsT.flex S j k))→ℝ,(∀ i,0≤ t i) ∧(∑ i,t i)=1 ∧ Averaging.filter a (ratioTo S k j) hy (ratioTo S k j • x)=∑ i,t i • hy (ratioTo S k j • x+i.val):=by
     obtain ⟨g,h0,h1,h⟩:=fortune S x a hy (p:=j) le_rfl hp (u:=⟨(),0,Lattice.center_box _⟩); let f(i: ↥(box (CardsT.flex S j k))):=g ((),i); refine ⟨f,fun i=> h0 _, ?_,?_⟩
     · rw[Fintype.sum_prod_type] at h1; exact Fintype.sum_unique (ι:=Unit) _|>.symm.trans h1
     rw[firstE,Fintype.sum_prod_type,Fintype.sum_unique (ι:=Unit)] at h; exact h
open Goblet
-- any average in authorized footprint, yields Fence/Potion/cost. no packing assumption.
lemma shelter {A:Type}(s:Finset A)(f:A→ Stud c F)(S:Set (Site c))(h:∀ i ∈ s,Fence S (f i)): Fence S (∑ i∈s,f i) :=by
     induction s using Finset.induction_on with
     | empty=> simp only [sum_empty]; simpa using (Fence.one (F:=F) (A:=S)).mass (0:ℂ)
     | insert a s ha ih=> rw[sum_insert ha]; exact (h a (mem_insert_self ..)).add (ih fun _ h'=>h _ (mem_insert_of_mem h'))
lemma sturdyR {A:Type*}[Fintype A](g:A→ℝ)(F':A→Stud c F)(hg:∀ i,0≤ g i)(hm:(∑ i,g i)=1)(q:Bool)(ho:∀ i,Fence (T.chamber v) (F' i))(hQ:∀ i W,Grass.Hom q (F' i W))(hs:Smoke T R)(hZ:∀ i,topH T R (F' i) v ≤ z): topH T R (∑ i:A,g i • F' i) v ≤ z:=by
    let x(i:A) := (↑(g i):ℂ) • F' i; change topH T R (∑ i,x i) v ≤ _ -- defeq
    apply (bills T R v x (fun i=> (ho i).mass _) (fun i=> ⟨q,fun U=> (hQ i U).smul _⟩) hs.real hs.seam hs.pos hs.cycle).trans
    refine (sum_le_sum (g:=fun i=>g i*z) fun i hi=>?_).trans_eq (?_)
    · rw [show topH T R (x i) v= _ from colorL _ _ (F' i) v (g i),abs_of_nonneg (hg i)]; exact mul_le_mul_of_nonneg_left (hZ i) (hg i)
    rw [← sum_mul,hm, one_mul]
end CardsT
end YM.Intag
#print axioms YM.Intag.CardsT.sturdyR
#print axioms YM.Intag.CardsT.shelter
#print axioms YM.Intag.CardsT.strummed
