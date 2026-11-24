import YM.Parishes.Braid
import YM.Parishes.Stair
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {u s t a θ v A' D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c f L:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
namespace Stamp
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle
variable {I J K E Uv Fv Zt:Type}
variable (H:TaperHol){U:Hol su}(A:Exhibit U)(b:Cover)
variable (x y:Label d) (q:Bool) (Pt:BudgetPoint)
set_option quotPrecheck false
namespace Stair
variable {w w' a b c₁ d₁ e y₃ ε ε' ε₁:ℝ}{Pt P Q R:BudgetPoint}
local notation "Wd" => fun (i:Jars d)=> u^(weightJ i)*princS x i P w
local notation "Sd"=>toted u x P w
local notation "W₁"=>wealth y.val Q.threshold w'
local notation "Wi"=>wealth x.val P.threshold w
variable {x y}
variable (x y)
-- exactly the quadratic spin lanes of the perturbation.V asset typ d can be any. hi used with d=8. coord powers.
structure OffS (x:Label d) :Prop where
    route (i: Rings d)(hp:coord i.val x.val≠0): crest i.val=(6,0,2) ∨ crest i.val=(8,0,2)
noncomputable def laps (k:ℕ)(x:Label d) :ℝ:= ∑ i:Rings d, (if weight i.val=k then ‖coord i x.val‖ else 0)
noncomputable def ripen (k:ℕ)(t:ℝ)(x y: Label d):ℝ:= laps k (y-(t:ℂ) • x)
lemma sailF (i:Jars d)(e:Rings d) (he:crest e.val≠i.val) : princS x i P w ≥0 := wealth_ge ..
lemma worthQ (e:Rings d)(h:OffS x): chartL P w e x= (w:ℂ)^2*coord e.val x.val:=by
    change coord _ (Sieve.widths _ _ _) = _; rw [rank_fee, Submodule.subtype_apply]; by_cases hh:coord e.val x.val=0; · rw [hh,mul_zero,mul_zero]
    have hp: (crest e.val).2=(0,2):=by rcases h.route e hh with hp|hp<;>rw[hp]
    rw [show life e.val.1=0 from congr_arg Prod.fst hp, show e.val.2.card=2 from congr_arg Prod.snd hp,pow_zero,one_mul]
-- allow jars not found empty early.W output constraints
noncomputable def pathC (k:ℕ)(x:Label d):ℝ:=∑ i:Rings d, if crest i.val=(k,0,2) then ‖coord i.val x.val‖ else 0
lemma moods (k:ℕ)(h:OffS x): pathC k x=laps k x:=by
    refine Finset.sum_congr rfl ?_; intro i _; by_cases he: UV.weight i.val=k
    · rw [if_pos he]; by_cases hg: coord i.val x.val=0; · rw [hg,norm_zero,ite_self]
      have hp:(crest i.val).2=(0,2):= (h.route i hg).elim (fun h=>congr_arg _ h) (fun h=>congr_arg _ h)
      exact if_pos (Prod.ext he hp)
    rw [if_neg he]; exact if_neg (fun h=> he (congr_arg Prod.fst h))
lemma fruits (k:ℕ)(h:OffS x)(hv:0≤ w): ∑ i∈Finset.univ.filter (fun i:Jars d=>weightJ i=k), princS x i P w=w^2*laps k x:=by
    let f(i:Jars d):= gradeCut d i.val x; let T:= Finset.univ.filter (fun i:Jars d=>weightJ i=k); let g(i):=w^2 * ‖coord (i:Rings d).val x.val‖
    unfold princS wealth laps; rw [sum_comm,Finset.mul_sum]; refine sum_congr rfl fun i _=>?_; let k':Jars d:= ⟨crest i.val, mem_image_of_mem _ i.property⟩; have hh(j:Jars d): Stative.fare i (f j).val P.threshold w= chartL P w i (f j):= rfl
    have hp(j:Jars d): Stative.fare i.val (gradeCut d j.val x).val P.threshold w=if k'=j then chartL P w i x else 0:=by
       change chartL P w i (gradeCut d j.val x)=_; rw[wpS]; by_cases h:k'=j; · rw [if_pos h,if_pos (congr_arg Subtype.val h)]
       rw [if_neg h,if_neg (fun hp=> h (Subtype.ext hp))]
    simp_rw [hp]; by_cases he:UV.weight i.val=k
    · rw [if_pos he,sum_eq_single k']
      · rw[if_pos rfl,worthQ _ _ h,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hv];
      · intro j hj hg; rw [if_neg hg.symm,norm_zero]
      exact fun ht=> (ht (mem_filter.mpr ⟨mem_univ _,he⟩)).elim
    rw [if_neg he,mul_zero]; exact sum_eq_zero fun j hj=>by rw [if_neg (fun (h:k'=j)=>he ((congr_arg weightJ h).trans ((mem_filter.mp hj).2))),norm_zero]
-- full normalized step diagonal. lower contamination term only from 6 into 8. This proof utility.Better any k.
lemma fare_lane (e:Rings d)(hx:TypeBeta u w w' v a ε ε' P Q x y)(hw:0≤u)(ha:0≤a)(he:0≤ε): ‖chartL Q w' e y- (u:ℂ)^weight e.val *chartL Q v e x‖ ≤ (∑ j∈Finset.univ.filter (fun j:Jars d=>weightJ j<weight e.val), a*u^(weightJ j)*princS x j P w)+ε*Wi+ε':=by
     obtain ⟨f,h1,h2⟩:= hx.paid; let T:=chartL Q w' e; let X:= chartL Q v e; let k:=UV.weight e.val; let g:= (u:ℂ)^k; let z:=y-∑ j,f j; let F(j:Jars d):=T (f j) - g * X (gradeCut d j.val x); have hf :T y - g*X x=(∑ i,F i)+T z:=by unfold F z; rw [sum_sub_distrib, map_sub,map_sum,← mul_sum, ← map_sum X,sumCut]; abel
     let A(j:Jars d):=a*u^weightJ j*princS x j P w; let B(j:Jars d):=ε *princS x j P w; have h(j:Jars d): ‖F j‖ ≤ (if weightJ j<k then A j else 0)+ B j :=by
          unfold F; by_cases he':weightJ j<k; swap; · rw[if_neg he',zero_add]; exact (h1 j).2 e (le_of_not_gt he')
          rw [if_pos he',show X (gradeCut d j.val x)=0 from (wpS x e j).trans (if_neg (fun hu=> he'.ne ((congr_arg Prod.fst hu).symm))),mul_zero,sub_zero]; exact ((fare_cap e _ _ _).trans (h1 j).1).trans (le_add_of_nonneg_right (mul_nonneg he (wealth_ge ..)))
     change ‖T y-g * X x‖ ≤_; rw[hf]; refine (norm_add_le ..).trans (add_le_add ((norm_sum_le ..).trans ((sum_le_sum (fun i _=>h i)).trans_eq ?_)) ((fare_cap e z.val _ _).trans h2))
     rw [sum_add_distrib, Finset.sum_filter,coinsS,Finset.mul_sum]; rfl
end Stair
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.fare_lane
