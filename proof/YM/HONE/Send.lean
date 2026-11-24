import YM.Intag.Summer
import YM.Profiles.Standards
import YM.TIPS.Fall
import YM.Patria.Sunrise
/-!
# exact averaged impulses at any step. real signage. Beam through large ratios
-/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.CardsT
open Function Filter Finset MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Lat QCD.Tide Push.GridApprox
open MassiveQCD.Cupola MassiveQCD.Sample MassiveQCD Sample.LoomT Sample.Quills
open scoped BigOperators Classical
variable (S:Scheme)(R:Side)(ℓ i k:ℕ){I:Type} [Fintype I]
variable (X:I→ Cover) (U:I→ Averaging)
local notation "H" k:arg=> Hole I S ℓ k
local notation "p" k:arg=> showX S ℓ k X
local notation "L" k:arg=> CardsT.link S ℓ k X
variable (w:Hole I S ℓ (k+1)→Hole I S ℓ k→ℝ)
-- Product sum, preserving ordered Grass charges. beans real orientation cost.
lemma choral {I J E:Type}[Fintype I][Fintype J][Ring E][Algebra ℂ E]{r:I→J→Prop}(g:I→J→ℝ)(F:I→E)(N:ℕ)(s:Fin N→J) : ((List.ofFn (fun j:Fin N=> ∑ i:LoomT.To r (s j),(↑(g i.val (s j)):ℂ) • F i.val))).prod=∑ u:Queue r s, beans r g s u • (List.ofFn (fun j=> F (attends r s u j))).prod:=by
     induction N with
     | zero=>rw [Fintype.sum_unique (ι:=∀ i:Fin 0, LoomT.To r (s i))]; simp [beans]
     | succ n ih=>
       let t:=Fin.tail s; let a:=s 0; let e:=Fin.consEquiv (fun i:Fin (n+1)=>LoomT.To r (s i))
       rw [← e.sum_comp,Fintype.sum_prod_type,List.ofFn_succ,List.prod_cons]; change ((∑ i:LoomT.To r a, (↑(g i.val a):ℂ) • F i.val)*(List.ofFn (fun j:Fin n=> ∑ i:LoomT.To r (t j),(↑(g i.val (t j)):ℂ) • F i.val)).prod)=_; rw [ih t,sum_mul]; refine sum_congr rfl fun j _=>?_ ; rw [mul_sum]; refine sum_congr rfl fun k _=>?_
       let u:Queue r s:= e (j,k); have hf: attends r s u 0=j.val:= rfl
       have hq: Fin.tail (attends r s u)= attends r t k:=funext (fun i=>by change ((@Fin.cons n (fun i:Fin (n+1)=> To r (s i)) j k) i.succ).val=_; simp [attends])
       have hp : beans r g s u=(↑(g j.val a):ℂ)*beans r g t k:=by unfold beans; rw [Fin.prod_univ_succ]; refine congr_arg ((↑(g j.val a):ℂ)*·) (prod_congr rfl fun i _=>?_); change (↑(g _ (s i.succ)):ℂ)=_; rw [show attends r s u i.succ=_ from congr_fun hq i]; rfl
       change _=beans r g s u • _; rw[List.ofFn_succ (n:=n), List.prod_cons,hp,hf,smul_mul_assoc,mul_smul_comm,mul_smul]; rw [show (fun i:Fin n=> F (attends r s u i.succ))=(fun i=> F (attends r t k i)) from funext fun i=>congr_arg F (congr_fun hq i)]
open Massive.Patria Massive.Patria.Depth Massive.Patria.Rolls
-- universal linear receiver Y (any ℝ-space). depth ledger φ coordinates. choose once for all n.
variable {Y:Type}[AddCommGroup Y] [Module ℝ Y]
noncomputable abbrev earnL (F:I → Cover → Y)(v:H k):Y:= Averaging.filter (U v.1) (ratioTo S i k) (F v.1) (ratioTo S i k • (showX S ℓ k X v))
set_option quotPrecheck false
local notation "ψ" k:arg=> earnL S ℓ i k X U
variable (hw: SignedWeights S ℓ k X U w)
include hw
set_option maxHeartbeats 480000 in
lemma towers (F:I → Cover → Y)(he:k < i)(v:H k): earnL S ℓ i k X U F v=∑ j:MassiveQCD.Sample.LoomT.To (CardsT.link S ℓ k X) v, w j.val v • (earnL S ℓ i (k+1) X U F j.val):=by
   unfold earnL; rw [step_factor he, Massive.Patria.Rolls.invite _ (U v.1) _ ((p k) v) _ (odd_to he) ((S.step k).odd)]
   rw [rollsT _ ℓ k X U w hw v]; refine sum_congr rfl (fun j _=>?_); have hx: j.val.1=v.1:= j.property.1; rw [hx]
omit hw
lemma receive (F:I → Cover → Y)(v:H i): earnL S ℓ i i X U F v=F v.1 (showX S ℓ i X v):=by rw [earnL,centreN,one_smul, roles,chain_zero] -- binder Y
lemma firstE (F:I → Cover → Y)(v:H ℓ): earnL S ℓ i ℓ X U F v=Averaging.filter (U v.1) (ratioTo S i ℓ) (F v.1) (ratioTo S i ℓ • X v.1):=by unfold earnL; rw [CardsT.through]
end YM.Intag.CardsT
#print axioms YM.Intag.CardsT.choral
#print axioms YM.Intag.CardsT.towers
#print axioms YM.Intag.CardsT.receive
#print axioms YM.Intag.CardsT.firstE
