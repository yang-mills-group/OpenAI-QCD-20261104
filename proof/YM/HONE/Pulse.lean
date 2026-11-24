import YM.HONE.Stand
import YM.Lyre.Ascent
import YM.Lyre.Pillar
import YM.Lyre.Bloom
set_option autoImplicit false
noncomputable section
namespace YM.Intag.CardsT
open Function Filter Finset MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Lat QCD.Tide Push.GridApprox
open QCD.Grass QCD.Plum
open MassiveQCD MassiveQCD.Cupola MassiveQCD.Sample Sample.LoomT Sample.Quills
open QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby
open scoped BigOperators Classical
variable {S:Scheme}{R:Side}{ℓ i k n:ℕ}{I:Type} [Fintype I] (A:Massive.Run S n R 6)
variable (X:I→ Cover) (U:I→ Averaging)(q:I→Bool)
local notation "H" k:arg=> Hole I S ℓ k
local notation "p" k:arg=> showX S ℓ k X
local notation "L" k:arg=> CardsT.link S ℓ k X
variable (w:∀ k:ℕ,Hole I S ℓ (k+1)→Hole I S ℓ k→ℝ)
variable (hw: ∀ k,ℓ ≤ k → SignedWeights S ℓ k X U (w k))
local notation "Sn"=> S.side R
set_option quotPrecheck false
variable (F:I → Cover → Insertion (S.side R n) 6) -- true ordered list tests
-- stage sensor.L.V ephemeral transport. choose left mass-density placement convention.

local notation "Pr"=>A.regulator.density
variable (Ψ:I → Cover → Insertion (S.side R k) 6)
noncomputable def passageT (v:Tones (S.side R (i+1)) (Hole I S ℓ (i+1))): Tones (S.side R i) (H i):= fun t s=> ∑ u: Queue (CardsT.link S ℓ i X) s, beans (CardsT.link S ℓ i X) (w i) s u • A.block i (v _ (attends (CardsT.link S ℓ i X) s u))
-- k projection.P w∀
noncomputable def fruitT (j:ℕ): Tones (S.side R j) (H j):= if h:j ≤ k then Nat.decreasingInduction (motive:=fun i _=> Tones (S.side R i) (Hole I S ℓ i)) (fun i _ y=> passageT A X w y) (egest A X U q F k Ψ) h else 0
local notation "YC"=> fruitT A X U q w F Ψ
local notation "Lr"=> egest A X U q F k Ψ (ℓ:=ℓ)
lemma crownV : YC k=Lr:=by unfold fruitT; rw [dif_pos le_rfl]; exact Nat.decreasingInduction_self ..
lemma sendY (hi:i < k): YC i=passageT A X w (YC (i+1)):=by unfold fruitT; rw [dif_pos hi.le,dif_pos (show i+1≤ k from hi)]; exact Nat.decreasingInduction_succ_left ..
variable (hA:A.Actual)(h:k≤n)
include h
lemma sprity (hi:i≤ k)(t:ℕ)(s:Fin t→ Hole I S ℓ i): Continuous (YC i t s):=by
     induction hi using Nat.decreasingInduction with
     | self=> rw [crownV]; exact egestF ..
     | of_succ i hi ih=>
        rw[sendY A X U q w F Ψ hi]; let a:= CardsT.link S ℓ i X
        let f(j:Quills.Queue a s):Massive.Density (S.side R i) 6:= beans (CardsT.link S ℓ i X) (w i) s j • A.block i (YC (i+1) _ (attends a s j)); have hf:q=q:=rfl
        unfold passageT; change Continuous (∑ j:Queue a s,f j); rw[show (∑ j:Queue a s,f j)=(fun x=>∑ j,f j x) from funext fun x=>Finset.sum_apply ..]; apply continuous_finsetSum; intro j _; exact (show Continuous (A.block i _) from Massive.Lyre.won _ _ ((S.admissible _)) (stays (ih (attends a s j)))).const_smul _ -- sig. `continuous.finset_sum` lemma Pi.side value, may missing
-- resulting exact checked word. at prices of all royalties.K.Sound.V
noncomputable def doubleT (v:H i) : Stud (S.side R n) 6:= earnL S ℓ k i X U (fun j b=>climbH A k n (Ψ j b)) v + ⇑(- earnL S ℓ n i X U F v)
local notation "VQ" mm:arg=> doubleT A X U F Ψ (i:=mm)
include hw
lemma elabor (hi:i < k)(he:ℓ ≤ i) (v:H i): (VQ i) v = ∑ j:LoomT.To (L i) v,(↑(w i j.val v):ℂ) • ((VQ(i+1)) j.val):=by
     let a:= CardsT.link S ℓ i X
     let Fx:= earnL S ℓ k (i+1) X U (fun t b=> (climbH A k n (Ψ t b)))
     let f':= earnL S ℓ n (i+1) X U F; let pξ(j: To a v):=w i j.val v
     have heq : (VQ i) v=(∑ j:To a v,pξ j • Fx j.val) + ⇑(-(∑ j:To a v,pξ j • f' j.val)):=by unfold doubleT; rw [towers S ℓ k i X U (w i) (hw i he) _ hi v,towers S ℓ n i X U (w i) (hw i he) _ (hi.trans_le h) v]
     rw[heq]; funext u; simp only [Pi.add_apply,ContinuousMap.neg_apply,ContinuousMap.sum_apply,Finset.sum_apply]; rw [← sum_neg_distrib, ← sum_add_distrib]; apply sum_congr rfl; intro j _
     unfold doubleT; rw [smul_add,Pi.add_apply]; congr 1; change -(pξ j • f' j.val u)=(pξ j) • (- f' j.val u); rw [smul_neg] -- neg smul
lemma songR (hi:i≤ k)(ht:ℓ ≤ i)(v:H i): Stays ((VQ i) v):=by
     induction hi using Nat.decreasingInduction with
     | self=> unfold doubleT; rw [receive S ℓ k X U _ v]; let t:= Ψ v.1 ((p k) v); let y:= -earnL S ℓ n k X U F v; exact (((Massive.Lyre.climbs A t (stays t.continuous) h).both (stays y.continuous)).flows (continuous_add (M:=Fields (S.side R n) 6)))
     | of_succ i hi ih=> rw[elabor _ _ _ w hw F Ψ h hi ht v]; apply Lyre.sumsA; intro i _; exact stockC _ _ (ih (by omega) _)
end YM.Intag.CardsT
#print axioms YM.Intag.CardsT.sprity
#print axioms YM.Intag.CardsT.songR
