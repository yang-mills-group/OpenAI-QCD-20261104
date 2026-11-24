import YM.HONE.Send
import YM.Lyre.Ascent
import YM.Differ.Rerun
/-!
  # REAL Tones made literal at arbitrary intermediate EP launch.
-/
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
noncomputable def rolledT (m:ℕ) (s:Fin m→ Hole I S ℓ i):Insertion (S.side R n) 6:=(List.ofFn (fun j=> earnL S ℓ n i X U F (s j))).prod
local notation "Pr"=>A.regulator.density
-- notation order.Repetition.
local notation "Qv"=>rolledT
noncomputable def older (k:ℕ): Tones (Sn k) (H k):=fun m s=>⇑(S.toStop R A.β A.w n k (Pr * rolledT X U F _ s))
local notation "Z"=> older A X U F
local notation "TF"=>nurture -- intermediate false weight tower.No dependency.
include hw
lemma enjamb (m:ℕ)(s:Fin m→ H k)(hi:k < n)(hx:ℓ ≤ k): Z k m s=∑ u: Sample.Quills.Queue (L k) s, beans (L k) (w k) s u • A.block k (Z (k+1) _ (attends (L k) s u)) :=by
     let G (m:ℕ) (u:H (k+1)):= earnL S ℓ n (k+1) X U F u; let T:=(L k); have ht (i:H k):earnL S ℓ n k X U F i=∑ j: To T i,(↑(w k j.val i):ℂ) • G 0 j.val:= (towers S ℓ n k X U (w k) (hw k hx) F hi i).trans (sum_congr rfl fun _ _=>rfl)
     let Cq (u:Queue T s):=rolledT X U F m (attends T s u); have hV: rolledT X U F m s=∑ u:Queue T s,beans T (w k) s u • Cq u:=by
          unfold rolledT; simp_rw [ht]; exact choral (r:=T) (w k) (G 0) m s
     unfold older; rw [hV,mul_sum]; simp_rw [mul_smul_comm,map_sum,map_smul]; funext x; rw [ContinuousMap.sum_apply, Finset.sum_apply]; apply sum_congr rfl; intro j _; exact congr_arg ((beans _ _ _ j) • ·) (congr_fun (Massive.Patria.Depth.route A (Pr * Cq j) hi) x)
omit hw
lemma voleur {Y:Type} [AddCommGroup Y][Module ℝ Y](x:Cover → Y)(g:ℝ)(o:Cover)(i:ℕ)(U:Averaging): Averaging.filter U i (fun k=>g • x k) o=g • Averaging.filter U i x o:=by
     let f:Y→ₗ[ℝ]Y:=g • LinearMap.id
     rw [Massive.Patria.Rolls.roles] -- no open.S adapt
     rw [Massive.Patria.Rolls.roles]; exact Eq.symm (Massive.Patria.Rolls.rollLinear (l:=Massive.Patria.Rolls.menu U) (M:=i) (k:=1) x o f)
lemma bornR (v:H k) : Z k 1 (fun _=>v)=⇑(trolley A (F v.1) (U v.1) k ((p k) v)):=by unfold older trolley AllAt rolledT; rw[List.ofFn_succ, List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one]
variable (hA:A.Actual)
include hA
lemma unborn (v:Fin 0→H k)(hk:k≤ n): Z k 0 v = A.density k:=by unfold older rolledT; rw [List.ofFn_zero,List.prod_nil,mul_one]; exact (pier A hA hk).symm
-- flip old all occurrences through check.
local notation "G"=>Talent.scale (fun _i:H k=>(-1:ℝ)) (Z k)
local notation "E" i:arg=> earnL S ℓ n i X U
end YM.Intag.CardsT
#print axioms YM.Intag.CardsT.enjamb
#print axioms YM.Intag.CardsT.voleur
#print axioms YM.Intag.CardsT.bornR
#print axioms YM.Intag.CardsT.unborn
