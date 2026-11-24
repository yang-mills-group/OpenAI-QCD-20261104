import YM.HONE.Pulse
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
variable (hA:A.Actual)(h:k≤n)
local notation "YC"=> fruitT A X U q w F Ψ
local notation "Qr" j:arg=> CardsT.stencil (I:=I) S ℓ j
local notation "VQ" jx:arg=> doubleT A X U F Ψ (i:=jx)
variable (hs:ℓ ≤ i)(hi:i≤ k)
-- allow customers ℓ stencil ANY testing use Projection.Score.C.
variable (hΨ:∀ (u:I)(b:Cover),∀ V:Grid (S.side R k),Hom (q u) (Ψ u b V))
variable (f:Hole I S ℓ k→∀ i,Set (Site (S.side R i))) (hx:∀ a:Hole I S ℓ k, Plum.Fence (f a k) (chordR X (ℓ:=ℓ) Ψ a))
variable (hv:∀ a: Hole I S ℓ k, Lease k n (f a))
variable (hd:∀ i:ℕ,k≤ i→ i < n→∀ (u v:Hole I S ℓ k),u.1 ≠ v.1→ Disjoint (f u i) (f v i))
variable (hΘ:∀ a:Hole I S ℓ k,∀ V:Grid (S.side R n),Hom (q a.1) ((earnL S ℓ n k X U F a) V))
include hw hA h hs hi hΨ hx hv hd hΘ
lemma rays (t:ℕ)(s:Fin t→ Hole I S ℓ i)(hp: Injective s)(hz:Quills.crest s∈ CardsT.stencil (I:=I) S ℓ i): sig A i (YC i t s)=valueH A.regulator ((List.ofFn (fun j=> doubleT A X U F Ψ (s j))).prod):=by
    induction hi using Nat.decreasingInduction with
    | self=> rw [crownV]; simp_rw[doubleT, receive S ℓ k X U]; exact astuteR A X U q F hA Ψ hΨ f hx h t s hΘ hp (fun v _=>hv v) (fun i h h' a ha b hb hZ=> hd i h h' a b (fun he=> hZ ((hz:Set.InjOn _ _) ha hb he)))
    | of_succ i hi ih=>
       let T:=CardsT.link S ℓ i X; have P:= CardsT.pledges S ℓ i X q; let b:=i+1; let Qw j:= Quills.beans T (w i) s j; let Tg(j: Queue T s):= attends T s j
       let G(j: Queue T s) := YC b t (Tg j); have hh:ℓ≤ b:= (Nat.le_succ_of_le hs); let Pq u := doubleT A X U F Ψ (i:=i+1) (ℓ:=ℓ) u
       have he(j): sig A b (G j)=valueH A.regulator (List.ofFn fun i=> Pq (Tg j i)).prod:= ih hh (Tg j) (attends_well _ _ _ _ _ P s j hz hp) (P.was _ _ (usher _ _ _ _ _ P s j hz hp))
       let Wq (j:Queue T s):= (List.ofFn fun i=> Pq (Tg j i)).prod; let Yq (j:Queue T s):= A.block i (G j)
       have hf: (List.ofFn fun j=>doubleT A X U F Ψ (s j)).prod= ∑ x:Queue T s,Qw x • Wq x:=by simp_rw [elabor A X U w hw F Ψ h hi hs]; exact choral (r:=T) (w i) Pq t s
       have hu(j):Stays (Wq j):= flockZ Pq (Tg j) (fun i _=>songR A X U w hw F Ψ h hi hh _)
       rw [sendY _ _ _ _ _ _ _ hi,hf,sumsV _ univ _ (fun i _=>stockC _ _ (hu i))]; unfold passageT
       have hG (j):= (stays (sprity A X U q w F Ψ h hi _ (Tg j))); have ht(j):Stays (Yq j):= stays (Massive.Lyre.won _ _ (S.admissible _) (hG j)); unfold sig; rw [stampM univ _ (fun i _=> stockC _ _ (ht i)), sum_div]; apply sum_congr rfl; intro j _; rw [stampB, mul_div_assoc, Lyre.spend]; change Qw j*sig A i (A.block i (G j))=_; rw [escalated A hA _ (hi.trans_le h) (hG j), he]; rfl
end YM.Intag.CardsT
#print axioms YM.Intag.CardsT.rays
