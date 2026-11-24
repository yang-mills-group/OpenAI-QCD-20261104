import YM.HONE.Pulse
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
open Massive.Patria.Rolls QCD.Tide Massive.Patria
local notation "κ"=> Tally
local notation "g"=> Pr
noncomputable abbrev densityW (i:ℕ): Insertion (S.side R i) 6:=AllAt A i (A.regulator.density)
noncomputable abbrev tentT (A:Massive.Run S n R 6) (J:Massive.Averaging)(Ψ:Cover → Insertion (S.side R k) 6) (i:ℕ)(b:Cover): Insertion (S.side R i) 6:= report A (fun j=>Ψ j*densityW A k) J i b
local notation "VZ" k:arg=> tentT A (U (Prod.fst k)) (Ψ k.1)
local notation "Zt" u:arg=>trolley A (F u.1) (U u.1)
variable (hΨ:∀ (u:I)(a b:Cover),Massive.Patria.march b (Ψ u a)=Ψ u (a+b))
open Exposure TorusPCAC.Geometry
include hΨ h hA
lemma tentsG (u:I): TideT A (U u) k (tentT A (U u) (Ψ u)):=by
      apply stampF; intro a b; let T:= densityW A k; have he:march b T=T:= Massive.Patria.Depth.first A _ h b; funext x; exact (map_mul (crank 1 1 (wrap _ b) (heat b)) _ _).trans (congr_arg₂ HMul.hMul (congr_fun (hΨ u a b) x) (congr_fun he x)) -- map march.L.S.Root
variable (hF:∀ (u:I)(a b:Cover),Massive.Patria.march b (F u a)=F u (a+b))
include hF
lemma tepidK (u:I) : TideT A (U u) k (tentT A (U u) (Ψ u)- trolley A (F u) (U u)):= tideDiff A (U u) _ _ (tentsG A U Ψ hA h hΨ u) (wingG A hA _ _ h (hF u))
include hw hs hi
local notation "FΠ" i:arg v:arg=> ((tentT A (U (Prod.fst v)) (Ψ (Prod.fst v)))-trolley A (F (Prod.fst v)) (U (Prod.fst v))) i ((p i) v)
open Sample.LoomT
lemma gawks (v:H i): YC i 1 (fun _=>v)=⇑(FΠ i v):=by
     induction hi using Nat.decreasingInduction with
     | self=>
         rw [crownV]; unfold egest; rw [faceT]; change Talent.scale _ _ 1 _ + chordR X Ψ v* Talent.scale _ _ 0 _ = ⇑((VZ v) k ((p k) v) - (Zt v) k ((p k) v)); rw[Talent.scale, show Talent.realize _ _=_ from (show Talent.realize (fun _i:H k=> (-1:ℝ)) (fun _:Fin 1=>v)=-1 by simp [Talent.realize]), neg_one_smul,Talent.scale,Talent.realize,Fintype.prod_empty,one_smul] -- Fintype.prod_empty Fintype Empty change
         rw [bornR, unborn A X U F hA _ h]; unfold tentT; rw [arrivesHere]; rw [pier A hA h]; let x1:= ((p k) v); let y: Density (Sn k) 6:=Ψ v.1 x1; let f: Density (Sn k) 6:= densityW A k; let t:Density (Sn k) 6:= (Zt v) k x1; change -t + y * f = y*f - t; abel -- cause orientation.Q
     | of_succ i hi ih=>
         rw [sendY _ _ _ _ _ _ _ hi]; let a:= CardsT.link S ℓ i X
         let D:= (VZ v) - Zt v; have hmC:= (tepidK A U F Ψ hA h hΨ hF v.1).steps i hi (To a v) (fun j=>w i j.val v) (fun j=> offset S _ _ X v j.val) ((hw i hs).toll v) ((p i) v)
         change _= ⇑(D i ((p i) v)); rw[show ⇑(D i ((p i) v)) = _ from hmC]
         unfold passageT
         -- reduce Queue over 1.Aggreg.Pe.Recipe.
         let f:Fin 1→H i:=fun _=>v; let X1:=Equiv.piUnique (fun i=> To a (f i)); refine Fintype.sum_equiv X1 _ _ ?_; intro t; have hx:attends a f t=fun _=>(X1 t).val:=funext fun z=>congr_arg (fun j=> (t j).val) (Subsingleton.elim ..); let z:=X1 t; change beans a (w i) f t • A.block i (YC (i+1) 1 (attends a f t))=_; unfold beans; rw[hx,Fin.prod_univ_one]
         rw [ih (Nat.le_succ_of_le hs) z.val]; change ((w i z.val v:ℝ):ℂ) • A.block i (FΠ (i+1) (z.val)) = _; rw [← mail S _ _ X v z.val]; change _ = _; rw [show z.val.1=v.1 from z.property.1] -- register.X
end YM.Intag.CardsT
#print axioms YM.Intag.CardsT.gawks
