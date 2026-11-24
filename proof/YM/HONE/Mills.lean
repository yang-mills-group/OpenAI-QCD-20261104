import YM.HONE.Tall
import YM.HONE.Sundae
import YM.Lyre.Advance
import YM.HONE.Bird
import YM.HONE.Bird
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
open Cylinder
variable (C:∀ l:ℕ,Cells.Cut (S.side R l))(hC:(C ℓ).kind=.link)(hwC:∀ j,ℓ ≤ j→ j < n→ C (j+1)= gateH (C j) (QCD.Flume.sliceL (S.step j) (S.sides_next R j)))
local notation "Tn"=> C n
variable (U0:Averaging)(a b:Cover)(hv: CompleteP (C ℓ) b)
local notation "K"=> C ℓ
local notation "Φ"=>Signed.mirror (C ℓ).pos
local notation "ρ" k:arg=> ratioTo S k ℓ
variable (X0 Y0: Cover → Insertion (S.side R n) 6)(hx:∀ p:Cover, Cylinder.Action.adj (C ℓ).pos ⇑(X0 p)=Y0 ((Signed.mirror (C ℓ).pos).act p))(hΩ:∀ a b:Cover,Massive.Patria.march b ⇑(Y0 a)=Y0 (a+b))
variable (X₁ Y₁: Cover → Insertion (S.side R k) 6)(hx1:∀ p:Cover, Cylinder.Action.adj (C ℓ).pos ⇑(X₁ p)=Y₁ ((Signed.mirror (C ℓ).pos).act p))(hΩ1:∀ a b:Cover,Massive.Patria.march b ⇑(Y₁ a)=Y₁ (a+b))
local notation "Zp"=> b+(C ℓ).flip.act a
local notation "T" =>tallH (C n)
local notation "QL" F:arg=>fun x:Cover=>climbH A k n (F x)
local notation "RT" k:arg=>checkedT U0 (ρ k)
include hv hwC hx1 hΩ1 h
lemma reaps (hs:ℓ≤ k): T ((RT k) (QL X₁) a)= (RT k) (QL Y₁) Zp:=by
    let G:=(C ℓ).flip; let W:= (ρ k) • b; let x:= (ρ k) • a
    have hp:= rarities C hwC b hv hs h; have ht(p:Cover): T ((QL X₁) p)=(QL Y₁) (W+G.act p):=by
          rw[Lyre.full_tall A C _ (stays (X₁ p).continuous) hp.link (fun i hi=>hwC _ (hs.trans hi)) h, Lyre.paintC (C k) W hp, doors C hwC hs h,hx1 p,hΩ1,add_comm W]
    change fenceT (C n) _=_; refine (rotateF G U0 (fenceT (C n)) _ (QL X₁) (QL Y₁) x W (odd_to hs) ht).trans ?_; change Averaging.filter _ _ _ _=Averaging.filter _ _ _ _; rw [show Averaging.permute G U0=U0 from permit_mirror ..]; apply congr_arg; rw [smul_add]; unfold W G x; rw [sculptA]
noncomputable abbrev checkE (ℓ:ℕ)(U:Averaging)(X:Cover→ Insertion (S.side R n) 6)(Y:Cover→ Insertion (S.side R k) 6)(a:Cover): Stud (S.side R n) 6:= checkedT U (ratioTo S k ℓ) (fun x:Cover=> climbH A k n (Y x)) a - ⇑(checkedT U (ratioTo S n ℓ) X a)
include hx hΩ
lemma rentM (hs:ℓ≤ k): T (checkE A ℓ U0 X0 X₁ a)= checkE A ℓ U0 Y0 Y₁ Zp :=by unfold checkE; change fenceT _ (_ - _) = _; rw [map_sub]; exact congr_arg₂ Sub.sub (reaps A h C hwC U0 a b hv X₁ Y₁ hx1 hΩ1 hs) (criesT C hwC U0 a b hv X0 Y0 hx hΩ (hs.trans h))
omit hv hwC hx hΩ hx1 hΩ1 h
lemma docket (v:H ℓ): doubleT A X U F Ψ v= checkE A ℓ (U v.1) (F v.1) (Ψ v.1) (X v.1):=by unfold doubleT checkE checkedT; rw [earnL,earnL,CardsT.through]; rw [sub_eq_add_neg]; rfl
-- canonical noncommute.S perk
end YM.Intag.CardsT
#print axioms YM.Intag.CardsT.rentM
#print axioms YM.Intag.CardsT.docket
